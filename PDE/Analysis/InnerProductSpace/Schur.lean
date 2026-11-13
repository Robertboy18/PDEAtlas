/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Orthonormal triangularization

Every endomorphism of a finite-dimensional complex inner product space has an upper
triangular matrix in an orthonormal basis. More generally, the construction works over
an algebraically closed `RCLike` field.

The induction chooses an eigenvector of the adjoint. Its orthogonal complement is
invariant under the original operator. An orthonormal triangularizing basis on that
complement, followed by the normalized eigenvector, gives the desired basis.

The operator need not be diagonalizable. Since the coordinate map is a linear isometry,
operator-norm estimates in triangular coordinates carry no change-of-basis constant.

For an operator with real spectrum, the resulting diagonal is real. Every matrix
entry is bounded by the original operator norm, independently of eigenvalue
multiplicities or the chosen orthonormal basis.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

noncomputable section

/-- The spectrum of an upper triangular matrix consists exactly of its diagonal
entries. Repeated entries are allowed; the characteristic polynomial is a product
of the corresponding linear factors. -/
theorem Matrix.IsUpperTriangular.spectrum_eq_range_diag
    {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [LinearOrder ι]
    {A : Matrix ι ι 𝕜} (hA : A.IsUpperTriangular) :
    spectrum 𝕜 A = Set.range (fun i ↦ A i i) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_of_isUpperTriangular A hA, Polynomial.isRoot_prod]
  simp only [Finset.mem_univ, true_and, Polynomial.IsRoot, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, Set.mem_range]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, hi.symm⟩, fun ⟨i, hi⟩ ↦ ⟨i, hi.symm⟩⟩

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Induction on the dimension constructs an orthonormal basis whose matrix entries
below the diagonal vanish. The adjoint supplies an invariant orthogonal complement
at each successor step; dimension zero uses the empty orthonormal basis. -/
private theorem exists_orthonormalBasis_inner_eq_zero_of_finrank
    {n : ℕ} (hn : finrank 𝕜 E = n) (T : E →ₗ[𝕜] E) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E,
      ∀ i j, j < i → inner 𝕜 (b i) (T (b j)) = 0 := by
  classical
  induction n generalizing E with
  | zero =>
      refine ⟨(stdOrthonormalBasis 𝕜 E).reindex (finCongr hn), ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      have : Nontrivial E :=
        finrank_pos_iff.mp (by rw [hn]; exact Nat.zero_lt_succ n)
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T.adjoint
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      let u : E := (‖v‖⁻¹ : 𝕜) • v
      have hu : ‖u‖ = 1 := norm_smul_inv_norm hv.2
      have hu_ne : u ≠ 0 := by
        intro h
        simp only [h, norm_zero, zero_ne_one] at hu
      have hue : T.adjoint u = μ • u := by
        dsimp only [u]
        rw [map_smul, hv.apply_eq_smul, smul_comm]
      let K : Submodule 𝕜 E := (𝕜 ∙ u)ᗮ
      have hK : ∀ x, x ∈ K → T x ∈ K := by
        intro x hx
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [← T.adjoint_inner_left x u, hue, inner_smul_left,
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp hx, mul_zero]
      have : Fact (finrank 𝕜 E = n + 1) := ⟨hn⟩
      have hdimK : finrank 𝕜 K = n := Submodule.finrank_orthogonal_span_singleton hu_ne
      obtain ⟨b, hb⟩ := ih (E := K) hdimK (T.restrict hK)
      have horth (i : Fin n) : inner 𝕜 u (b i : E) = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property
      let w : Fin (n + 1) → E := Fin.snoc (fun i ↦ (b i : E)) u
      have hw : Orthonormal 𝕜 w := by
        rw [orthonormal_iff_ite]
        intro i j
        refine Fin.lastCases ?_ (fun i ↦ ?_) i
        · refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · simp only [w, Fin.snoc_last, inner_self_eq_norm_sq_to_K, hu,
              RCLike.ofReal_one, one_pow, ite_true]
          · simpa only [w, Fin.snoc_last, Fin.snoc_castSucc,
              ite_eq_right j.castSucc_lt_last.ne'] using horth j
        · refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · simpa only [w, Fin.snoc_last, Fin.snoc_castSucc,
              ite_eq_right i.castSucc_lt_last.ne] using
              (inner_eq_zero_symm.mpr (horth i))
          · simpa only [w, Fin.snoc_castSucc, Fin.castSucc_inj, Submodule.coe_inner] using
              b.inner_eq_ite i j
      have hspan : Submodule.span 𝕜 (Set.range w) = ⊤ :=
        hw.linearIndependent.span_eq_top_of_card_eq_finrank'
          (by simpa only [Fintype.card_fin] using hn.symm)
      let c : OrthonormalBasis (Fin (n + 1)) 𝕜 E :=
        OrthonormalBasis.mk hw hspan.ge
      have hc_cast (i : Fin n) : c i.castSucc = (b i : E) := by
        simp only [c, OrthonormalBasis.coe_mk, w, Fin.snoc_castSucc]
      have hc_last : c (Fin.last n) = u := by
        simp only [c, OrthonormalBasis.coe_mk, w, Fin.snoc_last]
      refine ⟨c, ?_⟩
      intro i j
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · exact fun h ↦ (lt_irrefl _ h).elim
        · intro _
          rw [hc_last, hc_cast]
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
            (hK (b j) (b j).property)
      · refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · exact fun h ↦ (not_lt_of_ge (Fin.le_last i.castSucc) h).elim
        · intro hij
          rw [hc_cast, hc_cast]
          exact hb i j hij

/-- Schur triangularization in an orthonormal basis. The theorem allows repeated
eigenvalues and nontrivial Jordan blocks, and also covers the zero-dimensional space. -/
theorem exists_orthonormalBasis_isUpperTriangular (T : E →ₗ[𝕜] E) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_inner_eq_zero_of_finrank rfl T
  refine ⟨b, ?_⟩
  intro i j hij
  simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using hb i j hij

/-- An operator with real spectrum admits an orthonormal upper triangular form
with real diagonal and all entries bounded by its operator norm. This bound has
no eigenbasis condition number and applies without a diagonalizability hypothesis. -/
theorem exists_orthonormalBasis_isUpperTriangular_real
    (T : E →ₗ[𝕜] E) (hT : ∀ z ∈ spectrum 𝕜 T, RCLike.im z = 0) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular ∧
      (∀ i, RCLike.im (LinearMap.toMatrix b.toBasis b.toBasis T i i) = 0) ∧
      ∀ i j, ‖LinearMap.toMatrix b.toBasis b.toBasis T i j‖ ≤
        ‖T.toContinuousLinearMap‖ := by
  obtain ⟨b, hb⟩ := T.exists_orthonormalBasis_isUpperTriangular
  refine ⟨b, hb, ?_, ?_⟩
  · intro i
    apply hT
    rw [← T.spectrum_toMatrix b.toBasis, hb.spectrum_eq_range_diag]
    exact Set.mem_range_self i
  · intro i j
    rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]
    change ‖inner 𝕜 (b i) (T (b j))‖ ≤ ‖T.toContinuousLinearMap‖
    calc
      ‖inner 𝕜 (b i) (T (b j))‖ ≤ ‖b i‖ * ‖T (b j)‖ := norm_inner_le_norm _ _
      _ = ‖T (b j)‖ := by rw [b.norm_eq_one i, one_mul]
      _ ≤ ‖T.toContinuousLinearMap‖ :=
        T.toContinuousLinearMap.unit_le_opNorm (b j) (b.norm_eq_one j).le

end LinearMap
