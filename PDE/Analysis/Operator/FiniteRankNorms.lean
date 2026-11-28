/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Operator.FiniteRankCapture.TwoSided
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Norms of finite-rank operators from Gram matrices

A finite-rank operator `T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ` on a real inner product space is given by two
finite families. This module bounds `‖T f‖`, `∑ⱼ ⟪aⱼ, f⟫²` and `⟪f, T f⟫` by matrices of inner
products, which a computation can enclose: the Gram matrices `C` of `a` and `D` of `b`, and the
Gram matrix `W` of a family `w`. These are the bounds of Remark 8 of Hou, Wang and Yang. Remark 8
states equalities; only the upper bounds are proved here, which is the direction the estimates of
that paper use. The equalities are in `PDE.Analysis.Operator.FiniteRankNormIdentities`.

## Main results

All results hold on every real inner product space and for all finite families;
`norm_symmetricPart_eq_iSup_rayleighQuotient` asks the space to be complete.

* `finiteRank`: the operator `f ↦ ∑ⱼ ⟪aⱼ, f⟫ bⱼ` between two spaces.
* `pairing_quadForm_le_of_gram`, `abs_pairing_quadForm_le_of_gram`: with `cₖ = ⟪wₖ, f⟫`, the
  matrix inequality `(W α)ᵀ B (W α) ≤ t αᵀ W α` for every `α` gives `cᵀ B c ≤ t ‖f‖²`, and the
  same with absolute values.
* `abs_pairing_quadForm_le_l2_opNorm`: `|cᵀ B c| ≤ ‖W^{1/2} B W^{1/2}‖ ‖f‖²`, with the spectral
  norm.
* `norm_finiteRank_apply_sq_le_of_gram`, `norm_finiteRank_apply_sq_le_l2_opNorm`,
  `norm_finiteRank_apply_sq_le_trace`, `norm_finiteRank_le_sqrt_trace`: `‖T f‖² ≤ t ‖f‖²` from the
  matrix inequality `C D C ≤ t C`, for `t = ‖C^{1/2} D C^{1/2}‖` and for `t = tr(C D)`.
* `sum_inner_sq_le_of_gram`, `sum_inner_sq_le_l2_opNorm`: `∑ⱼ ⟪aⱼ, f⟫² ≤ t ‖f‖²` from `C² ≤ t C`,
  and for `t = ‖C‖`.
* `abs_inner_finiteRank_le_of_gram`, `abs_inner_finiteRank_le_l2_opNorm`: `|⟪f, T f⟫| ≤ θ ‖f‖²`
  from a matrix inequality for the two families side by side, and for `θ = ‖W^{1/2} K W^{1/2}‖`
  with `K = ½ [[0, 1], [1, 0]]` (`swapHalf`).
* `norm_symmetricPart_eq_iSup_rayleighQuotient`: the supremum of `|⟪T f, f⟫| / ‖f‖²` is
  `‖(T + T*) / 2‖`, for every bounded operator on a real Hilbert space.

## How it works

Everything `T` does to `f` goes through the finitely many pairings `cₖ = ⟪wₖ, f⟫`. Replace `f` by
its orthogonal projection `p = ∑ₖ αₖ wₖ` onto the span of `w`: the pairings stay the same,
`c = W α`, and `‖p‖² = αᵀ W α ≤ ‖f‖²`. So `cᵀ B c ≤ t ‖f‖²` as soon as `(W α)ᵀ B (W α) ≤ t αᵀ W α`
for every `α`, which is the matrix inequality `W B W ≤ t W` (`pairing_quadForm_le_of_gram`). This
is `le_mul_form_of_forall_mem_span` for the inner product, with Mathlib's orthogonal projection
and the bound on the span written as a matrix inequality.

Three choices of `w` and `B` give the bounds of Remark 8. With `w = a` and `B = D`,
`cᵀ D c = ‖T f‖²`. With `w = a` and `B = 1`, `cᵀ c = ∑ⱼ ⟪aⱼ, f⟫²`. With the two families side by
side and `B = K`, `cᵀ K c = ⟪f, T f⟫`. Writing `S = W^{1/2}` and `β = S α`, the matrix inequality
reads `βᵀ (S B S) β ≤ t |β|²`, so the spectral norm of `S B S` is an admissible `t`
(`abs_gram_quadForm_le_l2_opNorm`).

The trace bound needs no projection. With `R = D^{1/2}`, `‖T f‖² = |R c|² = ∑ₖ ⟪gₖ, f⟫²` for
`gₖ = ∑ⱼ Rₖⱼ aⱼ`, and `∑ₖ ‖gₖ‖² = tr(R C R) = tr(C D)`. The identity for the symmetric part is
Mathlib's `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` applied to `(T + T*) / 2`.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Remark 8.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped Matrix RealInnerProductSpace
open InnerProductSpace (rankOne)

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

section Pairings

variable {κ : Type*} [Fintype κ]

/-- The pairings of a combination of a family are its Gram matrix applied to the coefficients. -/
theorem inner_sum_smul_eq_gram_mulVec (w : κ → X) (α : κ → ℝ) (k : κ) :
    ⟪w k, ∑ l, α l • w l⟫ = (Matrix.gram ℝ w *ᵥ α) k := by
  simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, Matrix.gram_apply]
  exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _

/-- The squared norm of a combination of a family is the quadratic form of its Gram matrix. This is
Mathlib's `Matrix.star_dotProduct_gram_mulVec`, where the star of `ℝ` is trivial. -/
theorem norm_sq_sum_smul_eq_gram (w : κ → X) (α : κ → ℝ) :
    ‖∑ l, α l • w l‖ ^ 2 = α ⬝ᵥ Matrix.gram ℝ w *ᵥ α := by
  rw [← real_inner_self_eq_norm_sq, ← Matrix.star_dotProduct_gram_mulVec, star_trivial]

/-- **Quadratic functionals of finitely many pairings.** Let `W` be the Gram matrix of a finite
family `w` and `cₖ = ⟪wₖ, f⟫`. If `(W α)ᵀ B (W α) ≤ t αᵀ W α` for every `α`, then
`cᵀ B c ≤ t ‖f‖²` for every `f`. The orthogonal projection of `f` onto the span of `w` has the
pairings of `f` and a smaller norm, and on the span the claim is the matrix inequality. -/
theorem pairing_quadForm_le_of_gram (w : κ → X) (B : Matrix κ κ ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hcert : ∀ α : κ → ℝ, (Matrix.gram ℝ w *ᵥ α) ⬝ᵥ B *ᵥ (Matrix.gram ℝ w *ᵥ α) ≤
      t * (α ⬝ᵥ Matrix.gram ℝ w *ᵥ α)) (f : X) :
    (fun k ↦ ⟪w k, f⟫) ⬝ᵥ B *ᵥ (fun k ↦ ⟪w k, f⟫) ≤ t * ‖f‖ ^ 2 := by
  set K := Submodule.span ℝ (Set.range w)
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (Submodule.starProjection_apply_mem K f)
  have hpair : (fun k ↦ ⟪w k, f⟫) = Matrix.gram ℝ w *ᵥ α := by
    funext k
    have h := K.starProjection_inner_eq_zero f (w k) (Submodule.subset_span ⟨k, rfl⟩)
    rw [← inner_sum_smul_eq_gram_mulVec, hα, real_inner_comm f, real_inner_comm _ (w k),
      ← sub_eq_zero, ← inner_sub_left]
    exact h
  rw [hpair]
  calc
    _ ≤ t * (α ⬝ᵥ Matrix.gram ℝ w *ᵥ α) := hcert α
    _ = t * ‖K.starProjection f‖ ^ 2 := by rw [← norm_sq_sum_smul_eq_gram, hα]
    _ ≤ t * ‖f‖ ^ 2 := by
      gcongr
      exact Submodule.norm_starProjection_apply_le K f

/-- **Quadratic functionals of finitely many pairings, two-sided.** Let `W` be the Gram matrix
of a finite family `w` and `cₖ = ⟪wₖ, f⟫`. If `|(W α)ᵀ B (W α)| ≤ t αᵀ W α` for every `α`, with
`t ≥ 0`, then `|cᵀ B c| ≤ t ‖f‖²` for every `f`. This is `pairing_quadForm_le_of_gram` for `B`
and for `-B`. -/
theorem abs_pairing_quadForm_le_of_gram (w : κ → X) (B : Matrix κ κ ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hcert : ∀ α : κ → ℝ, |(Matrix.gram ℝ w *ᵥ α) ⬝ᵥ B *ᵥ (Matrix.gram ℝ w *ᵥ α)| ≤
      t * (α ⬝ᵥ Matrix.gram ℝ w *ᵥ α)) (f : X) :
    |(fun k ↦ ⟪w k, f⟫) ⬝ᵥ B *ᵥ (fun k ↦ ⟪w k, f⟫)| ≤ t * ‖f‖ ^ 2 := by
  rw [abs_le]
  constructor
  · have h := pairing_quadForm_le_of_gram w (-B) ht (fun α ↦ by
      rw [Matrix.neg_mulVec, dotProduct_neg]
      exact (neg_le_abs _).trans (hcert α)) f
    rw [Matrix.neg_mulVec, dotProduct_neg] at h
    linarith
  · exact pairing_quadForm_le_of_gram w B ht (fun α ↦ (le_abs_self _).trans (hcert α)) f

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- For a positive semidefinite `W` with square root `S`, the form `α ↦ (W α)ᵀ B (W α)` is
bounded by `‖S B S‖ αᵀ W α`: with `β = S α` it is `βᵀ (S B S) β`, and `αᵀ W α = |β|²`. -/
theorem abs_gram_quadForm_le_l2_opNorm [DecidableEq κ] {W : Matrix κ κ ℝ} (hW : W.PosSemidef)
    (B : Matrix κ κ ℝ) (α : κ → ℝ) :
    |(W *ᵥ α) ⬝ᵥ B *ᵥ (W *ᵥ α)| ≤ ‖CFC.sqrt W * B * CFC.sqrt W‖ * (α ⬝ᵥ W *ᵥ α) := by
  set S := CFC.sqrt W
  have hSS : S * S = W := CFC.sqrt_mul_sqrt_self W (Matrix.nonneg_iff_posSemidef.mpr hW)
  have hSt : Sᵀ = S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)).isHermitian
  set β := S *ᵥ α
  have hquad : α ⬝ᵥ W *ᵥ α = β ⬝ᵥ β := by
    rw [← hSS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSt]
  have hform : (W *ᵥ α) ⬝ᵥ B *ᵥ (W *ᵥ α) = β ⬝ᵥ (S * B * S) *ᵥ β := by
    rw [← hSS, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec β, ← Matrix.mulVec_transpose, hSt]
  rw [hform, hquad]
  exact abs_dotProduct_mulVec_le_l2_opNorm _ β

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **Quadratic functionals of pairings, with the spectral norm.** With `W` the Gram matrix of
`w`, `S = W^{1/2}` and `cₖ = ⟪wₖ, f⟫`, `|cᵀ B c| ≤ ‖S B S‖ ‖f‖²`. This is
`abs_pairing_quadForm_le_of_gram` with `t = ‖S B S‖`, admissible by
`abs_gram_quadForm_le_l2_opNorm`. -/
theorem abs_pairing_quadForm_le_l2_opNorm [DecidableEq κ] (w : κ → X) (B : Matrix κ κ ℝ)
    (f : X) :
    |(fun k ↦ ⟪w k, f⟫) ⬝ᵥ B *ᵥ (fun k ↦ ⟪w k, f⟫)| ≤
      ‖CFC.sqrt (Matrix.gram ℝ w) * B * CFC.sqrt (Matrix.gram ℝ w)‖ * ‖f‖ ^ 2 :=
  abs_pairing_quadForm_le_of_gram w B (norm_nonneg _)
    (abs_gram_quadForm_le_l2_opNorm (Matrix.posSemidef_gram ℝ w) B) f

end Pairings

section FiniteRank

variable {ι : Type*} [Fintype ι]

/-- The finite-rank operator `f ↦ ∑ⱼ ⟪aⱼ, f⟫ bⱼ` from `X` to `Y`, a sum of the rank-one
operators of Mathlib. -/
def finiteRank (a : ι → X) (b : ι → Y) : X →L[ℝ] Y :=
  ∑ j, rankOne ℝ (b j) (a j)

/-- The finite-rank operator applied to a vector. -/
theorem finiteRank_apply (a : ι → X) (b : ι → Y) (f : X) :
    finiteRank a b f = ∑ j, ⟪a j, f⟫ • b j := by
  simp [finiteRank]

/-- `‖T f‖² = cᵀ D c` with `cⱼ = ⟪aⱼ, f⟫` and `D` the Gram matrix of `b`. -/
theorem norm_finiteRank_apply_sq (a : ι → X) (b : ι → Y) (f : X) :
    ‖finiteRank a b f‖ ^ 2 =
      (fun j ↦ ⟪a j, f⟫) ⬝ᵥ Matrix.gram ℝ b *ᵥ (fun j ↦ ⟪a j, f⟫) := by
  rw [finiteRank_apply, norm_sq_sum_smul_eq_gram]

/-- **The norm of a finite-rank operator from a matrix inequality.** With `C` and `D` the Gram
matrices of `a` and `b`, the inequality `C D C ≤ t C` gives `‖T f‖² ≤ t ‖f‖²`. -/
theorem norm_finiteRank_apply_sq_le_of_gram (a : ι → X) (b : ι → Y) {t : ℝ} (ht : 0 ≤ t)
    (hcert : ∀ α : ι → ℝ,
      (Matrix.gram ℝ a *ᵥ α) ⬝ᵥ Matrix.gram ℝ b *ᵥ (Matrix.gram ℝ a *ᵥ α) ≤
        t * (α ⬝ᵥ Matrix.gram ℝ a *ᵥ α)) (f : X) :
    ‖finiteRank a b f‖ ^ 2 ≤ t * ‖f‖ ^ 2 := by
  rw [norm_finiteRank_apply_sq]
  exact pairing_quadForm_le_of_gram a _ ht hcert f

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The norm of a finite-rank operator, spectral form** (Hou–Wang–Yang, Remark 8):
`‖T f‖² ≤ ‖C^{1/2} D C^{1/2}‖ ‖f‖²`. -/
theorem norm_finiteRank_apply_sq_le_l2_opNorm [DecidableEq ι] (a : ι → X) (b : ι → Y) (f : X) :
    ‖finiteRank a b f‖ ^ 2 ≤
      ‖CFC.sqrt (Matrix.gram ℝ a) * Matrix.gram ℝ b * CFC.sqrt (Matrix.gram ℝ a)‖ * ‖f‖ ^ 2 := by
  rw [norm_finiteRank_apply_sq]
  exact (le_abs_self _).trans (abs_pairing_quadForm_le_l2_opNorm a _ f)

open scoped MatrixOrder in
/-- **The norm of a finite-rank operator, trace form** (Hou–Wang–Yang, Remark 8):
`‖T f‖² ≤ tr(C D) ‖f‖²`, the Hilbert–Schmidt bound. With `R = D^{1/2}`,
`‖T f‖² = ∑ₖ ⟪gₖ, f⟫²` for `gₖ = ∑ⱼ Rₖⱼ aⱼ`, and `∑ₖ ‖gₖ‖² = tr(R C R) = tr(C D)`. -/
theorem norm_finiteRank_apply_sq_le_trace (a : ι → X) (b : ι → Y) (f : X) :
    ‖finiteRank a b f‖ ^ 2 ≤ (Matrix.gram ℝ a * Matrix.gram ℝ b).trace * ‖f‖ ^ 2 := by
  classical
  set C := Matrix.gram ℝ a
  set D := Matrix.gram ℝ b
  set R := CFC.sqrt D
  have hD := Matrix.posSemidef_gram ℝ b
  have hRR : R * R = D := CFC.sqrt_mul_sqrt_self D (Matrix.nonneg_iff_posSemidef.mpr hD)
  have hRt : Rᵀ = R := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian
  set c : ι → ℝ := fun j ↦ ⟪a j, f⟫
  let g : ι → X := fun k ↦ ∑ j, R k j • a j
  have hRc (k : ι) : (R *ᵥ c) k = ⟪g k, f⟫ := by
    simp only [g, c, Matrix.mulVec, dotProduct, sum_inner, inner_smul_left]
    rfl
  have hquad : c ⬝ᵥ D *ᵥ c = ∑ k, ⟪g k, f⟫ ^ 2 := by
    rw [← hRR, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRt,
      dotProduct]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hRc, sq]
  have hg : ∑ k, ‖g k‖ ^ 2 = (C * D).trace := by
    have hk (k : ι) : ‖g k‖ ^ 2 = (R * C * Rᵀ) k k := by
      rw [norm_sq_sum_smul_eq_gram, Matrix.dotProduct_mulVec, Matrix.mul_apply, dotProduct]
      rfl
    calc
      ∑ k, ‖g k‖ ^ 2 = (R * C * Rᵀ).trace := Finset.sum_congr rfl fun k _ ↦ hk k
      _ = (C * D).trace := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, hRt, Matrix.mul_assoc, hRR]
  rw [norm_finiteRank_apply_sq, hquad, ← hg, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ ↦ by
    rw [← mul_pow]
    exact (sq_abs _).symm.trans_le
      (pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2)

open scoped MatrixOrder in
/-- The operator norm of a finite-rank operator is at most `√tr(C D)`. -/
theorem norm_finiteRank_le_sqrt_trace (a : ι → X) (b : ι → Y) :
    ‖finiteRank a b‖ ≤ √(Matrix.gram ℝ a * Matrix.gram ℝ b).trace := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun f ↦ ?_
  refine abs_le_of_sq_le_sq' ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f)) |>.2
  have h := norm_finiteRank_apply_sq_le_trace a b f
  by_cases htr : 0 ≤ (Matrix.gram ℝ a * Matrix.gram ℝ b).trace
  · rwa [mul_pow, Real.sq_sqrt htr]
  · -- A negative trace forces `f = 0`, and then both sides vanish.
    have hf : ‖f‖ ^ 2 ≤ 0 := by
      by_contra hpos
      have := mul_neg_of_neg_of_pos (not_le.mp htr) (not_le.mp hpos)
      linarith [sq_nonneg ‖finiteRank a b f‖]
    have hf0 : f = 0 := by
      simpa using le_antisymm hf (sq_nonneg _)
    simp [hf0]

/-- **The coefficient bound from a matrix inequality** (Hou–Wang–Yang, (4.32)). With `C` the
Gram matrix of `a`, the inequality `C² ≤ t C` gives `∑ⱼ ⟪aⱼ, f⟫² ≤ t ‖f‖²`. -/
theorem sum_inner_sq_le_of_gram (a : ι → X) {t : ℝ} (ht : 0 ≤ t)
    (hcert : ∀ α : ι → ℝ, (Matrix.gram ℝ a *ᵥ α) ⬝ᵥ (Matrix.gram ℝ a *ᵥ α) ≤
      t * (α ⬝ᵥ Matrix.gram ℝ a *ᵥ α)) (f : X) :
    ∑ j, ⟪a j, f⟫ ^ 2 ≤ t * ‖f‖ ^ 2 := by
  classical
  have h := pairing_quadForm_le_of_gram a 1 ht (fun α ↦ by rw [Matrix.one_mulVec]; exact hcert α) f
  rw [Matrix.one_mulVec] at h
  exact (Finset.sum_congr rfl fun j _ ↦ sq _).trans_le h

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The coefficient bound, spectral form**: `∑ⱼ ⟪aⱼ, f⟫² ≤ ‖C‖ ‖f‖²`, with `C` the Gram
matrix of `a`. -/
theorem sum_inner_sq_le_l2_opNorm [DecidableEq ι] (a : ι → X) (f : X) :
    ∑ j, ⟪a j, f⟫ ^ 2 ≤ ‖Matrix.gram ℝ a‖ * ‖f‖ ^ 2 := by
  have hC := Matrix.posSemidef_gram ℝ a
  have h := abs_pairing_quadForm_le_l2_opNorm a 1 f
  rw [Matrix.one_mulVec, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hC)] at h
  exact (Finset.sum_congr rfl fun j _ ↦ sq _).trans_le ((le_abs_self _).trans h)

end FiniteRank

section Symmetric

variable {ι : Type*} [Fintype ι]

/-- `⟪f, T f⟫ = ∑ⱼ ⟪aⱼ, f⟫ ⟪bⱼ, f⟫` for `T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ` on one space. -/
theorem inner_finiteRank_apply (a b : ι → X) (f : X) :
    ⟪f, finiteRank a b f⟫ = ∑ j, ⟪a j, f⟫ * ⟪b j, f⟫ := by
  rw [finiteRank_apply, inner_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [inner_smul_right, real_inner_comm (b j) f]

/-- The matrix `K = ½ [[0, 1], [1, 0]]` of Remark 8 of Hou, Wang and Yang, on two copies of the
index type. Its quadratic form at `(x, y)` is `∑ⱼ xⱼ yⱼ`. -/
def swapHalf (ι : Type*) [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 ((1 / 2 : ℝ) • 1) ((1 / 2 : ℝ) • 1) 0

/-- The quadratic form of `K` pairs the two halves of a vector. -/
theorem dotProduct_swapHalf_mulVec [DecidableEq ι] (c : ι ⊕ ι → ℝ) :
    c ⬝ᵥ swapHalf ι *ᵥ c = ∑ j, c (Sum.inl j) * c (Sum.inr j) := by
  conv_lhs => rw [← Sum.elim_comp_inl_inr c]
  rw [swapHalf, Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    zero_add, add_zero, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    Function.comp_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- `⟪f, T f⟫ = cᵀ K c`, with `c` the pairings of `f` with the two families `a`, `b` side by
side and `K` the matrix `swapHalf`. -/
theorem inner_finiteRank_apply_eq_swapHalf [DecidableEq ι] (a b : ι → X) (f : X) :
    ⟪f, finiteRank a b f⟫ =
      (fun k ↦ ⟪Sum.elim a b k, f⟫) ⬝ᵥ swapHalf ι *ᵥ (fun k ↦ ⟪Sum.elim a b k, f⟫) := by
  rw [inner_finiteRank_apply, dotProduct_swapHalf_mulVec]
  rfl

/-- **The quadratic form of a finite-rank operator from a matrix inequality** (Hou–Wang–Yang,
Remark 8). Let `W` be the Gram matrix of the two families `a`, `b` side by side and `K` the
matrix `swapHalf`. If `|(W α)ᵀ K (W α)| ≤ θ αᵀ W α` for every `α`, then `|⟪f, T f⟫| ≤ θ ‖f‖²`:
`⟪f, T f⟫ = cᵀ K c` for the pairings `c` of `f` with the two families, and
`abs_pairing_quadForm_le_of_gram` applies. -/
theorem abs_inner_finiteRank_le_of_gram [DecidableEq ι] (a b : ι → X) {θ : ℝ} (hθ : 0 ≤ θ)
    (hcert : ∀ α : ι ⊕ ι → ℝ,
      |(Matrix.gram ℝ (Sum.elim a b) *ᵥ α) ⬝ᵥ swapHalf ι *ᵥ (Matrix.gram ℝ (Sum.elim a b) *ᵥ α)| ≤
        θ * (α ⬝ᵥ Matrix.gram ℝ (Sum.elim a b) *ᵥ α)) (f : X) :
    |⟪f, finiteRank a b f⟫| ≤ θ * ‖f‖ ^ 2 := by
  rw [inner_finiteRank_apply_eq_swapHalf]
  exact abs_pairing_quadForm_le_of_gram (Sum.elim a b) (swapHalf ι) hθ hcert f

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The quadratic form of a finite-rank operator, spectral form** (Hou–Wang–Yang, Remark 8):
`|⟪f, T f⟫| ≤ ‖W^{1/2} K W^{1/2}‖ ‖f‖²`, with `W` the Gram matrix of the two families side by
side. -/
theorem abs_inner_finiteRank_le_l2_opNorm [DecidableEq ι] (a b : ι → X) (f : X) :
    |⟪f, finiteRank a b f⟫| ≤
      ‖CFC.sqrt (Matrix.gram ℝ (Sum.elim a b)) * swapHalf ι *
        CFC.sqrt (Matrix.gram ℝ (Sum.elim a b))‖ * ‖f‖ ^ 2 :=
  abs_inner_finiteRank_le_of_gram a b (norm_nonneg _)
    (abs_gram_quadForm_le_l2_opNorm (Matrix.posSemidef_gram ℝ _) _) f

/-- **The quadratic form of an operator and its symmetric part** (Hou–Wang–Yang, Remark 8).
For a bounded operator `T` on a real Hilbert space, the supremum of `|⟪T f, f⟫| / ‖f‖²` is the
norm of `(T + T*) / 2`. -/
theorem norm_symmetricPart_eq_iSup_rayleighQuotient [CompleteSpace X] (T : X →L[ℝ] X) :
    ‖(2⁻¹ : ℝ) • (T + ContinuousLinearMap.adjoint T)‖ = ⨆ f, |T.rayleighQuotient f| := by
  set A : X →L[ℝ] X := (2⁻¹ : ℝ) • (T + ContinuousLinearMap.adjoint T)
  have hA : (A : X →ₗ[ℝ] X).IsSymmetric := by
    intro x y
    simp only [A, ContinuousLinearMap.coe_coe, smul_apply, add_apply, inner_smul_left,
      inner_smul_right, inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, conj_trivial]
    ring
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient A hA]
  congr 1
  funext f
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, A,
    smul_apply, add_apply, inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, RCLike.re_to_real, conj_trivial]
  rw [real_inner_comm f (T f)]
  congr 2
  ring

end Symmetric

end PDE.Analysis.Operator
