/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.CellProblem
public import PDE.Analysis.Integration.PeriodicAveraging.LocalMeasure
public import PDE.Elliptic.Variational.DivergenceSolution

/-!
# Canonical Dirichlet solutions for rescaled periodic coefficients

The periodic operator field induces measurable matrix coefficients on Euclidean
domains. Rescaling preserves the original ellipticity constant. The Dirichlet
solver `weakDivergenceSolve` therefore constructs a unique `H¹₀` solution for every nonzero
period on a bounded open domain. The original ellipticity constant and the
zero-boundary Poincaré inequality bound the whole solution family uniformly.
The effective matrix defines its canonical Dirichlet solution in the same space;
convergence to it is `PeriodicCell.Convergence`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

/-- Each entry of a bounded periodic operator field remains essentially bounded after rescaling. -/
theorem memLp_rescaledMatrix_entry {n : ℕ}
    (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n)) (Ω : Set (ℝ^n))
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin n) :
    MemLp (fun x ↦ A (toTorus n (ε⁻¹ • x)) (PiLp.single 2 j 1) i) ∞
      (domainMeasure n Ω) := by
  let L : ((ℝ^n) →L[ℝ] (ℝ^n)) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (ContinuousLinearMap.apply ℝ (ℝ^n) (PiLp.single 2 j 1))
  exact ((memLp_top_comp_toTorus_smul A ε⁻¹ (inv_ne_zero hε)).mono_measure
    Measure.restrict_le_self).continuousLinearMap_comp L

/-- The matrix coefficient `A(x/ε)` in the canonical weak elliptic API. -/
def rescaledMatrixCoefficient {n : ℕ}
    (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n)) (Ω : Set (ℝ^n))
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin n) : DerivLp n ∞ Ω :=
  (memLp_rescaledMatrix_entry A Ω ε hε i j).toLp _

/-- The stored coefficient entries represent the rescaled periodic field. -/
theorem rescaledMatrixCoefficient_ae {n : ℕ}
    (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n)) (Ω : Set (ℝ^n))
    (ε : ℝ) (hε : ε ≠ 0) :
    ∀ᵐ x ∂domainMeasure n Ω, ∀ i j : Fin n,
      rescaledMatrixCoefficient A Ω ε hε i j x =
        A (toTorus n (ε⁻¹ • x)) (PiLp.single 2 j 1) i := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  exact fun j ↦ (memLp_rescaledMatrix_entry A Ω ε hε i j).coeFn_toLp

/-- The quadratic expression of the coordinate matrix is the operator's inner product. -/
theorem sum_matrix_entries_eq_inner {n : ℕ} (B : (ℝ^n) →L[ℝ] (ℝ^n))
    (ξ : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, B (PiLp.single 2 j 1) i * ξ j * ξ i) =
      ⟪B (WithLp.toLp 2 ξ), WithLp.toLp 2 ξ⟫_ℝ := by
  classical
  have hξ : (∑ j : Fin n, ξ j • (PiLp.single 2 j 1 : ℝ^n)) = WithLp.toLp 2 ξ := by
    apply (WithLp.equiv 2 _).injective
    ext i
    simp [Pi.single_apply]
  have hcoord (i : Fin n) :
      ∑ j : Fin n, B (PiLp.single 2 j 1) i * ξ j = B (WithLp.toLp 2 ξ) i := by
    conv_rhs => rw [← hξ, map_sum]
    simp [map_smul, mul_comm]
  calc
    _ = ∑ i : Fin n, B (WithLp.toLp 2 ξ) i * ξ i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_mul, hcoord]
    _ = _ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)

include hα hA in
/-- Periodic rescaling preserves almost-everywhere ellipticity with the same constant. -/
theorem aeUniformlyElliptic_rescaledMatrixCoefficient (Ω : Set (ℝ^n))
    (ε : ℝ) (hε : ε ≠ 0) :
    AEUniformlyElliptic (rescaledMatrixCoefficient A Ω ε hε) α := by
  refine ⟨hα, ?_⟩
  filter_upwards [rescaledMatrixCoefficient_ae A Ω ε hε,
    ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
      (inv_ne_zero hε)).ae hA)] with x hx hAx
  intro ξ
  simp only [hx, sum_matrix_entries_eq_inner]
  convert! hAx (WithLp.toLp 2 ξ) using 1
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [pow_two]

include hα hA in
/-- Every nonzero period gives a unique canonical weak Dirichlet solution. -/
theorem existsUnique_rescaledDirichletSolution {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (ε : ℝ) (hε : ε ≠ 0) (f : DerivLp n 2 Ω) :
    ∃! u : H¹₀(Ω), IsWeakDivergenceSolution (rescaledMatrixCoefficient A Ω ε hε) f u :=
  IsWeakDivergenceSolution.existsUnique_of_ae hΩo hn hΩ
    (rescaledMatrixCoefficient A Ω ε hε)
    (aeUniformlyElliptic_rescaledMatrixCoefficient A hα hA Ω ε hε) f

/-- The canonical weak solution for the oscillatory periodic matrix. -/
def rescaledDirichletSolution {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (ε : ℝ) (hε : ε ≠ 0) (f : DerivLp n 2 Ω) : H¹₀(Ω) :=
  weakDivergenceSolve hn hΩ (rescaledMatrixCoefficient A Ω ε hε)
    (aeUniformlyElliptic_rescaledMatrixCoefficient A hα hA Ω ε hε) f

/-- The named oscillatory solution satisfies the distributional equation. -/
theorem rescaledDirichletSolution_isWeakDivergenceSolution {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (ε : ℝ) (hε : ε ≠ 0) (f : DerivLp n 2 Ω) :
    IsWeakDivergenceSolution (rescaledMatrixCoefficient A Ω ε hε) f
      (rescaledDirichletSolution A hα hA hn hΩ ε hε f) := by
  exact weakDivergenceSolve_isWeakDivergenceSolution hΩo hn hΩ
    (rescaledMatrixCoefficient A Ω ε hε)
    (aeUniformlyElliptic_rescaledMatrixCoefficient A hα hA Ω ε hε) f

/-- The canonical oscillatory Dirichlet solutions have a period-independent Sobolev bound. -/
theorem exists_rescaledDirichletSolution_norm_bound {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (f : DerivLp n 2 Ω) :
    ∃ M : ℝ, ∀ ε : ℝ, ∀ hε : ε ≠ 0,
      ‖rescaledDirichletSolution A hα hA hn hΩ ε hε f‖ ≤ M := by
  obtain ⟨c, hc, hdir⟩ := dirichletForm_isCoercive hn hΩ
  let ell := loadFunctional f
  refine ⟨‖ell‖ / (α * c), fun ε hε ↦ ?_⟩
  let u := rescaledDirichletSolution A hα hA hn hΩ ε hε f
  apply PDE.Analysis.Variational.norm_le_dual_norm_div_of_pairing ell (α * c)
    (mul_pos hα hc)
  have heq := (isWeakSolution_iff_isWeakDivergenceSolution hΩo
    (rescaledMatrixCoefficient A Ω ε hε) f u).2
      (rescaledDirichletSolution_isWeakDivergenceSolution A hα hA hn hΩ hΩo ε hε f)
  calc
    _ = α * (c * ‖u‖ * ‖u‖) := by ring
    _ ≤ α * dirichletForm u u := mul_le_mul_of_nonneg_left (hdir _) hα.le
    _ ≤ variableCoeffForm
        (multiplicationCoefficientOperator (rescaledMatrixCoefficient A Ω ε hε)) u u :=
      (integratedElliptic_multiplication_of_ae (rescaledMatrixCoefficient A Ω ε hε)
        (aeUniformlyElliptic_rescaledMatrixCoefficient A hα hA Ω ε hε)).2 u
    _ = ell u := heq u

/-- The effective matrix as a constant coefficient in the canonical elliptic API. -/
def effectiveMatrixCoefficient (Ω : Set (ℝ^n)) (i j : Fin n) : DerivLp n ∞ Ω :=
  (memLp_top_const (effectiveMatrix A hα hA i j)).toLp _

/-- The effective coefficient entries represent the derived constant matrix. -/
theorem effectiveMatrixCoefficient_ae (Ω : Set (ℝ^n)) :
    ∀ᵐ x ∂domainMeasure n Ω, ∀ i j : Fin n,
      effectiveMatrixCoefficient A hα hA Ω i j x = effectiveMatrix A hα hA i j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  exact fun j ↦ (memLp_top_const (effectiveMatrix A hα hA i j)).coeFn_toLp

/-- The constant effective coefficient satisfies the same canonical ellipticity predicate. -/
theorem aeUniformlyElliptic_effectiveMatrixCoefficient (Ω : Set (ℝ^n)) :
    AEUniformlyElliptic (effectiveMatrixCoefficient A hα hA Ω) α := by
  refine ⟨hα, ?_⟩
  filter_upwards [effectiveMatrixCoefficient_ae A hα hA Ω] with x hx
  intro ξ
  have h := effectiveMatrix_lower_bound A hα hA (WithLp.toLp 2 ξ)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa only [hx, PiLp.toLp_apply, pow_two,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

/-- The effective Dirichlet solution uses the derived mean-flux matrix. -/
def effectiveDirichletSolution {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω) : H¹₀(Ω) :=
  weakDivergenceSolve hn hΩ (effectiveMatrixCoefficient A hα hA Ω)
    (aeUniformlyElliptic_effectiveMatrixCoefficient A hα hA Ω) f

/-- The effective solution satisfies the weak equation. -/
theorem effectiveDirichletSolution_isWeakDivergenceSolution {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω) (f : DerivLp n 2 Ω) :
    IsWeakDivergenceSolution (effectiveMatrixCoefficient A hα hA Ω) f
      (effectiveDirichletSolution A hα hA hn hΩ f) :=
  weakDivergenceSolve_isWeakDivergenceSolution hΩo hn hΩ
    (effectiveMatrixCoefficient A hα hA Ω)
    (aeUniformlyElliptic_effectiveMatrixCoefficient A hα hA Ω) f

end PDE.Elliptic.Homogenization.PeriodicCell
