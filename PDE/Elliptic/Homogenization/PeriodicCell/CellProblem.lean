/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Coefficient
public import PDE.Elliptic.Homogenization.VariationalCell

/-!
# Periodic cell gradients and the effective matrix in arbitrary dimension

Lax–Milgram constructs the unique cell correction in the closure of gradients of
periodic potentials. Its flux has zero pairing with this space, and its mean defines
the effective matrix. The original ellipticity lower bound is preserved; symmetry
is preserved when present. The correction is a limit of gradients of periodic potentials.

The periodic Sobolev potential of the cell gradient is `PeriodicCell.Potential`, and the
convergence of the oscillatory Dirichlet problems is `PeriodicCell.Convergence`.
-/

@[expose] public noncomputable section

open Matrix MeasureTheory Set Filter PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))

variable {α : ℝ} (hα : 0 < α)
  (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)

/-- The periodic cell gradient constructed in the closed gradient space. -/
def correctorGradient : (ℝ^n) →L[ℝ] gradientSpace n :=
  VariationalCell.correctorCLM (gradientSpace n) (coefficientForm A)
    (coefficientForm_isCoercive A hα hA) (constantField n)

/-- The constant imposed gradient plus its constructed periodic correction. -/
def correctedField : (ℝ^n) →L[ℝ] Lp (ℝ^n) 2 (cellMeasure n) :=
  VariationalCell.totalGradientCLM (gradientSpace n) (coefficientForm A)
    (coefficientForm_isCoercive A hα hA) (constantField n)

/-- The corrected flux annihilates every gradient in the closed periodic space. -/
theorem correctorGradient_equation (ξ : ℝ^n) (g : gradientSpace n) :
    (∫ x, ⟪A x (correctedField A hα hA ξ x),
      (g : Lp (ℝ^n) 2 (cellMeasure n)) x⟫_ℝ ∂cellMeasure n) = 0 := by
  rw [← coefficientForm_eq_integral]
  exact VariationalCell.corrector_equation (gradientSpace n) (coefficientForm A)
    (coefficientForm_isCoercive A hα hA) (constantField n) ξ g

/-- The periodic cell equation uniquely determines the correction in this space. -/
theorem correctorGradient_unique (ξ : ℝ^n) {g : gradientSpace n}
    (hg : ∀ h : gradientSpace n,
      (∫ x, ⟪A x ((constantField n ξ + (g : Lp (ℝ^n) 2 (cellMeasure n))) x),
        (h : Lp (ℝ^n) 2 (cellMeasure n)) x⟫_ℝ ∂cellMeasure n) = 0) :
    g = correctorGradient A hα hA ξ := by
  apply VariationalCell.corrector_unique (gradientSpace n) (coefficientForm A)
    (coefficientForm_isCoercive A hα hA) (constantField n) ξ
  intro h
  rw [coefficientForm_eq_integral]
  exact hg h

/-- The cell correction is a strong `L²` limit of gradients of periodic potentials. -/
theorem correctorGradient_approximation (ξ : ℝ^n) :
    ∃ (u : ℕ → C(UnitAddTorus (Fin n), ℝ))
      (g : ℕ → C(UnitAddTorus (Fin n), ℝ^n)),
      (∀ k x i t, HasDerivAt (fun s ↦ u k (x + coordinateShift i s))
        (g k (x + coordinateShift i t) i) t) ∧
      Tendsto (fun k ↦ ContinuousMap.toLp 2 (cellMeasure n) ℝ (g k)) atTop
        (𝓝 (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n))) := by
  obtain ⟨v, hv, ht⟩ := exists_gradient_approximation (correctorGradient A hα hA ξ)
  choose u g hd he using hv
  refine ⟨u, g, hd, ?_⟩
  exact ht.congr' (Eventually.of_forall he)

/-- The effective bilinear form of the periodic coefficient. -/
def effectiveForm : (ℝ^n) →L[ℝ] (ℝ^n) →L[ℝ] ℝ :=
  VariationalCell.effectiveForm (gradientSpace n) (coefficientForm A)
    (coefficientForm_isCoercive A hα hA) (constantField n)

/-- The linear map represented by the effective bilinear form. -/
def effectiveOperator : (ℝ^n) →L[ℝ] (ℝ^n) :=
  (InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (effectiveForm A hα hA)

/-- The effective operator represents the effective flux pairing. -/
theorem effectiveOperator_inner (ξ η : ℝ^n) :
    ⟪effectiveOperator A hα hA ξ, η⟫_ℝ = effectiveForm A hα hA ξ η :=
  InnerProductSpace.toDual_symm_apply

/-- The effective coefficient retains the original ellipticity constant. -/
theorem effectiveOperator_lower_bound (ξ : ℝ^n) :
    α * ‖ξ‖ ^ 2 ≤ ⟪effectiveOperator A hα hA ξ, ξ⟫_ℝ := by
  rw [effectiveOperator_inner]
  exact VariationalCell.effectiveForm_lower_bound (gradientSpace n) (coefficientForm A)
    (coefficientForm_isCoercive A hα hA) (constantField n) α hα.le
    (coefficientForm_lower_bound A α hA) constantField_orthogonal_gradientSpace ξ

/-- The effective operator equals the mean corrected microscopic flux. -/
theorem effectiveOperator_eq_mean_flux (ξ : ℝ^n) :
    effectiveOperator A hα hA ξ =
      ∫ x, A x (correctedField A hα hA ξ x) ∂cellMeasure n := by
  let v := correctedField A hα hA ξ
  have hi : Integrable (fun x ↦ A x (v x)) (cellMeasure n) :=
    ((Lp.memLp (coefficientOperator A v)).integrable (by norm_num)).congr
      (coefficientOperator_ae A v)
  apply ext_inner_right ℝ
  intro η
  rw [effectiveOperator_inner]
  change coefficientForm A v (constantField n η) = _
  rw [coefficientForm_eq_integral]
  calc
    _ = ∫ x, ⟪A x (v x), η⟫_ℝ ∂cellMeasure n := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 (cellMeasure n) η] with x hx
      rw [show (constantField n η : UnitAddTorus (Fin n) → ℝ^n) x = η from hx]
    _ = ∫ x, ⟪η, A x (v x)⟫_ℝ ∂cellMeasure n :=
      integral_congr_ae (Eventually.of_forall fun x ↦ real_inner_comm _ _)
    _ = ⟪η, ∫ x, A x (v x) ∂cellMeasure n⟫_ℝ := integral_inner hi η
    _ = _ := real_inner_comm _ _

/-- Almost-everywhere microscopic symmetry passes to the effective form. -/
theorem effectiveForm_symmetric
    (hsymm : ∀ᵐ x ∂cellMeasure n, ∀ ξ η : ℝ^n, ⟪A x ξ, η⟫_ℝ = ⟪A x η, ξ⟫_ℝ)
    (ξ η : ℝ^n) : effectiveForm A hα hA ξ η = effectiveForm A hα hA η ξ := by
  apply VariationalCell.effectiveForm_symmetric
  intro v w
  rw [coefficientForm_eq_integral, coefficientForm_eq_integral]
  apply integral_congr_ae
  filter_upwards [hsymm] with x hx
  exact hx (v x) (w x)

/-- The effective operator in the standard Euclidean coordinate basis. -/
def effectiveMatrix : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.toEuclideanLin.symm (effectiveOperator A hα hA).toLinearMap

/-- The matrix acts as the effective operator on Euclidean coordinates. -/
theorem effectiveMatrix_mulVec (ξ : ℝ^n) :
    effectiveMatrix A hα hA *ᵥ (ξ : Fin n → ℝ) = effectiveOperator A hα hA ξ := by
  have h := congrArg (fun L : (ℝ^n) →ₗ[ℝ] (ℝ^n) ↦ L ξ)
    (Matrix.toEuclideanLin.apply_symm_apply (effectiveOperator A hα hA).toLinearMap)
  change WithLp.toLp 2 (effectiveMatrix A hα hA *ᵥ (ξ : Fin n → ℝ)) =
    effectiveOperator A hα hA ξ at h
  exact congrArg (fun v : ℝ^n ↦ (v : Fin n → ℝ)) h

/-- The effective matrix satisfies the original uniform ellipticity lower bound. -/
theorem effectiveMatrix_lower_bound (ξ : ℝ^n) :
    α * ‖ξ‖ ^ 2 ≤ (ξ : Fin n → ℝ) ⬝ᵥ (effectiveMatrix A hα hA *ᵥ (ξ : Fin n → ℝ)) := by
  rw [effectiveMatrix_mulVec]
  simpa only [dotProduct, PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using
    effectiveOperator_lower_bound A hα hA ξ

/-- Each matrix entry is the effective pairing of the corresponding basis vectors. -/
theorem effectiveMatrix_entry (i j : Fin n) :
    effectiveMatrix A hα hA i j =
      effectiveForm A hα hA (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [← effectiveOperator_inner, EuclideanSpace.inner_basisFun_real]
  change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (effectiveOperator A hα hA).toLinearMap i j = _
  rw [LinearMap.toMatrix_apply]
  rfl

/-- A symmetric periodic coefficient has a symmetric effective matrix. -/
theorem effectiveMatrix_isSymm
    (hsymm : ∀ᵐ x ∂cellMeasure n, ∀ ξ η : ℝ^n, ⟪A x ξ, η⟫_ℝ = ⟪A x η, ξ⟫_ℝ) :
    (effectiveMatrix A hα hA).IsSymm := by
  ext i j
  change effectiveMatrix A hα hA j i = effectiveMatrix A hα hA i j
  rw [effectiveMatrix_entry, effectiveMatrix_entry, effectiveForm_symmetric A hα hA hsymm]

end PDE.Elliptic.Homogenization.PeriodicCell
