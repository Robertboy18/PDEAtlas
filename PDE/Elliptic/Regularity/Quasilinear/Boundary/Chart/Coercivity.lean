/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Parameters

/-!
# Monotonicity constants from chart geometry

The compact chart estimates bound the inverse-Jacobian weight below
and the smallest singular value of the physical-gradient map away from zero.
Here the coordinate singular-value estimate is converted to the operator norm
form used by nonlinear fluxes. No inverse of the unknown Hessian is assumed.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open Set SobolevSpace SobolevSpace.GraphSpace.BoundaryRegularity
open PDE.Analysis.Operator
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The coordinate chart estimate bounds the physical-gradient map below. -/
theorem norm_chartGradientMap_lower_bound
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) {y : ℝ^n} {c : ℝ} (hc : 0 ≤ c)
    (hD : HasGradientLowerBound (chartDerivativeMatrix E (E.symm y)) c) (z : ℝ^n) :
    c * ‖z‖ ≤ ‖chartGradientMap E y z‖ := by
  have heq : Matrix.mulVec (chartDerivativeMatrix E (E.symm y)) z.ofLp =
      (chartGradientMap E y z).ofLp := by
    funext i
    exact mulVec_chartDerivativeMatrix_eq_adjoint E hE (E.symm y) z i
  have hsq := hD z.ofLp
  rw [heq] at hsq
  have hnorm (v : ℝ^n) : v.ofLp ⬝ᵥ v.ofLp = ‖v‖ ^ 2 := by
    simpa only [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq v).symm
  rw [hnorm, hnorm] at hsq
  have hp : 0 ≤ c * ‖z‖ := mul_nonneg hc (norm_nonneg z)
  have ht := norm_nonneg (chartGradientMap E y z)
  nlinarith only [hsq, hp, ht]

/-- A positive physical monotonicity constant yields a uniform positive chart
constant on every compact subset of the target. The inverse derivative and its
determinant supply both lower bounds, independently of the unknown function. -/
theorem exists_chartFlux_pairing_lower_bound_on_compact
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKt : K ⊆ E.target)
    (A : ℝ^n → ℝ^n) {θ : ℝ} (hθ : 0 < θ)
    (hA : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫) :
    ∃ m : ℝ, 0 < m ∧ ∀ y ∈ K,
      ∀ z w, m * ‖z - w‖ * ‖z - w‖ ≤
        ⟪chartFlux E A y z - chartFlux E A y w, z - w⟫ := by
  by_cases hne : K.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun y hy ↦ False.elim (hne ⟨y, hy⟩)⟩
  let J := inverseChartJacobianWeight E
  have hJcont : Continuous J :=
    (ContinuousLinearMap.continuous_det.comp
      (hSymm.continuous_fderiv (by norm_num))).abs
  obtain ⟨yJ, hyJ, hJmin⟩ := hK.exists_isMinOn hne hJcont.continuousOn
  let Jzero := J yJ
  have hJzero : 0 < Jzero :=
    inverseChartJacobianWeight_pos_on_target E hE hSymm (hKt hyJ)
  let B := fderiv ℝ (fun y ↦ E.symm y)
  obtain ⟨yB, hyB, hBmax⟩ := hK.exists_isMaxOn hne
    (hSymm.continuous_fderiv (by norm_num)).norm.continuousOn
  let C := max 1 ‖B yB‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let c := C⁻¹
  have hc : 0 < c := inv_pos.mpr hC
  refine ⟨Jzero * θ * c ^ 2, by positivity, ?_⟩
  intro y hy z w
  have hD := hasGradientLowerBound_of_inverseDerivative_norm_le E hE hSymm
    (hKt hy) hC ((hBmax hy).trans (le_max_right 1 ‖B yB‖))
  have hT (v : ℝ^n) : c * ‖v‖ ≤ ‖chartGradientMap E y v‖ :=
    norm_chartGradientMap_lower_bound E hE hc.le hD v
  have hmono := pullbackFlux_pairing_lower_bound A hθ.le hA (chartGradientMap E y)
    hc.le hT (inverseChartJacobianWeight_nonneg E y) z w
  apply le_trans _ hmono
  have hj : Jzero ≤ inverseChartJacobianWeight E y := hJmin hy
  change (Jzero * θ * c ^ 2) * ‖z - w‖ * ‖z - w‖ ≤
    (inverseChartJacobianWeight E y * θ * c ^ 2) * ‖z - w‖ * ‖z - w‖
  gcongr

end PDE.Elliptic.Regularity.Quasilinear
