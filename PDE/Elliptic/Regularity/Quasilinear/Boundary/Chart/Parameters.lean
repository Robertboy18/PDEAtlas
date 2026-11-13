/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartCoefficientRegularity
public import PDE.Analysis.Operator.StrongMonotonicity.PullbackParameters
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Chart parameters for a nonlinear flux

If `y = E(x)`, a gradient in the `y` variables becomes `DE(x)† p` in physical
coordinates. The flux therefore transforms as `J DE(x) A(DE(x)† p)`, where
`J = |det D(E⁻¹)(y)|`. These definitions use Fréchet derivatives.

A larger smooth cutoff gives globally bounded Lipschitz representatives of the
gradient map and Jacobian weight. The signed determinant is cut off before taking
its absolute value, so the proof never differentiates an absolute value at zero.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open Set SobolevSpace SobolevSpace.GraphSpace.BoundaryRegularity
open PDE.Analysis.Operator
open scoped NNReal

variable {n : ℕ}

/-- The physical-gradient map associated with a chart, evaluated at a target point. -/
def chartGradientMap (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (y : ℝ^n) :
    ℝ^n →L[ℝ] ℝ^n :=
  (fderiv ℝ (fun x ↦ E x) (E.symm y)).adjoint

/-- The transformed nonlinear flux, including the inverse-Jacobian weight. -/
def chartFlux (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → ℝ^n) (y p : ℝ^n) : ℝ^n :=
  pullbackFlux A (chartGradientMap E y) (inverseChartJacobianWeight E y) p

/-- Twice continuously differentiable chart representatives give a continuously
differentiable field of physical-gradient maps. -/
theorem contDiff_chartGradientMap
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y)) :
    ContDiff ℝ 1 (chartGradientMap E) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ (fun x ↦ E x)) :=
    hE.fderiv_right (by norm_num)
  exact ContinuousLinearMap.adjoint.toContinuousLinearEquiv.contDiff.comp (hd.comp hSymm)

/-- A compact multiplier extends the chart gradient map to a bounded global field. -/
def cutoffChartGradientMap (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (y : ℝ^n) : ℝ^n →L[ℝ] ℝ^n :=
  κ.toFun y • chartGradientMap E y

/-- The cutoff gradient map has the regularity needed for a global Lipschitz bound. -/
theorem contDiff_cutoffChartGradientMap
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ContDiff ℝ 1 (cutoffChartGradientMap E κ) :=
  (κ.contDiff.of_le (by simp)).smul (contDiff_chartGradientMap E hE hSymm)

/-- The global weight is the absolute value of the cut-off signed determinant. -/
def cutoffChartJacobian (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (y : ℝ^n) : ℝ :=
  |κ.toFun y * (fderiv ℝ (fun z ↦ E.symm z) y).det|

/-- Where the larger cutoff is one, both global parameters are exactly the
chart parameters. -/
theorem cutoffChartParameters_eq_of_eq_one
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {y : ℝ^n} (hy : κ.toFun y = 1) :
    cutoffChartGradientMap E κ y = chartGradientMap E y ∧
      cutoffChartJacobian E κ y = inverseChartJacobianWeight E y := by
  simp only [cutoffChartGradientMap, cutoffChartJacobian, inverseChartJacobianWeight,
    hy, one_smul, one_mul, and_self]

private theorem exists_bound_and_lipschitz
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∃ M D : ℝ≥0, (∀ x, ‖f x‖ ≤ M) ∧
      ∀ x y, ‖f x - f y‖ ≤ D * ‖x - y‖ := by
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hs
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by norm_num)
  exact ⟨Real.toNNReal M, D, fun x ↦ (hM x).trans (Real.le_coe_toNNReal M),
    hD.norm_sub_le⟩

/-- The localized physical-gradient map is uniformly bounded and Lipschitz. -/
theorem exists_cutoffChartGradientMap_bounds
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ E.symm y))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ M D : ℝ≥0,
      (∀ y, ‖cutoffChartGradientMap E κ y‖ ≤ M) ∧
      ∀ y z, ‖cutoffChartGradientMap E κ y - cutoffChartGradientMap E κ z‖ ≤
        D * ‖y - z‖ := by
  have hT : ContDiff ℝ 1 (cutoffChartGradientMap E κ) :=
    contDiff_cutoffChartGradientMap E hE (hSymm.of_le (by norm_num)) κ
  have hTs : HasCompactSupport (cutoffChartGradientMap E κ) := by
    change HasCompactSupport (fun y ↦ κ.toFun y • chartGradientMap E y)
    exact κ.hasCompactSupport.smul_right (f' := chartGradientMap E)
  exact exists_bound_and_lipschitz hT hTs

/-- Cutting off the signed determinant and then taking its absolute value gives
a bounded Lipschitz Jacobian weight, including where the cutoff vanishes. -/
theorem exists_cutoffChartJacobian_bounds
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hSymm : ContDiff ℝ 2 (fun y ↦ E.symm y))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ B H : ℝ≥0, (∀ y, |cutoffChartJacobian E κ y| ≤ B) ∧
      ∀ y z, |cutoffChartJacobian E κ y - cutoffChartJacobian E κ z| ≤
        H * ‖y - z‖ := by
  let d : ℝ^n → ℝ := fun y ↦ κ.toFun y * (fderiv ℝ (fun z ↦ E.symm z) y).det
  have hd : ContDiff ℝ 1 d :=
    (κ.contDiff.of_le (by simp)).mul (contDiff_det_fderiv _ hSymm)
  have hds : HasCompactSupport d := by
    change HasCompactSupport (fun y ↦ κ.toFun y * (fderiv ℝ (fun z ↦ E.symm z) y).det)
    exact κ.hasCompactSupport.mul_right
      (f' := fun y ↦ (fderiv ℝ (fun z ↦ E.symm z) y).det)
  obtain ⟨B, H, hB, hH⟩ := exists_bound_and_lipschitz hd hds
  refine ⟨B, H, ?_, ?_⟩
  · intro y
    change abs (abs (d y)) ≤ _
    simpa only [abs_abs, Real.norm_eq_abs] using hB y
  · intro y z
    exact (abs_abs_sub_abs_le (d y) (d z)).trans
      (by simpa only [Real.norm_eq_abs] using hH y z)

end PDE.Elliptic.Regularity.Quasilinear
