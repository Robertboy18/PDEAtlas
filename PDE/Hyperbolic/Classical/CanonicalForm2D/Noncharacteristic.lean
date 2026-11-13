/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D.FirstIntegral
public import PDE.Hyperbolic.Classical.CanonicalForm2D.Algebra
public import PDE.Hyperbolic.Classical.CanonicalForm2D.Transformation
public import PDE.Analysis.Calculus.Jacobian.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Construction with a noncharacteristic initial line

When the first pure coefficient is nonzero, the two characteristic slopes define
scalar ODEs transverse to the line `x₀ = constant`. Their inverse labels construct
independent C² characteristic coordinates. All regularity hypotheses are germs.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology
open PDE.Analysis

namespace Hyperbolic.CanonicalForm2D

/-- C² principal coefficients give C² characteristic slopes near a hyperbolic point
with nonzero first pure coefficient. -/
theorem contDiffAt_characteristicSlope {A : ℝ^2 → PrincipalPart} {x : ℝ^2}
    (h₁₁ : ContDiffAt ℝ 2 (fun y ↦ (A y).a11) x) (h₁₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a12) x)
    (h₂₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a22) x) (ha : (A x).a11 ≠ 0) (hD : 0 < (A x).discriminant)
    (ε : ℝ) :
    ContDiffAt ℝ 2 (fun y ↦ (A y).characteristicSlope ε) x := by
  have hdisc : ContDiffAt ℝ 2 (fun y ↦ (A y).discriminant) x := (h₁₂.pow 2).sub (h₁₁.mul h₂₂)
  exact (h₁₂.add (contDiffAt_const.mul (hdisc.sqrt (ne_of_gt hD)))).div h₁₁ ha

/-- The two ODE families construct a characteristic coordinate map with nonzero
Jacobian. Neither the coordinates nor their transport equations are hypotheses. -/
theorem exists_characteristic_map_of_a11_ne_zero {A : ℝ^2 → PrincipalPart} {x : ℝ^2}
    (h₁₁ : ContDiffAt ℝ 2 (fun y ↦ (A y).a11) x) (h₁₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a12) x)
    (h₂₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a22) x) (ha : (A x).a11 ≠ 0) (hA : (A x).IsHyperbolic) :
    ∃ Φ : ℝ^2 → ℝ^2, ContDiffAt ℝ 2 Φ x ∧ (jacobianMatrix Φ x).det ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, (transformedPrincipal A Φ y).a11 = 0 ∧
        (transformedPrincipal A Φ y).a22 = 0) := by
  have hD := ((A x).isHyperbolic_iff_discriminant_pos).mp hA
  obtain ⟨ξ, hξ, hξ₁, hξt⟩ :=
    exists_local_firstIntegral (contDiffAt_characteristicSlope h₁₁ h₁₂ h₂₂ ha hD 1)
  obtain ⟨η, hη, hη₁, hηt⟩ :=
    exists_local_firstIntegral (contDiffAt_characteristicSlope h₁₁ h₁₂ h₂₂ ha hD (-1))
  let Φ : ℝ^2 → ℝ^2 := fun y ↦ !₂[ξ y, η y]
  have hΦ : ContDiffAt ℝ 2 Φ x := by
    refine (contDiffAt_piLp 2).mpr fun i ↦ ?_
    fin_cases i
    · exact hξ
    · exact hη
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    change (∂[0] ξ) x * (∂[1] η) x - (∂[1] ξ) x * (∂[0] η) x ≠ 0
    rw [hξ₁, hη₁, mul_one, one_mul]
    have hξ₀ := hξt.self_of_nhds
    have hη₀ := hηt.self_of_nhds
    rw [hξ₁, mul_one] at hξ₀
    rw [hη₁, mul_one] at hη₀
    have hne := (A x).characteristicSlope_ne ha hD
    intro hz
    apply hne
    linarith
  · have hdisc : ContinuousAt (fun y ↦ (A y).discriminant) x :=
      ((h₁₂.pow 2).sub (h₁₁.mul h₂₂)).continuousAt
    filter_upwards [hξt, hηt, h₁₁.continuousAt.eventually_ne ha,
      hdisc.eventually (eventually_gt_nhds hD)] with y hξy hηy hay hDy
    constructor
    · exact (A y).quadratic_eq_zero_of_transport _ _ _
        ((A y).characteristicSlope_equation 1 (by norm_num) hay hDy.le) hξy
    · exact (A y).quadratic_eq_zero_of_transport _ _ _
        ((A y).characteristicSlope_equation (-1) (by norm_num) hay hDy.le) hηy

end Hyperbolic.CanonicalForm2D
