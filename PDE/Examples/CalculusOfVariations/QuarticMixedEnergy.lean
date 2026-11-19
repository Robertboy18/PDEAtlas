/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Dirichlet
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A quartic mixed energy on a bounded measurable subset of the line

The density `(s² - 1)² + ‖z‖⁴` is convex in the gradient, but not in the value.
Its zero competitor has density one, so boundedness of the domain supplies a
finite competitor. The minimization theorem constructs the minimum at `p = 4`.

The closed unit ball is an explicit nonopen domain. Its boundary condition is
the supported smooth-core closure, as in the general measurable-domain theorem.
No trace atlas, prescribed minimizer, or assumed lower semicontinuity is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace PDE.Examples.QuarticMixedEnergy

/-- The double-well value energy plus the fourth power of the weak gradient,
integrated against Lebesgue measure restricted to `Ω`. The integral is extended
and nonnegative; finiteness of a minimizing function is part of the conclusion. -/
def energy {Ω : Set (ℝ^1)} (u : W^{1,4}(Ω)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    (((wkpBaseCoordinateCLM (n := 1) (m := 1) (p := 4) (Ω := Ω) u x) ^ 2 - 1) ^ 2 +
      ‖∇ u x‖ ^ 4) ∂domainMeasure 1 Ω

/-- Differentiating the square of the squared norm gives the quartic
supporting field, including at the zero gradient. -/
private theorem hasFDerivAt_norm_four (z : ℝ^1) :
    HasFDerivAt (fun y : ℝ^1 ↦ ‖y‖ ^ 4)
      (innerSL ℝ ((4 * ‖z‖ ^ 2) • z)) z := by
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hfour := (h.mul h).congr_fderiv
    (g' := innerSL ℝ ((4 * ‖z‖ ^ 2) • z)) (by
      ext v
      simp only [two_smul, add_apply, smul_apply,
        innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
      ring)
  have hfun : ((fun y : ℝ^1 ↦ ‖y‖ ^ 2) * fun y ↦ ‖y‖ ^ 2) =
      (fun y : ℝ^1 ↦ ‖y‖ ^ 4) := by
    funext y
    simp only [Pi.mul_apply]
    ring
  rw [hfun] at hfour
  exact hfour

/-- Every bounded measurable subset of the line admits a finite-energy
minimum of the quartic double-well functional in its supported smooth-core
closure. Only gradient convexity is needed; the value potential is nonconvex. -/
theorem exists_minimizer {Ω : Set (ℝ^1)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ u : W^{1,4}(Ω),
      u ∈ wkp0SubmoduleOn (n := 1) (k := 1) (p := 4) (Ω := Ω) ∧
      energy u ≠ ∞ ∧
      ∀ v : W^{1,4}(Ω),
        v ∈ wkp0SubmoduleOn (n := 1) (k := 1) (p := 4) (Ω := Ω) →
        energy u ≤ energy v := by
  have : Fact (0 < (1 : ℕ)) := ⟨by norm_num⟩
  have : IsFiniteMeasure (domainMeasure 1 Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let F (_ : ℝ^1) (z : ℝ × ℝ^1) : ℝ := (z.1 ^ 2 - 1) ^ 2 + ‖z.2‖ ^ 4
  let D (_ : ℝ^1) (z : ℝ × ℝ^1) : ℝ^1 := (4 * ‖z.2‖ ^ 2) • z.2
  have hF : Measurable (Function.uncurry F) := by
    apply Continuous.measurable
    dsimp [F, Function.uncurry]
    fun_prop
  have hD : Measurable (Function.uncurry D) := by
    apply Continuous.measurable
    dsimp [D, Function.uncurry]
    fun_prop
  have hconvex (s : ℝ) : ConvexOn ℝ univ (fun z : ℝ^1 ↦ F 0 (s, z)) := by
    have hnorm : ConvexOn ℝ univ (fun z : ℝ^1 ↦ ‖z‖ ^ 4) := by
      have hpow :=
        (convexOn_univ_norm : ConvexOn ℝ univ (norm : ℝ^1 → ℝ)).pow
          (fun z _ ↦ norm_nonneg z) 4
      have hfun : (norm : ℝ^1 → ℝ) ^ 4 = (fun z : ℝ^1 ↦ ‖z‖ ^ 4) := by
        funext z
        simp only [Pi.pow_apply]
      rw [hfun] at hpow
      exact hpow
    exact (convexOn_const ((s ^ 2 - 1) ^ 2) convex_univ).add hnorm
  have hfinite : energy (0 : W^{1,4}(Ω)) ≠ ∞ := by
    have heq : energy (0 : W^{1,4}(Ω)) =
        ∫⁻ _x : ℝ^1, (1 : ℝ≥0∞) ∂domainMeasure 1 Ω := by
      unfold energy
      simp only [map_zero]
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_zero ℝ 4 (domainMeasure 1 Ω),
        Lp.coeFn_zero (ℝ^1) 4 (domainMeasure 1 Ω)] with x hx hz
      change (0 : Lp ℝ 4 (domainMeasure 1 Ω)) x = 0 at hx
      change (0 : Lp (ℝ^1) 4 (domainMeasure 1 Ω)) x = 0 at hz
      rw [hx, hz]
      norm_num
    have hμ : (domainMeasure 1 Ω) univ ≠ ∞ :=
      measure_ne_top (domainMeasure 1 Ω) univ
    rw [heq, lintegral_const, one_mul]
    exact hμ
  have hfiniteAffine : (∫⁻ x, ENNReal.ofReal (F x
      (wkpBaseCoordinateCLM (n := 1) (m := 1) (p := 4) (Ω := Ω)
          ((0 : W^{1,4}(Ω)) + ((0 : W₀^{1,4}(Ω)) :
            W^{1,4}(Ω))) x,
        ∇ ((0 : W^{1,4}(Ω)) + ((0 : W₀^{1,4}(Ω)) :
            W^{1,4}(Ω))) x) + 0) ∂domainMeasure 1 Ω) ≠ ∞ := by
    simpa only [F, ZeroMemClass.coe_zero, add_zero, energy] using hfinite
  have : Fact (1 ≤ ((4 : NNReal) : ℝ≥0∞)) := ⟨by norm_num⟩
  have hexists := PDE.CalculusOfVariations.exists_minimizer_mixedWkpLIntegral_prescribed_boundary
    (n := 1) (p := (4 : NNReal)) (F := F) (D := D) (b := fun _ ↦ 0)
    hΩ hbounded (by norm_num)
  simp only [ENNReal.coe_ofNat] at hexists
  have hmin := hexists hF hD measurable_const
    (Filter.Eventually.of_forall fun _ z ↦ by dsimp [F]; fun_prop)
    (Filter.Eventually.of_forall fun _ z ↦ by dsimp [D]; fun_prop)
    (Filter.Eventually.of_forall fun _ s ↦ hconvex s)
    (Filter.Eventually.of_forall fun _ s z ↦ (hasFDerivAt_norm_four z).const_add
      ((s ^ 2 - 1) ^ 2))
    (c := 1) (by norm_num)
    (Filter.Eventually.of_forall fun _ s z ↦ by
      change 1 * ‖z‖ ^ (4 : ℝ) - 0 ≤ (s ^ 2 - 1) ^ 2 + ‖z‖ ^ 4
      rw [one_mul, sub_zero, Real.rpow_ofNat]
      exact le_add_of_nonneg_left (sq_nonneg (s ^ 2 - 1)))
    (0 : W^{1,4}(Ω)) (0 : W₀^{1,4}(Ω)) hfiniteAffine
  obtain ⟨u, hu, hufinite, humin⟩ := hmin
  refine ⟨u, ?_, ?_, ?_⟩
  · change u - (0 : W^{1,4}(Ω)) ∈
        wkp0SubmoduleOn (n := 1) (k := 1) (p := 4) (Ω := Ω) at hu
    rw [sub_zero] at hu
    exact hu
  · simp only [F, add_zero, energy] at hufinite ⊢
    exact hufinite
  · intro v hv
    have hvzero : v - (0 : W^{1,4}(Ω)) ∈
        wkp0SubmoduleOn (n := 1) (k := 1) (p := 4) (Ω := Ω) := by
      rw [sub_zero]
      exact hv
    have hvmin := humin v hvzero
    simp only [F, add_zero, energy] at hvmin ⊢
    exact hvmin

/-- On the closed unit interval, expressed as the closed unit ball in `ℝ¹`,
the same minimum exists without an open-domain or boundary-atlas hypothesis. -/
theorem exists_minimizer_closed_unit_interval :
    ∃ u : W^{1,4}(Metric.closedBall (0 : ℝ^1) 1),
      u ∈ wkp0SubmoduleOn (n := 1) (k := 1) (p := 4)
        (Ω := Metric.closedBall (0 : ℝ^1) 1) ∧
      energy u ≠ ∞ ∧
      ∀ v : W^{1,4}(Metric.closedBall (0 : ℝ^1) 1),
        v ∈ wkp0SubmoduleOn (n := 1) (k := 1) (p := 4)
          (Ω := Metric.closedBall (0 : ℝ^1) 1) →
        energy u ≤ energy v :=
  exists_minimizer measurableSet_closedBall Metric.isBounded_closedBall

end PDE.Examples.QuarticMixedEnergy

end
