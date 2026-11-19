/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Parametric interval integrals

Local Leibniz rules for interval integrals whose integrand and right endpoint vary together:

  `d/dq ∫_a^{g q} H q s ds = (H q (g q)) · g' q + ∫_a^{g q} ∂_q H q s ds`.

The fixed-interval derivative is discharged by Mathlib's dominated parametric integral theorem
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`; joint continuity of `H`
controls the mixed term `∫_{g p}^{g q} (H q s - H p s) ds`, which is `o(‖q - p‖)` because the
interval shrinks and the integrand is uniformly small near `(p, g p)`. The rules are used to
differentiate Duhamel-type integrals `∫_0^t K(t, s) ds` in which the time variable appears both
as the endpoint and inside the integrand.

## Main results

* `hasFDerivAt_intervalIntegral_moving_right`: the abstract Leibniz rule, taking the
  fixed-interval derivative as a hypothesis.
* `hasFDerivAt_intervalIntegral_moving_right_of_continuous_of_eventually_bound`: the rule
  for a differentiable endpoint given a local bound on the parameter derivative.
* `hasFDerivAt_intervalIntegral_moving_right_fst_of_continuous`: in finite dimensions the bound
  follows from continuity of the parameter derivative on a compact neighbourhood.

This is the classical Leibniz integral rule; the fixed-endpoint case is differentiation under
the integral sign.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley,
  1999.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory
open scoped Interval Topology

/-- A local Leibniz rule for an interval integral whose integrand and right endpoint vary.

The derivative is the sum of the fixed-interval derivative and the endpoint derivative. -/
theorem hasFDerivAt_intervalIntegral_moving_right
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : X → ℝ → E) (a : ℝ) (g : X → ℝ) (p : X)
    {g' : X →L[ℝ] ℝ} {D : X →L[ℝ] E}
    (hg : HasFDerivAt g g' p)
    (hfixed : HasFDerivAt (fun q ↦ ∫ s in a..g p, H q s) D p)
    (hcorner : ContinuousAt (fun qs : X × ℝ ↦ H qs.1 qs.2) (p, g p))
    (hcorner_meas : StronglyMeasurableAtFilter (H p) (𝓝 (g p)) volume)
    (hint : ∀ᶠ q in 𝓝 p,
      IntervalIntegrable (H q) volume a (g p) ∧
        IntervalIntegrable (H q) volume (g p) (g q) ∧
        IntervalIntegrable (H p) volume (g p) (g q)) :
    HasFDerivAt (fun q ↦ ∫ s in a..g q, H q s)
      (g'.smulRight (H p (g p)) + D) p := by
  let R : X → E := fun q ↦ ∫ s in g p..g q, H q s - H p s
  have hHp : ContinuousAt (H p) (g p) := hcorner.comp (continuousAt_const.prodMk continuousAt_id)
  have hendpoint : HasFDerivAt (fun q ↦ ∫ s in g p..g q, H p s) (g'.smulRight (H p (g p))) p :=
    ((intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl (f := H p))
      hcorner_meas hHp).hasFDerivAt.comp p hg).congr_fderiv (by ext; simp)
  -- near `(p, g p)` the integrand of `R` is uniformly small
  have hcorner_bound : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ q in 𝓝 p, ∀ s ∈ Ι (g p) (g q), ‖H q s - H p s‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcorner (ε / 2) (half_pos hε)
    filter_upwards [Metric.ball_mem_nhds p hδ,
      hg.continuousAt (Metric.ball_mem_nhds (g p) hδ)] with q hq hgq s hs
    have hs : dist s (g p) < δ := lt_of_le_of_lt (by
      simpa [dist_comm] using Real.dist_left_le_of_mem_uIcc (Set.uIoc_subset_uIcc hs))
      (Metric.mem_ball.1 hgq)
    have h₁ := hclose (show dist (q, s) (p, g p) < δ by
      simpa [Prod.dist_eq] using ⟨Metric.mem_ball.1 hq, hs⟩)
    have h₂ := hclose (show dist (p, s) (p, g p) < δ by simpa [Prod.dist_eq] using hs)
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (H q s) (H p s) (H p (g p))]
  have hR_littleO : R =o[𝓝 p] fun q ↦ q - p := by
    refine (Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_ :
      R =o[𝓝 p] fun q ↦ g q - g p).trans_isBigO hg.isBigO_sub
    filter_upwards [hcorner_bound ε hε] with q hq
    simpa [R, Real.norm_eq_abs, mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s ↦ H q s - H p s) hq
  have hR0 : R p = 0 := by simp [R]
  have hR : HasFDerivAt R (0 : X →L[ℝ] E) p := .of_isLittleO (by simpa [hR0] using hR_littleO)
  -- split `∫_a^{g q} H q = ∫_a^{g p} H q + ∫_{g p}^{g q} H p + R q`
  have hsum := hfixed.add (hendpoint.add hR)
  rw [add_zero, add_comm D] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hint] with q hq
  simp only [R, Pi.add_apply, intervalIntegral.integral_sub hq.2.1 hq.2.2,
    ← intervalIntegral.integral_add_adjacent_intervals hq.1 hq.2.1]
  abel

/-- A continuous Banach-valued parameter derivative and a local bound give the
moving-endpoint derivative for an arbitrary differentiable endpoint. -/
theorem hasFDerivAt_intervalIntegral_moving_right_of_continuous_of_eventually_bound
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : X → ℝ → E) (F' : X → ℝ → X →L[ℝ] E)
    (a : ℝ) (g : X → ℝ) {g' : X →L[ℝ] ℝ}
    (hH : Continuous fun qs : X × ℝ ↦ H qs.1 qs.2)
    (hF' : Continuous fun qs : X × ℝ ↦ F' qs.1 qs.2)
    (hderiv : ∀ q s, HasFDerivAt (fun y ↦ H y s) (F' q s) q)
    (C : ℝ) (p : X) (hg : HasFDerivAt g g' p)
    (hbound : ∀ᶠ q in 𝓝 p, ∀ s ∈ Ι a (g p), ‖F' q s‖ ≤ C) :
    HasFDerivAt (fun q ↦ ∫ s in a..g q, H q s)
      (g'.smulRight (H p (g p)) + ∫ s in a..g p, F' p s) p := by
  have hH_slice (q : X) : Continuous (H q) := hH.comp (continuous_const.prodMk continuous_id)
  have hF'_slice (q : X) : Continuous (F' q) := hF'.comp (continuous_const.prodMk continuous_id)
  have hfixed : HasFDerivAt (fun q ↦ ∫ s in a..g p, H q s) (∫ s in a..g p, F' p s) p :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ C) hbound
      (.of_forall fun q ↦ (hH_slice q).aestronglyMeasurable.restrict)
      ((hH_slice p).intervalIntegrable a (g p)) (hF'_slice p).aestronglyMeasurable.restrict
      (.of_forall fun s hs q hq ↦ hq s hs) (continuous_const.intervalIntegrable a (g p))
      (.of_forall fun s _ q _ ↦ hderiv q s)
  exact hasFDerivAt_intervalIntegral_moving_right H a g p hg hfixed hH.continuousAt
    (hH_slice p).aestronglyMeasurable.stronglyMeasurableAtFilter (.of_forall fun q ↦
      ⟨(hH_slice q).intervalIntegrable a (g p), (hH_slice q).intervalIntegrable (g p) (g q),
        (hH_slice p).intervalIntegrable (g p) (g q)⟩)

/-- Finite-dimensional parameter neighborhoods supply the derivative bound for
Banach-valued integrands and arbitrary differentiable moving endpoints. -/
theorem hasFDerivAt_intervalIntegral_moving_right_of_continuous
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : X → ℝ → E) (F' : X → ℝ → X →L[ℝ] E)
    (a : ℝ) (g : X → ℝ) {g' : X →L[ℝ] ℝ}
    (hH : Continuous fun qs : X × ℝ ↦ H qs.1 qs.2)
    (hF' : Continuous fun qs : X × ℝ ↦ F' qs.1 qs.2)
    (hderiv : ∀ q s, HasFDerivAt (fun y ↦ H y s) (F' q s) q)
    (p : X) (hg : HasFDerivAt g g' p) :
    HasFDerivAt (fun q ↦ ∫ s in a..g q, H q s)
      (g'.smulRight (H p (g p)) + ∫ s in a..g p, F' p s) p := by
  have hK : IsCompact (Metric.closedBall p 1 ×ˢ Set.uIcc a (g p)) :=
    (isCompact_closedBall p 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuousOn
  apply hasFDerivAt_intervalIntegral_moving_right_of_continuous_of_eventually_bound
    H F' a g hH hF' hderiv C p hg
  filter_upwards [Metric.ball_mem_nhds p zero_lt_one] with q hq
  intro s hs
  exact hC (q, s) ⟨Metric.ball_subset_closedBall hq, Set.uIoc_subset_uIcc hs⟩

/-- In finite dimensions, continuity of the parameter derivative supplies the local bound needed
for the moving-endpoint derivative. -/
theorem hasFDerivAt_intervalIntegral_moving_right_fst_of_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : (ℝ × V) → ℝ → ℝ)
    (F' : (ℝ × V) → ℝ → (ℝ × V) →L[ℝ] ℝ)
    (hH : Continuous fun qs : (ℝ × V) × ℝ ↦ H qs.1 qs.2)
    (hF' : Continuous fun qs : (ℝ × V) × ℝ ↦ F' qs.1 qs.2)
    (hderiv : ∀ q s, HasFDerivAt (fun y ↦ H y s) (F' q s) q)
    (p : ℝ × V) :
    HasFDerivAt (fun q ↦ ∫ s in (0 : ℝ)..q.1, H q s)
      ((H p p.1) • ContinuousLinearMap.fst ℝ ℝ V +
        ∫ s in (0 : ℝ)..p.1, F' p s) p := by
  have hmap :
      (ContinuousLinearMap.fst ℝ ℝ V).smulRight (H p p.1) =
        (H p p.1) • ContinuousLinearMap.fst ℝ ℝ V := by
    apply ContinuousLinearMap.ext
    intro q
    simp [mul_comm]
  rw [← hmap]
  exact hasFDerivAt_intervalIntegral_moving_right_of_continuous
    H F' 0 Prod.fst hH hF' hderiv p (ContinuousLinearMap.fst ℝ ℝ V).hasFDerivAt

end PDE.Analysis
