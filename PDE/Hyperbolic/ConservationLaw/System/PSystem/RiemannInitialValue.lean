/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.InitialValue
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannSolution

/-!
# Initial trace of the local p-system Riemann solution

For globally `C²` stress with strictly positive first and second derivatives
on `ℝ`, the elementary two-wave construction solves the p-system on positive
time. For right states in the local strength chart,
it also attains the prescribed Riemann datum strongly in `L¹_loc(ℝ)`. The
mechanical-entropy conclusions additionally assume a globally `C¹` potential
whose derivative is the stress.

At each fixed `x ≠ 0`, every affine wave front converges to the origin as
`t ↓ 0`. The solution is therefore eventually equal to the left state for
`x < 0` and to the right state for `x > 0`. Measurability and uniform bounds
for the two elementary waves then give the local `L¹` trace by dominated
convergence.

The Riemann problem is (1)-(2) of Evans, §11.2, and Theorem 4 of §11.2.4 solves it locally by
elementary waves as an integral solution, which takes the initial condition in the weak sense of
(13) of §11.1.1; we prove the strong trace. The mechanical entropy pair is Example 2 of §11.4.2.

## Main results

* `elementaryRiemannSolution_tendsto_initial_of_ne_zero`: for `x ≠ 0` the
  two-wave solution converges pointwise to the Riemann datum as `t ↓ 0`.
* `elementaryRiemannSolution_hasInitialTraceLocallyL1`: the datum is attained
  strongly in `L¹_loc(ℝ)`.
* `isWeakSolutionWithInitialTrace_elementaryRiemannSolution`: for a right
  state in the target of the strength chart, the two-wave profile solves the
  Riemann problem in the interior-weak, strong-trace sense.
* `exists_local_mechanicalEntropySolutionWithInitialTrace`: every right state
  in an open neighborhood of `left` admits a mechanically entropy-admissible
  solution of the p-system Riemann problem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equation (13); §11.2, equations (1)-(2);
  §11.2.4, Theorem 4; §11.4.2, Example 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.Scalar
open PDE.Hyperbolic.ConservationLaw.System

private theorem eventually_mem_leftHalfSpace_of_neg {x : ℝ} (hx : x < 0) (speed : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (!₂[t, x] : ℝ^2) ∈ AffineInterface.leftHalfSpace speed := by
  have ht0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
  have hfront :
      Tendsto (fun t : ℝ ↦ speed * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht0
  filter_upwards [hfront.eventually (Ioi_mem_nhds hx)] with t ht using ht

private theorem eventually_not_mem_leftHalfSpace_of_pos {x : ℝ} (hx : 0 < x) (speed : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (!₂[t, x] : ℝ^2) ∉ AffineInterface.leftHalfSpace speed := by
  have ht0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
  have hfront :
      Tendsto (fun t : ℝ ↦ speed * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht0
  filter_upwards [hfront.eventually (Iio_mem_nhds hx)] with t ht hmem
  exact (not_lt_of_ge ht.le) hmem

private theorem elementaryWaveSolution_zero_eventuallyEq_left (stress : ℝ → ℝ) (left : ℝ^2)
    (strength : ℝ) {x : ℝ} (hx : x < 0) :
    (fun t : ℝ ↦ elementaryWaveSolution stress 0 left strength !₂[t, x]) =ᶠ[𝓝[>] 0] fun _ ↦
      left := by
  rcases le_or_gt strength 0 with hstrength | hpos
  · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength]
    exact (eventually_mem_leftHalfSpace_of_neg hx (rarefactionSpeed stress 0 (left 0))).mono
      fun _ ht ↦ AffineFan.profile_eq_left ht
  · rw [elementaryWaveSolution_zero_of_pos stress left hpos]
    exact (eventually_mem_leftHalfSpace_of_neg hx
      (shockSpeed stress 0 (left 0) (left 0 + strength))).mono
        fun _ ht ↦ planarShock_apply_of_mem ht

private theorem elementaryWaveSolution_one_eventuallyEq_right (stress : ℝ → ℝ) (left : ℝ^2)
    (strength : ℝ) {x : ℝ} (hx : 0 < x) :
    (fun t : ℝ ↦ elementaryWaveSolution stress 1 left strength !₂[t, x]) =ᶠ[𝓝[>] 0] fun _ ↦
      elementaryWaveState stress 1 strength left := by
  rcases lt_or_ge strength 0 with hstrength | hnonneg
  · rw [elementaryWaveSolution_one_of_neg stress left hstrength,
      elementaryWaveState_one_of_neg stress left hstrength]
    exact (eventually_not_mem_leftHalfSpace_of_pos hx
      (shockSpeed stress 1 (left 0) (left 0 + strength))).mono
        fun _ ht ↦ planarShock_apply_of_not_mem ht
  · rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg,
      elementaryWaveState_one_of_nonneg stress left hnonneg]
    filter_upwards [eventually_not_mem_leftHalfSpace_of_pos hx (rarefactionSpeed stress 1 (left 0)),
      eventually_not_mem_leftHalfSpace_of_pos hx (rarefactionSpeed stress 1 (left 0 + strength))]
      with t hleft hright using AffineFan.profile_eq_right hleft hright

/-- At each `x ≠ 0`, the elementary two-wave solution converges from positive
times to the corresponding Riemann state. -/
theorem elementaryRiemannSolution_tendsto_initial_of_ne_zero {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) {x : ℝ}
    (hx : x ≠ 0) :
    Tendsto (fun t : ℝ ↦ elementaryRiemannSolution hstress hpositive left right !₂[t, x]) (𝓝[>] 0)
      (𝓝 (riemannData left right x)) := by
  have htime : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  rcases lt_or_gt_of_ne hx with hxNeg | hxPos
  · rw [riemannData_of_neg left right hxNeg]
    refine tendsto_const_nhds.congr' (EventuallyEq.symm ?_)
    filter_upwards [htime, elementaryWaveSolution_zero_eventuallyEq_left stress left
      (elementaryRiemannStrength hstress hpositive left right 0) hxNeg] with t ht hwave
    rw [elementaryRiemannSolution_eq_zero_wave_of_neg_space hstress hpositive left right ht hxNeg]
    exact hwave
  · let middle := elementaryRiemannIntermediateState hstress hpositive left right
    let strength := elementaryRiemannStrength hstress hpositive left right 1
    have hendpoint : elementaryWaveState stress 1 strength middle = right := by
      simpa only [middle, strength] using
        elementaryWaveState_one_elementaryRiemannStrength hstress hpositive left hright
    rw [riemannData_of_nonneg left right hxPos.le]
    refine tendsto_const_nhds.congr' (EventuallyEq.symm ?_)
    filter_upwards [htime,
      elementaryWaveSolution_one_eventuallyEq_right stress middle strength hxPos] with t ht hwave
    rw [elementaryRiemannSolution_eq_one_wave_of_nonneg_space hstress hpositive left right ht
      hxPos.le]
    exact hwave.trans hendpoint

/-- The elementary p-system Riemann solution attains its step datum strongly
in local `L¹` as `t ↓ 0`. -/
theorem elementaryRiemannSolution_hasInitialTraceLocallyL1 {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) :
    HasInitialTraceLocallyL1 (elementaryRiemannSolution hstress hpositive left right)
      (riemannData left right) := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  let middle := elementaryRiemannIntermediateState hstress hpositive left right
  have hsolutionMeas : Measurable (elementaryRiemannSolution hstress hpositive left right) :=
    show Measurable (glueAtCommonState middle (elementaryWaveSolution stress 0 left (strength 0))
        (elementaryWaveSolution stress 1 middle (strength 1))) from
      ((measurable_elementaryWaveSolution hstress hpositive hsecond 0 left (strength 0)).add
        (measurable_elementaryWaveSolution hstress hpositive hsecond 1 middle (strength 1))).sub
        measurable_const
  obtain ⟨C₀, hC₀⟩ :=
    exists_norm_elementaryWaveSolution_le_of_pos_time hstress hpositive hsecond 0 left (strength 0)
  obtain ⟨C₁, hC₁⟩ := exists_norm_elementaryWaveSolution_le_of_pos_time
    hstress hpositive hsecond 1 middle (strength 1)
  apply PDE.Hyperbolic.ConservationLaw.Scalar.hasInitialTraceLocallyL1_of_dominated
  · exact locallyIntegrable_riemannData left right
  · exact fun a b ↦ .of_forall fun t ↦ ((hsolutionMeas.comp
      (by fun_prop : Measurable (fun x : ℝ ↦ (!₂[t, x] : ℝ^2)))).sub
        (measurable_riemannData left right)).aestronglyMeasurable
  · intro a b
    refine ⟨fun _ : ℝ ↦ C₀ + C₁ + ‖middle‖ + max ‖left‖ ‖right‖,
      integrableOn_const measure_Icc_lt_top.ne, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine .of_forall fun x ↦
      (norm_sub_le _ _).trans (add_le_add ?_ (norm_riemannData_le_max left right x))
    change ‖elementaryWaveSolution stress 0 left (strength 0) !₂[t, x] +
      elementaryWaveSolution stress 1 middle (strength 1) !₂[t, x] - middle‖ ≤ C₀ + C₁ + ‖middle‖
    exact (norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (hC₀ _ ht) (hC₁ _ ht))) le_rfl)
  · filter_upwards [(by rw [ae_iff]; simp : ∀ᵐ x : ℝ ∂volume, x ≠ 0)] with x hx
    exact elementaryRiemannSolution_tendsto_initial_of_ne_zero hstress hpositive left hright hx

/-- The selected elementary profile solves the p-system Riemann initial-value
problem in the interior-weak, strong-trace sense. -/
theorem isWeakSolutionWithInitialTrace_elementaryRiemannSolution {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) :
    IsWeakSolutionWithInitialTrace (flux stress) (riemannData left right)
      (elementaryRiemannSolution hstress hpositive left right) :=
  ⟨isWeakSolution_elementaryRiemannSolution hstress hpositive hsecond left right,
    elementaryRiemannSolution_hasInitialTraceLocallyL1 hstress hpositive hsecond left hright⟩

/-- There is a positive radius on which every nearby right state is joined
to `left` by the explicit mechanically entropy-admissible Riemann solution
with strong local `L¹` initial trace. -/
theorem exists_pos_radius_mechanicalEntropySolutionWithInitialTrace
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) :
    ∃ ε > 0, ∀ right : ℝ^2, dist right left < ε →
      IsWeakSolutionWithInitialTrace
          (flux stress) (riemannData left right)
          (elementaryRiemannSolution hstress hpositive left right) ∧
        SatisfiesEntropyInequalityFor forwardHalfSpace
          (elementaryRiemannSolution hstress hpositive left right)
          (mechanicalEntropyPair stress potential
            (hstress.of_le (by norm_num)) hpotential hderiv) := by
  let e := elementaryRiemannHomeomorph hstress hpositive left
  have hleft : left ∈ e.target := by
    simpa only [e] using left_mem_elementaryRiemannHomeomorph_target hstress hpositive left
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target left hleft
  refine ⟨ε, hε, fun right hright ↦ ?_⟩
  have hrightTarget : right ∈ e.target := hball (Metric.mem_ball.mpr hright)
  exact ⟨isWeakSolutionWithInitialTrace_elementaryRiemannSolution
        hstress hpositive hsecond left hrightTarget,
      satisfiesEntropyInequalityFor_elementaryRiemannSolution
        hstress hpotential hderiv hpositive hsecond left right⟩

/-- Every Riemann datum sufficiently close to `left` admits a mechanically
entropy-admissible p-system solution with a strong local `L¹` initial trace.

The stress is globally `C²` with strictly positive first and second
derivatives, and a globally `C¹` potential with derivative equal to the stress
is supplied. The witness is the explicit elementary two-wave solution. Local
existence refers to the right state being near `left`; the weak equation holds
on all positive times. The conclusion is the mechanical-entropy inequality.
-/
theorem exists_local_mechanicalEntropySolutionWithInitialTrace
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) :
    ∃ target : Set (ℝ^2),
      IsOpen target ∧
        left ∈ target ∧
          ∀ right ∈ target,
            ∃ u : ℝ^2 → ℝ^2,
              IsWeakSolutionWithInitialTrace
                  (flux stress) (riemannData left right) u ∧
                SatisfiesEntropyInequalityFor forwardHalfSpace u
                  (mechanicalEntropyPair stress potential
                    (hstress.of_le (by norm_num)) hpotential hderiv) := by
  let e := elementaryRiemannHomeomorph hstress hpositive left
  refine ⟨e.target, e.open_target, ?_, ?_⟩
  · simpa only [e] using left_mem_elementaryRiemannHomeomorph_target hstress hpositive left
  · intro right hright
    refine ⟨elementaryRiemannSolution hstress hpositive left right, ?_⟩
    exact ⟨isWeakSolutionWithInitialTrace_elementaryRiemannSolution
          hstress hpositive hsecond left hright,
        satisfiesEntropyInequalityFor_elementaryRiemannSolution
          hstress hpotential hderiv hpositive hsecond left right⟩

end PDE.Hyperbolic.ConservationLaw.System.PSystem
