/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PSystem.ElementaryWave
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.Rarefaction.Fan
public import PDE.Hyperbolic.ConservationLaw.System.WeakGluing
import PDE.Analysis.Scalar.DividedDifference
import PDE.Hyperbolic.ConservationLaw.System.EntropyGluing

/-!
# Local Riemann solutions for the one-dimensional p-system

We build positive-time weak p-system profiles for globally `C²`
stress with strictly positive first and second derivatives on `ℝ`. The
mechanical-entropy statements also assume a globally `C¹` potential whose
derivative is the stress. Each physical elementary wave is represented by its
positive-time weak solution:

* family zero uses a rarefaction for nonpositive strength and a shock for
  positive strength;
* family one uses a shock for negative strength and a rarefaction for
  nonnegative strength.

Family-zero waves have negative propagation speeds, while family-one waves
have positive propagation speeds. At every positive-time point, at least one
profile equals the intermediate state: the family-zero profile is already at
its right endpoint on `x ≥ 0`, and the family-one profile is still at its left
endpoint on `x < 0`.

The two-wave solution is assembled by inclusion-exclusion,

`u₀ + u₁ - intermediate`.

The gluing theorems then prove the nonlinear conservation law and the
mechanical-entropy inequality from the corresponding one-wave statements.

This is the p-system case of Theorem 4 of Evans, §11.2.4. Evans joins the waves by noting that
they lie in disjoint sectors; we glue the profiles by inclusion-exclusion. The entropy inequality
is (29) of §11.4.2 for the pair of Example 2 there.

## Main results

* `elementaryWaveSolution`: the profile (planar shock or rarefaction fan)
  realizing one physical wave of family `k`.
* `isWeakSolution_elementaryWaveSolution`,
  `satisfiesEntropyInequalityFor_elementaryWaveSolution`: each one-wave
  profile is a weak solution satisfying the mechanical-entropy inequality.
* `elementaryRiemannSolution`: the two-wave profile for a left state and a
  right state, with strengths taken from the local chart
  `elementaryRiemannHomeomorph`.
* `isWeakSolution_elementaryRiemannSolution`,
  `satisfiesEntropyInequalityFor_elementaryRiemannSolution`: the two-wave
  profile is a weak solution of the p-system on `t > 0` and dissipates the
  mechanical entropy.

The initial trace, and hence the statement that this profile solves the
Riemann initial-value problem, is proved in `PSystem.RiemannInitialValue`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, Theorem 4 and its proof; §11.4.2, equations
  (28)-(29) and Example 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.System

private theorem not_mem_leftHalfSpace_of_nonneg_space_of_speed_neg {speed : ℝ} {p : ℝ^2}
    (hspace : 0 ≤ p 1) (htime : 0 < p 0) (hspeed : speed < 0) :
    p ∉ AffineInterface.leftHalfSpace speed :=
  fun hp ↦ (not_lt_of_ge hspace) <| hp.trans (mul_neg_of_neg_of_pos hspeed htime)

private theorem mem_leftHalfSpace_of_neg_space_of_speed_pos {speed : ℝ} {p : ℝ^2} (hspace : p 1 < 0)
    (htime : 0 < p 0) (hspeed : 0 < speed) :
    p ∈ AffineInterface.leftHalfSpace speed :=
  hspace.trans (mul_pos hspeed htime)

/-! ## One-wave solutions -/

/-- Global positive-time profile of one physical elementary wave. -/
def elementaryWaveSolution
    (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2)
    (strength : ℝ) : ℝ^2 → ℝ^2 :=
  if k = 0 then if strength ≤ 0 then rarefactionFan stress 0 left strength else planarShock left
        (shockState stress 0 left (left 0 + strength))
        (shockSpeed stress 0 (left 0) (left 0 + strength))
  else if strength < 0 then planarShock left (shockState stress 1 left (left 0 + strength))
        (shockSpeed stress 1 (left 0) (left 0 + strength))
    else rarefactionFan stress 1 left strength

/-- A nonpositive family-zero wave is represented by its rarefaction fan. -/
theorem elementaryWaveSolution_zero_of_nonpos (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : strength ≤ 0) :
    elementaryWaveSolution stress 0 left strength = rarefactionFan stress 0 left strength := by
  simp [elementaryWaveSolution, hstrength]

/-- A positive family-zero wave is represented by its planar shock. -/
theorem elementaryWaveSolution_zero_of_pos (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : 0 < strength) :
    elementaryWaveSolution stress 0 left strength = planarShock left
      (shockState stress 0 left (left 0 + strength))
      (shockSpeed stress 0 (left 0) (left 0 + strength)) := by
  simp [elementaryWaveSolution, not_le_of_gt hstrength]

/-- A negative family-one wave is represented by its planar shock. -/
theorem elementaryWaveSolution_one_of_neg (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : strength < 0) :
    elementaryWaveSolution stress 1 left strength = planarShock left
      (shockState stress 1 left (left 0 + strength))
      (shockSpeed stress 1 (left 0) (left 0 + strength)) := by
  simp [elementaryWaveSolution, hstrength]

/-- A nonnegative family-one wave is represented by its rarefaction fan. -/
theorem elementaryWaveSolution_one_of_nonneg (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : 0 ≤ strength) :
    elementaryWaveSolution stress 1 left strength = rarefactionFan stress 1 left strength := by
  simp [elementaryWaveSolution, not_lt_of_ge hstrength]

/-- Every physical elementary-wave profile is invariant under positive
spacetime dilation. -/
theorem elementaryWaveSolution_smul_of_pos {stress : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ) (p : ℝ^2) :
    elementaryWaveSolution stress k left strength (a • p) =
      elementaryWaveSolution stress k left strength p := by
  by_cases hk : k = 0
  · subst k
    by_cases hstrength : strength ≤ 0
    · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength]
      exact rarefactionFan_smul_of_pos ha 0 left strength p
    · have hpos : 0 < strength := lt_of_not_ge hstrength
      rw [elementaryWaveSolution_zero_of_pos stress left hpos]
      exact planarShock_smul_of_pos ha _ _ _ p
  · have hk : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    by_cases hstrength : strength < 0
    · rw [elementaryWaveSolution_one_of_neg stress left hstrength]
      exact planarShock_smul_of_pos ha _ _ _ p
    · have hnonneg : 0 ≤ strength := le_of_not_gt hstrength
      rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg]
      exact rarefactionFan_smul_of_pos ha 1 left strength p

/-- Every physical elementary-wave profile is a weak solution on positive
time. -/
theorem isWeakSolution_elementaryWaveSolution {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ) :
    IsWeakSolution (flux stress) forwardHalfSpace
      (elementaryWaveSolution stress k left strength) := by
  by_cases hk : k = 0
  · subst k
    by_cases hstrength : strength ≤ 0
    · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength]
      exact isWeakSolution_rarefactionFan_zero_of_nonpos hstress hpositive hsecond left hstrength
    · have hpos : 0 < strength := lt_of_not_ge hstrength
      rw [elementaryWaveSolution_zero_of_pos stress left hpos]
      have hslope : 0 < dslope stress (left 0) (left 0 + strength) :=
        PDE.Analysis.Scalar.dslope_pos_of_deriv_pos hpositive _ _
      exact (isWeakSolution_planarShock_shockState (stress := stress) 0 left (left 0 + strength)
          hslope.le).mono_domain le_top
  · have hk : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    by_cases hstrength : strength < 0
    · rw [elementaryWaveSolution_one_of_neg stress left hstrength]
      have hslope : 0 < dslope stress (left 0) (left 0 + strength) :=
        PDE.Analysis.Scalar.dslope_pos_of_deriv_pos hpositive _ _
      exact (isWeakSolution_planarShock_shockState (stress := stress) 1 left (left 0 + strength)
          hslope.le).mono_domain le_top
    · have hnonneg : 0 ≤ strength := le_of_not_gt hstrength
      rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg]
      exact isWeakSolution_rarefactionFan_one_of_nonneg hstress hpositive hsecond left hnonneg

/-- Every physical elementary wave satisfies the mechanical-entropy
inequality on positive time. Rarefaction waves have zero entropy production,
while shock waves have strictly negative production at their interface. -/
theorem satisfiesEntropyInequalityFor_elementaryWaveSolution
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (k : Fin 2) (left : ℝ^2) (strength : ℝ) :
    SatisfiesEntropyInequalityFor forwardHalfSpace
      (elementaryWaveSolution stress k left strength)
      (mechanicalEntropyPair stress potential
        (hstress.of_le (by norm_num)) hpotential hderiv) := by
  by_cases hk : k = 0
  · subst k
    by_cases hstrength : strength ≤ 0
    · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength]
      exact satisfiesEntropyInequalityFor_rarefactionFan_zero_of_nonpos hstress hpositive hsecond
        (mechanicalEntropyPair stress potential (hstress.of_le (by norm_num)) hpotential hderiv)
        left hstrength
    · have hpos : 0 < strength := lt_of_not_ge hstrength
      rw [elementaryWaveSolution_zero_of_pos stress left hpos]
      apply (satisfiesEntropyInequalityFor_planarShock_shockState_zero_of_left_lt_right
          hstress hpotential hderiv hpositive hsecond left
          (show left 0 < left 0 + strength by linarith)).mono_domain
      exact le_top
  · have hk : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    by_cases hstrength : strength < 0
    · rw [elementaryWaveSolution_one_of_neg stress left hstrength]
      apply (satisfiesEntropyInequalityFor_planarShock_shockState_one_of_right_lt_left
          hstress hpotential hderiv hpositive hsecond left
          (show left 0 + strength < left 0 by linarith)).mono_domain
      exact le_top
    · have hnonneg : 0 ≤ strength := le_of_not_gt hstrength
      rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg]
      exact satisfiesEntropyInequalityFor_rarefactionFan_one_of_nonneg hstress hpositive hsecond
        (mechanicalEntropyPair stress potential (hstress.of_le (by norm_num)) hpotential hderiv)
        left hnonneg

/-- Every physical elementary-wave profile is measurable. -/
theorem measurable_elementaryWaveSolution {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ) :
    Measurable (elementaryWaveSolution stress k left strength) := by
  by_cases hk : k = 0
  · subst k
    by_cases hstrength : strength ≤ 0
    · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength]
      exact measurable_rarefactionFan hstress hpositive hsecond 0 left strength
        (rarefactionSpeed_zero_le_of_nonpos hstress hpositive hsecond left hstrength)
    · rw [elementaryWaveSolution_zero_of_pos stress left (lt_of_not_ge hstrength)]
      exact measurable_planarShock _ _ _
  · have hk : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    by_cases hstrength : strength < 0
    · rw [elementaryWaveSolution_one_of_neg stress left hstrength]
      exact measurable_planarShock _ _ _
    · have hnonneg : 0 ≤ strength := le_of_not_gt hstrength
      rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg]
      exact measurable_rarefactionFan hstress hpositive hsecond 1 left strength
        (rarefactionSpeed_one_le_of_nonneg hstress hpositive hsecond left hnonneg)

/-- On positive time, every physical elementary wave has a uniform norm
bound. -/
theorem exists_norm_elementaryWaveSolution_le_of_pos_time {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2) (left : ℝ^2) (strength : ℝ) :
    ∃ C : ℝ, ∀ p : ℝ^2, 0 < p 0 → ‖elementaryWaveSolution stress k left strength p‖ ≤ C := by
  by_cases hk : k = 0
  · subst k
    by_cases hstrength : strength ≤ 0
    · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength]
      exact exists_norm_rarefactionFan_le_of_pos_time hstress hpositive hsecond 0 left strength
    · have hpos : 0 < strength := lt_of_not_ge hstrength
      rw [elementaryWaveSolution_zero_of_pos stress left hpos]
      refine ⟨max ‖left‖ ‖shockState stress 0 left (left 0 + strength)‖, fun p _ ↦ ?_⟩
      exact norm_planarShock_le_max _ _ _ p
  · have hk : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    by_cases hstrength : strength < 0
    · rw [elementaryWaveSolution_one_of_neg stress left hstrength]
      refine ⟨max ‖left‖ ‖shockState stress 1 left (left 0 + strength)‖, fun p _ ↦ ?_⟩
      exact norm_planarShock_le_max _ _ _ p
    · have hnonneg : 0 ≤ strength := le_of_not_gt hstrength
      rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg]
      exact exists_norm_rarefactionFan_le_of_pos_time hstress hpositive hsecond 1 left strength

/-- On nonnegative space, a family-zero wave has reached its right endpoint. -/
theorem elementaryWaveSolution_zero_eq_right_of_nonneg_space {stress : ℝ → ℝ}
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) (strength : ℝ) {p : ℝ^2} (htime : 0 < p 0)
    (hspace : 0 ≤ p 1) :
    elementaryWaveSolution stress 0 left strength p =
      elementaryWaveState stress 0 strength left := by
  by_cases hstrength : strength ≤ 0
  · rw [elementaryWaveSolution_zero_of_nonpos stress left hstrength,
      elementaryWaveState_zero_of_nonpos stress left hstrength]
    apply AffineFan.profile_eq_right
    · apply not_mem_leftHalfSpace_of_nonneg_space_of_speed_neg hspace htime
      rw [rarefactionSpeed_zero]
      exact neg_neg_of_pos <| soundSpeed_pos (hpositive (left 0))
    · apply not_mem_leftHalfSpace_of_nonneg_space_of_speed_neg hspace htime
      rw [rarefactionSpeed_zero]
      exact neg_neg_of_pos <| soundSpeed_pos (hpositive (left 0 + strength))
  · have hpos : 0 < strength := lt_of_not_ge hstrength
    rw [elementaryWaveSolution_zero_of_pos stress left hpos,
      elementaryWaveState_zero_of_pos stress left hpos]
    apply planarShock_apply_of_not_mem
    apply not_mem_leftHalfSpace_of_nonneg_space_of_speed_neg hspace htime
    rw [shockSpeed_zero]
    exact neg_neg_of_pos <| Real.sqrt_pos.2 <|
      PDE.Analysis.Scalar.dslope_pos_of_deriv_pos hpositive _ _

/-- On negative space, a family-one wave is still at its left endpoint. -/
theorem elementaryWaveSolution_one_eq_left_of_neg_space {stress : ℝ → ℝ}
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) (strength : ℝ) {p : ℝ^2} (htime : 0 < p 0)
    (hspace : p 1 < 0) :
    elementaryWaveSolution stress 1 left strength p = left := by
  by_cases hstrength : strength < 0
  · rw [elementaryWaveSolution_one_of_neg stress left hstrength]
    apply planarShock_apply_of_mem
    apply mem_leftHalfSpace_of_neg_space_of_speed_pos hspace htime
    rw [shockSpeed_one]
    exact Real.sqrt_pos.2 <| PDE.Analysis.Scalar.dslope_pos_of_deriv_pos hpositive _ _
  · have hnonneg : 0 ≤ strength := le_of_not_gt hstrength
    rw [elementaryWaveSolution_one_of_nonneg stress left hnonneg]
    apply AffineFan.profile_eq_left
    apply mem_leftHalfSpace_of_neg_space_of_speed_pos hspace htime
    rw [rarefactionSpeed_one]
    exact soundSpeed_pos (hpositive (left 0))

/-- Two physical waves from consecutive families meet at their common state
at every positive-time point, provided the family-zero endpoint is that
state. This is the pointwise compatibility needed by both gluing theorems. -/
theorem elementaryWaveSolutions_meet_at_common_state {stress : ℝ → ℝ}
    (hpositive : ∀ v, 0 < deriv stress v) (left common : ℝ^2) (zeroStrength oneStrength : ℝ)
    (hcommon : elementaryWaveState stress 0 zeroStrength left = common) (p : ℝ^2)
    (htime : 0 < p 0) :
    elementaryWaveSolution stress 0 left zeroStrength p = common ∨
      elementaryWaveSolution stress 1 common oneStrength p = common := by
  by_cases hspace : 0 ≤ p 1
  · left
    rw [elementaryWaveSolution_zero_eq_right_of_nonneg_space
      hpositive left zeroStrength htime hspace]
    exact hcommon
  · right
    exact elementaryWaveSolution_one_eq_left_of_neg_space
      hpositive common oneStrength htime (lt_of_not_ge hspace)

/-! ## Two-wave Riemann solution -/

/-- The selected second elementary wave reaches the prescribed nearby right
state. -/
theorem elementaryWaveState_one_elementaryRiemannStrength {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) :
    elementaryWaveState stress 1 (elementaryRiemannStrength hstress hpositive left right 1)
      (elementaryRiemannIntermediateState hstress hpositive left right) = right := by
  simpa only [elementaryRiemannIntermediateState, elementaryWaveMap] using
    elementaryWaveMap_elementaryRiemannStrength hstress hpositive left hright

/-- The local self-similar p-system Riemann solution selected by the
elementary-wave coordinates.

Outside the target neighborhood, the strengths use the totalized inverse of
`elementaryRiemannHomeomorph`; the final theorem therefore keeps the
target-membership hypothesis explicit.
-/
def elementaryRiemannSolution
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (left right : ℝ^2) : ℝ^2 → ℝ^2 :=
  let strength :=
    elementaryRiemannStrength hstress hpositive left right
  let middle :=
    elementaryRiemannIntermediateState hstress hpositive left right
  glueAtCommonState middle (elementaryWaveSolution stress 0 left (strength 0))
    (elementaryWaveSolution stress 1 middle (strength 1))

/-- The selected two-wave p-system Riemann solution is invariant under
positive spacetime dilation. -/
theorem elementaryRiemannSolution_smul_of_pos {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) {a : ℝ} (ha : 0 < a) (left right : ℝ^2) (p : ℝ^2) :
    elementaryRiemannSolution hstress hpositive left right (a • p) =
      elementaryRiemannSolution hstress hpositive left right p := by
  simp only [elementaryRiemannSolution, glueAtCommonState]
  rw [elementaryWaveSolution_smul_of_pos ha, elementaryWaveSolution_smul_of_pos ha]

/-- On negative space, the two-wave solution agrees with its family-zero
wave. -/
theorem elementaryRiemannSolution_eq_zero_wave_of_neg_space {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (left right : ℝ^2)
    {p : ℝ^2} (htime : 0 < p 0) (hspace : p 1 < 0) :
    elementaryRiemannSolution hstress hpositive left right p = elementaryWaveSolution stress 0 left
      (elementaryRiemannStrength hstress hpositive left right 0) p := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  let middle := elementaryRiemannIntermediateState hstress hpositive left right
  change glueAtCommonState middle (elementaryWaveSolution stress 0 left (strength 0))
        (elementaryWaveSolution stress 1 middle (strength 1)) p =
      elementaryWaveSolution stress 0 left (strength 0) p
  unfold glueAtCommonState
  rw [elementaryWaveSolution_one_eq_left_of_neg_space hpositive middle (strength 1) htime hspace]
  simp

/-- On nonnegative space, the two-wave solution agrees with its family-one
wave. -/
theorem elementaryRiemannSolution_eq_one_wave_of_nonneg_space {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (left right : ℝ^2)
    {p : ℝ^2} (htime : 0 < p 0) (hspace : 0 ≤ p 1) :
    elementaryRiemannSolution hstress hpositive left right p =
      elementaryWaveSolution stress 1 (elementaryRiemannIntermediateState hstress hpositive left
      right) (elementaryRiemannStrength hstress hpositive left right 1) p := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  let middle := elementaryRiemannIntermediateState hstress hpositive left right
  change glueAtCommonState middle (elementaryWaveSolution stress 0 left (strength 0))
        (elementaryWaveSolution stress 1 middle (strength 1)) p =
      elementaryWaveSolution stress 1 middle (strength 1) p
  unfold glueAtCommonState
  rw [elementaryWaveSolution_zero_eq_right_of_nonneg_space hpositive left (strength 0) htime hspace]
  change middle + elementaryWaveSolution stress 1 middle (strength 1) p - middle =
      elementaryWaveSolution stress 1 middle (strength 1) p
  abel

/-- The selected two-wave profile is a weak p-system solution on positive
time. -/
theorem isWeakSolution_elementaryRiemannSolution {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left right : ℝ^2) :
    IsWeakSolution (flux stress) forwardHalfSpace
      (elementaryRiemannSolution hstress hpositive left right) := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  let middle := elementaryRiemannIntermediateState hstress hpositive left right
  let zeroWave := elementaryWaveSolution stress 0 left (strength 0)
  let oneWave := elementaryWaveSolution stress 1 middle (strength 1)
  have hzero : IsWeakSolution (flux stress) forwardHalfSpace zeroWave :=
    isWeakSolution_elementaryWaveSolution hstress hpositive hsecond 0 left (strength 0)
  have hone : IsWeakSolution (flux stress) forwardHalfSpace oneWave :=
    isWeakSolution_elementaryWaveSolution hstress hpositive hsecond 1 middle (strength 1)
  change IsWeakSolution (flux stress) forwardHalfSpace (glueAtCommonState middle zeroWave oneWave)
  exact hzero.glue_at_common_state hone fun p hp ↦ elementaryWaveSolutions_meet_at_common_state
    hpositive left middle (strength 0) (strength 1) (by rfl) p hp

/-- The selected two-wave Riemann solution satisfies the mechanical-entropy
inequality on positive time. -/
theorem satisfiesEntropyInequalityFor_elementaryRiemannSolution
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left right : ℝ^2) :
    SatisfiesEntropyInequalityFor forwardHalfSpace
      (elementaryRiemannSolution hstress hpositive left right)
      (mechanicalEntropyPair stress potential
        (hstress.of_le (by norm_num)) hpotential hderiv) := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  let middle := elementaryRiemannIntermediateState hstress hpositive left right
  let zeroWave := elementaryWaveSolution stress 0 left (strength 0)
  let oneWave := elementaryWaveSolution stress 1 middle (strength 1)
  let mechanicalPair : EntropyPair (flux stress) :=
    mechanicalEntropyPair stress potential (hstress.of_le (by norm_num)) hpotential hderiv
  have hzero : SatisfiesEntropyInequalityFor forwardHalfSpace zeroWave mechanicalPair := by
    simpa only [zeroWave, mechanicalPair] using satisfiesEntropyInequalityFor_elementaryWaveSolution
        hstress hpotential hderiv hpositive hsecond 0 left (strength 0)
  have hone : SatisfiesEntropyInequalityFor forwardHalfSpace oneWave mechanicalPair := by
    simpa only [oneWave, mechanicalPair] using satisfiesEntropyInequalityFor_elementaryWaveSolution
        hstress hpotential hderiv hpositive hsecond 1 middle (strength 1)
  change SatisfiesEntropyInequalityFor forwardHalfSpace
    (glueAtCommonState middle zeroWave oneWave) mechanicalPair
  exact hzero.glue_at_common_state hone fun p hp ↦ elementaryWaveSolutions_meet_at_common_state
    hpositive left middle (strength 0) (strength 1) (by rfl) p hp

end PDE.Hyperbolic.ConservationLaw.System.PSystem
