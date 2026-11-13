/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PSystem.Shock
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.CharacteristicCurve
public import PDE.Hyperbolic.ConservationLaw.System.Riemann
import PDE.Hyperbolic.ConservationLaw.System.PSystem.WaveGeometry
import PDE.Hyperbolic.ConservationLaw.System.Riemann.ElementaryChain

/-!
# Elementary waves for the one-dimensional p-system

For a stress law with `p' > 0` and `p'' > 0`, the physical p-system wave
through a left state uses different branches according to its family and
strain increment:

* family zero uses a rarefaction for a nonpositive increment and a Lax shock
  for a positive increment;
* family one uses a Lax shock for a negative increment and a rarefaction for
  a nonnegative increment.

`elementaryWaveState` makes this choice directly. Its strength is exactly the change in the strain
coordinate. The ordered map `elementaryWaveMap` first applies family zero and
then family one, as in the p-system Riemann construction.

The rarefaction and shock branches have the same value and the same joint
derivative at zero strength, namely the selected right eigenvector in the
strength direction and the identity in the state direction. The piecewise
definition is therefore jointly `C¹` in strength and left state, which is the
regularity the inverse function theorem needs.

This is the p-system instance of Theorem 4 of Evans, §11.2.4, the local solution of Riemann's
problem. Each wave follows the curve `Tₖ` of §11.2.4: the rarefaction branch comes from Theorem 1
of §11.2.2 and the shock branch satisfies the Lax entropy condition (42) of §11.2.3(b).

## Main results

* `contDiff_elementaryWaveState`: the physical wave is jointly `C¹` in
  strength and left state.
* `elementaryWaveFamily`, `elementaryWaveFamily_isElementary`: the two
  physical waves form a `LocalWaveFamily` all of whose connections are
  admissible elementary connections when `p' > 0` and `p'' > 0`.
* `elementaryRiemannHomeomorph`, `elementaryRiemannStrength`: the local
  strength chart supplied by the inverse function theorem and its inverse.
* `existsUnique_elementaryRiemann_strength`: every right state near `left` is
  reached by exactly one ordered pair of physical wave strengths inside the
  chart, with both connections admissible.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.2, Theorem 1; §11.2.3(b), equations (35)-(42);
  §11.2.4, definition of the wave curves `Tₖ` and Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.System

/-- State reached by the physical elementary wave of family `k`.

The strength is the strain increment. The value at zero strength is the left
state, independently of which branch contains the endpoint. -/
def elementaryWaveState
    (stress : ℝ → ℝ) (k : Fin 2)
    (strength : ℝ) (left : ℝ^2) : ℝ^2 :=
  if k = 0 then
    if strength ≤ 0 then
      characteristicCurve stress 0 strength left
    else
      shockState stress 0 left (left 0 + strength)
  else
    if strength < 0 then
      shockState stress 1 left (left 0 + strength)
    else
      characteristicCurve stress 1 strength left

/-- A nonpositive family-zero wave follows the characteristic curve. -/
theorem elementaryWaveState_zero_of_nonpos (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : strength ≤ 0) :
    elementaryWaveState stress 0 strength left = characteristicCurve stress 0 strength left := by
  simp [elementaryWaveState, hstrength]

/-- A positive family-zero wave follows the Lax-shock branch. -/
theorem elementaryWaveState_zero_of_pos (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : 0 < strength) :
    elementaryWaveState stress 0 strength left = shockState stress 0 left (left 0 + strength) := by
  simp [elementaryWaveState, not_le_of_gt hstrength]

/-- A negative family-one wave follows the Lax-shock branch. -/
theorem elementaryWaveState_one_of_neg (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : strength < 0) :
    elementaryWaveState stress 1 strength left = shockState stress 1 left (left 0 + strength) := by
  simp [elementaryWaveState, hstrength]

/-- A nonnegative family-one wave follows the characteristic curve. -/
theorem elementaryWaveState_one_of_nonneg (stress : ℝ → ℝ) (left : ℝ^2) {strength : ℝ}
    (hstrength : 0 ≤ strength) :
    elementaryWaveState stress 1 strength left = characteristicCurve stress 1 strength left := by
  simp [elementaryWaveState, not_lt_of_ge hstrength]

/-- Zero wave strength leaves the state unchanged. -/
@[simp]
theorem elementaryWaveState_zero_strength (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) :
    elementaryWaveState stress k 0 left = left := by
  fin_cases k <;> simp [elementaryWaveState]

/-- The strength of an elementary wave is its change in strain. -/
@[simp]
theorem elementaryWaveState_apply_zero (stress : ℝ → ℝ) (k : Fin 2) (strength : ℝ) (left : ℝ^2) :
    elementaryWaveState stress k strength left 0 = left 0 + strength := by
  fin_cases k
  · by_cases hstrength : strength ≤ 0
    · simp [elementaryWaveState, hstrength]
    · simp [elementaryWaveState, hstrength]
  · by_cases hstrength : strength < 0
    · simp [elementaryWaveState, hstrength]
    · simp [elementaryWaveState, hstrength]

/-- Distinct strengths produce distinct states on each elementary wave. -/
theorem elementaryWaveState_injective (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) :
    Function.Injective (fun strength ↦ elementaryWaveState stress k strength left) := by
  intro s t hstate
  have hstrain := congrArg (fun state : ℝ^2 ↦ state 0) hstate
  simp only [elementaryWaveState_apply_zero] at hstrain
  exact add_left_cancel hstrain

/-- Every physical elementary wave is tangent at zero strength to its
selected right characteristic vector.

For each family, the physical curve is restricted to its rarefaction branch
on one closed half-line and its shock branch on the other. The two branch
derivatives agree at zero, so their derivatives glue across the switch. -/
theorem hasDerivAt_elementaryWaveState_zero_strength {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 1 stress) (k : Fin 2) (left : ℝ^2) :
    HasDerivAt (fun strength ↦ elementaryWaveState stress k strength left)
      (rightEigenvector (soundSpeed stress (left 0)) k) 0 := by
  fin_cases k
  · have hrare : HasDerivAt (fun strength ↦ characteristicCurve stress 0 strength left)
        (rightEigenvector (soundSpeed stress (left 0)) 0) 0 := by
      simpa using hasDerivAt_characteristicCurve hstress 0 left 0
    have hshock :=
      hasDerivAt_shockState_strength_zero left (hstress.differentiable one_ne_zero (left 0)) 0
    rw [← hasDerivWithinAt_univ, ← Set.Iic_union_Ici]
    refine (hrare.hasDerivWithinAt.congr
      (fun _ h ↦ elementaryWaveState_zero_of_nonpos stress left h) (by simp)).union
      (hshock.hasDerivWithinAt.congr (fun strength hstrength ↦ ?_) (by simp))
    rcases (show 0 ≤ strength from hstrength).eq_or_lt with rfl | hpos
    · simp
    · exact elementaryWaveState_zero_of_pos stress left hpos
  · have hrare : HasDerivAt (fun strength ↦ characteristicCurve stress 1 strength left)
        (rightEigenvector (soundSpeed stress (left 0)) 1) 0 := by
      simpa using hasDerivAt_characteristicCurve hstress 1 left 0
    have hshock :=
      hasDerivAt_shockState_strength_zero left (hstress.differentiable one_ne_zero (left 0)) 1
    rw [← hasDerivWithinAt_univ, ← Set.Iic_union_Ici]
    refine (hshock.hasDerivWithinAt.congr (fun strength hstrength ↦ ?_) (by simp)).union
      (hrare.hasDerivWithinAt.congr
        (fun _ h ↦ elementaryWaveState_one_of_nonneg stress left h) (by simp))
    rcases (show strength ≤ 0 from hstrength).lt_or_eq with hneg | rfl
    · exact elementaryWaveState_one_of_neg stress left hneg
    · simp

/-- The physical elementary-wave state is jointly `C¹` in strength and left
state.

The rarefaction and Hugoniot branches are separately `C¹`. Their values and
full Fréchet derivatives agree at zero strength, so they glue across the
switching hyperplane. -/
theorem contDiff_elementaryWaveState {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ elementaryWaveState stress k p.1 p.2) := by
  have hstressOne : ContDiff ℝ 1 stress := hstress.of_le (by norm_num)
  fin_cases k
  · have hglue : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ if p.1 ≤ 0 then
        characteristicCurve stress 0 p.1 p.2 else shockState stress 0 p.2 (p.2 0 + p.1)) := by
      apply PDE.Analysis.contDiff_one_if_fst_le 0 (contDiff_characteristicCurve hstressOne 0)
        (contDiff_shockState_strength hstress hpositive 0)
      · rintro ⟨strength, state⟩ (rfl : strength = 0)
        simp
      · rintro ⟨strength, state⟩ (rfl : strength = 0)
        exact (hasFDerivAt_characteristicCurve_zero hstressOne 0 state).fderiv.trans
          (hasFDerivAt_shockState_strength_zero hstress hpositive 0 state).fderiv.symm
    simpa [elementaryWaveState] using hglue
  · have hglue : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ if p.1 ≤ 0 then
        shockState stress 1 p.2 (p.2 0 + p.1) else characteristicCurve stress 1 p.1 p.2) := by
      apply PDE.Analysis.contDiff_one_if_fst_le 0 (contDiff_shockState_strength hstress hpositive 1)
        (contDiff_characteristicCurve hstressOne 1)
      · rintro ⟨strength, state⟩ (rfl : strength = 0)
        simp
      · rintro ⟨strength, state⟩ (rfl : strength = 0)
        exact (hasFDerivAt_shockState_strength_zero hstress hpositive 1 state).fderiv.trans
          (hasFDerivAt_characteristicCurve_zero hstressOne 1 state).fderiv.symm
    have heq : (fun p : ℝ × ℝ^2 ↦ elementaryWaveState stress 1 p.1 p.2) = fun p ↦
        if p.1 ≤ 0 then shockState stress 1 p.2 (p.2 0 + p.1)
        else characteristicCurve stress 1 p.1 p.2 := by
      funext p
      rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
      · simp [elementaryWaveState, hneg, hneg.le]
      · simp [elementaryWaveState, hzero]
      · simp [elementaryWaveState, not_lt_of_ge hpos.le, not_le_of_gt hpos]
    change ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ elementaryWaveState stress 1 p.1 p.2)
    rw [heq]
    exact hglue

/-- At zero strength, a physical elementary-wave step has the standard joint
wave derivative. -/
theorem hasFDerivAt_elementaryWaveState_zero {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (state : ℝ^2) :
    HasFDerivAt (fun p : ℝ × ℝ^2 ↦ elementaryWaveState stress k p.1 p.2)
      (waveStepDerivative (rightEigenvector (soundSpeed stress (state 0)) k)) (0, state) :=
  hasFDerivAt_waveStep_zero (elementaryWaveState stress k) state
    (rightEigenvector (soundSpeed stress (state 0)) k) (elementaryWaveState_zero_strength stress k)
    ((contDiff_elementaryWaveState hstress hpositive k).differentiable one_ne_zero (0, state))
    (hasDerivAt_elementaryWaveState_zero_strength (hstress.of_le (by norm_num)) k state)

/-- The physical shock-rarefaction curves form the local wave family for the
p-system. -/
def elementaryWaveFamily
    (stress : ℝ → ℝ) (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) :
    LocalWaveFamily (flux stress)
      (fun k ↦
        characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive k) where
  curve := elementaryWaveState stress
  curve_zero := elementaryWaveState_zero_strength stress
  hasStrictFDerivAt_zero k state _hstate :=
    (contDiff_elementaryWaveState hstress hpositive k).contDiffAt
      |>.hasStrictFDerivAt'
        (hasFDerivAt_elementaryWaveState_zero
          hstress hpositive k state)
        one_ne_zero

/-- Every family-zero physical wave is an admissible elementary connection.
Zero strength is represented by the `same` constructor. -/
theorem isElementaryConnection_elementaryWaveState_zero
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) (strength : ℝ) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 0
      left (elementaryWaveState stress 0 strength left) := by
  rcases lt_trichotomy strength 0 with hneg | hzero | hpos
  · rw [elementaryWaveState_zero_of_nonpos stress left hneg.le]
    exact isElementaryConnection_characteristicCurve_zero_of_neg hstress hpositive hsecond left hneg
  · subst strength
    rw [elementaryWaveState_zero_strength]
    exact IsElementaryConnection.same left
  · rw [elementaryWaveState_zero_of_pos stress left hpos]
    exact isElementaryConnection_shockState_zero_of_left_lt_right
      hstress hpositive hsecond left (lt_add_of_pos_right _ hpos)

/-- Every family-one physical wave is an admissible elementary connection.
Zero strength is represented by the `same` constructor. -/
theorem isElementaryConnection_elementaryWaveState_one
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) (strength : ℝ) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 1
      left (elementaryWaveState stress 1 strength left) := by
  rcases lt_trichotomy strength 0 with hneg | hzero | hpos
  · rw [elementaryWaveState_one_of_neg stress left hneg]
    exact isElementaryConnection_shockState_one_of_right_lt_left
      hstress hpositive hsecond left (by linarith)
  · subst strength
    rw [elementaryWaveState_zero_strength]
    exact IsElementaryConnection.same left
  · rw [elementaryWaveState_one_of_nonneg stress left hpos.le]
    exact isElementaryConnection_characteristicCurve_one_of_pos hstress hpositive hsecond left hpos

/-- Every physical p-system wave branch is an admissible elementary
connection. -/
theorem isElementaryConnection_elementaryWaveState
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (k : Fin 2) (left : ℝ^2) (strength : ℝ) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) k
      left (elementaryWaveState stress k strength left) := by
  fin_cases k
  · simpa using
      isElementaryConnection_elementaryWaveState_zero hstress hpositive hsecond left strength
  · simpa using
      isElementaryConnection_elementaryWaveState_one hstress hpositive hsecond left strength

/-- The physical p-system wave family consists entirely of admissible
elementary connections. -/
theorem elementaryWaveFamily_isElementary {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) :
    (elementaryWaveFamily stress hstress hpositive).IsElementary := by
  intro k strength state
  exact isElementaryConnection_elementaryWaveState hstress hpositive hsecond k state strength

/-- Apply the physical family-zero wave and then the physical family-one
wave. -/
def elementaryWaveMap
    (stress : ℝ → ℝ) (left strength : ℝ^2) : ℝ^2 :=
  elementaryWaveState stress 1 (strength 1)
    (elementaryWaveState stress 0 (strength 0) left)

/-- Zero strengths leave the left state unchanged. -/
@[simp]
theorem elementaryWaveMap_zero (stress : ℝ → ℝ) (left : ℝ^2) :
    elementaryWaveMap stress left 0 = left := by
  simp [elementaryWaveMap]

/-- The generic ordered composition of the physical wave family is the
explicit elementary wave map. -/
theorem elementaryWaveFamily_composedWaveMap {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left strength : ℝ^2) :
    (elementaryWaveFamily stress hstress hpositive |>.composedWaveMap left) strength =
      elementaryWaveMap stress left strength := by
  change elementaryWaveState stress 1 (strength 1)
        (elementaryWaveState stress 0 (strength 0) left) = elementaryWaveMap stress left strength
  rfl

-- The first prefix state is the result of the family-zero elementary wave.
private theorem elementaryWaveFamily_intermediateState_one {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (left strength : ℝ^2) :
    (elementaryWaveFamily stress hstress hpositive ).intermediateState left strength 1 =
      elementaryWaveState stress 0 (strength 0) left := by
  simpa [elementaryWaveFamily] using (elementaryWaveFamily stress hstress hpositive
      ).intermediateState_succ left strength (0 : Fin 2)

/-- The total strain change is the sum of the two family strengths. -/
@[simp]
theorem elementaryWaveMap_apply_zero (stress : ℝ → ℝ) (left strength : ℝ^2) :
    elementaryWaveMap stress left strength 0 = left 0 + strength 0 + strength 1 := by
  simp [elementaryWaveMap]

/-- In the two-rarefaction quadrant, the physical wave map agrees with the
characteristic wave map used by the inverse-function theorem. -/
theorem elementaryWaveMap_eq_characteristicWaveMap_of_nonpos_nonneg (stress : ℝ → ℝ)
    (left strength : ℝ^2) (hzero : strength 0 ≤ 0) (hone : 0 ≤ strength 1) :
    elementaryWaveMap stress left strength = characteristicWaveMap stress left strength := by
  rw [elementaryWaveMap, elementaryWaveState_zero_of_nonpos stress left hzero,
    elementaryWaveState_one_of_nonneg stress (characteristicCurve stress 0 (strength 0) left) hone]
  rfl

/-- The right eigenvectors of the characteristic field at `left` are the eigenbasis vectors
attached to the sound speed at `left 0`. -/
theorem elementaryWaveFamily_rightEigenvector_eq_eigenbasis
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    ∀ k,
      ((characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive k
          ).rightEigenvector left) =
        eigenbasis (soundSpeed stress (left 0))
          (soundSpeed_pos (hpositive (left 0))) k := by
  intro k
  change rightEigenvector (soundSpeed stress (left 0)) k = eigenbasis (soundSpeed stress (left 0))
        (soundSpeed_pos (hpositive (left 0))) k
  exact (eigenbasis_apply (soundSpeed stress (left 0)) (soundSpeed_pos (hpositive (left 0))) k).symm

/-- Local wave-strength coordinates for the physical p-system waves.

The source is an open neighborhood of zero strength, the target is an open
neighborhood of `left`, and the forward map is `elementaryWaveMap`. Using
Mathlib's `OpenPartialHomeomorph` exposes the local inverse and its uniqueness
without introducing a separate Riemann-solver structure. -/
def elementaryRiemannHomeomorph
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    OpenPartialHomeomorph (ℝ^2) (ℝ^2) :=
  (elementaryWaveFamily stress hstress hpositive
    ).localRiemannHomeomorph left (Set.mem_univ left)
      (eigenbasis (soundSpeed stress (left 0))
        (soundSpeed_pos (hpositive (left 0))))
      (elementaryWaveFamily_rightEigenvector_eq_eigenbasis
        hstress hpositive left)

/-- The forward map of the local strength chart is the ordered physical wave
map. -/
@[simp]
theorem elementaryRiemannHomeomorph_apply {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left strength : ℝ^2) :
    elementaryRiemannHomeomorph hstress hpositive left strength =
      elementaryWaveMap stress left strength := by
  simp only [elementaryRiemannHomeomorph, LocalWaveFamily.localRiemannHomeomorph_apply,
    elementaryWaveFamily_composedWaveMap]

/-- Zero strength belongs to the source neighborhood of the physical
p-system Riemann solver. -/
theorem zero_mem_elementaryRiemannHomeomorph_source {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    0 ∈ (elementaryRiemannHomeomorph hstress hpositive left).source := by
  exact (elementaryWaveFamily stress hstress hpositive
      ).zero_mem_localRiemannHomeomorph_source left (Set.mem_univ left)
        (eigenbasis (soundSpeed stress (left 0)) (soundSpeed_pos (hpositive (left 0))))
        (elementaryWaveFamily_rightEigenvector_eq_eigenbasis hstress hpositive left)

/-- The left state belongs to the target neighborhood of the physical
p-system Riemann solver. -/
theorem left_mem_elementaryRiemannHomeomorph_target {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    left ∈ (elementaryRiemannHomeomorph hstress hpositive left).target := by
  exact (elementaryWaveFamily stress hstress hpositive
      ).left_mem_localRiemannHomeomorph_target left (Set.mem_univ left)
        (eigenbasis (soundSpeed stress (left 0)) (soundSpeed_pos (hpositive (left 0))))
        (elementaryWaveFamily_rightEigenvector_eq_eigenbasis hstress hpositive left)

/-- Canonical ordered wave strengths for a nearby right state.

Outside the target neighborhood this is the totalized inverse supplied by
`OpenPartialHomeomorph`; the endpoint and uniqueness theorems below therefore
retain explicit target-membership hypotheses. -/
def elementaryRiemannStrength
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (left right : ℝ^2) : ℝ^2 :=
  (elementaryRiemannHomeomorph
    hstress hpositive left).symm right

/-- The selected p-system wave strengths vary continuously with the nearby
right state. -/
theorem continuousOn_elementaryRiemannStrength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    ContinuousOn (elementaryRiemannStrength hstress hpositive left)
      (elementaryRiemannHomeomorph hstress hpositive left).target := by
  change ContinuousOn (fun right ↦ (elementaryRiemannHomeomorph hstress hpositive left).symm right)
    (elementaryRiemannHomeomorph hstress hpositive left).target
  exact (elementaryRiemannHomeomorph hstress hpositive left).continuousOn_symm

/-- Equal left and right states have zero strengths in both wave families. -/
@[simp]
theorem elementaryRiemannStrength_self {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    elementaryRiemannStrength hstress hpositive left left = 0 := by
  let e := elementaryRiemannHomeomorph hstress hpositive left
  have hzero : (0 : ℝ^2) ∈ e.source := by
    simpa only [e] using zero_mem_elementaryRiemannHomeomorph_source hstress hpositive left
  have hinv := e.left_inv hzero
  simpa only [e, elementaryRiemannStrength,
    elementaryRiemannHomeomorph_apply, elementaryWaveMap_zero] using hinv

/-- The selected wave strengths lie in the source neighborhood. -/
theorem elementaryRiemannStrength_mem_source {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) :
    elementaryRiemannStrength hstress hpositive left right ∈
      (elementaryRiemannHomeomorph hstress hpositive left).source :=
  (elementaryRiemannHomeomorph hstress hpositive left).map_target hright

/-- Applying the selected physical waves reaches the prescribed right
state. -/
theorem elementaryWaveMap_elementaryRiemannStrength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) :
    elementaryWaveMap stress left (elementaryRiemannStrength hstress hpositive left right) =
      right := by
  exact (elementaryRiemannHomeomorph hstress hpositive left).right_inv hright

/-- The sum of the selected family strengths is the total strain change. -/
theorem elementaryRiemannStrength_zero_add_one {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) {right : ℝ^2}
    (hright : right ∈ (elementaryRiemannHomeomorph hstress hpositive left).target) :
    elementaryRiemannStrength hstress hpositive left right 0 +
      elementaryRiemannStrength hstress hpositive left right 1 = right 0 - left 0 := by
  have hendpoint := congrArg (fun state : ℝ^2 ↦ state 0)
    (elementaryWaveMap_elementaryRiemannStrength hstress hpositive left hright)
  simp only [elementaryWaveMap_apply_zero] at hendpoint
  linarith

/-- The selected vector is the unique strength in the source neighborhood
that reaches the prescribed right state. -/
theorem elementaryRiemannStrength_unique {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) {right strength : ℝ^2}
    (hstrength : strength ∈ (elementaryRiemannHomeomorph hstress hpositive left).source)
    (hmap : elementaryWaveMap stress left strength = right) :
    strength = elementaryRiemannStrength hstress hpositive left right := by
  let e := elementaryRiemannHomeomorph hstress hpositive left
  calc
    strength = e.symm (e strength) := (e.left_inv hstrength).symm
    _ = e.symm right :=
      congrArg e.symm <| by
        simpa [e] using hmap
    _ = elementaryRiemannStrength hstress hpositive left right := rfl

/-- Intermediate state after applying the family-zero wave selected for a
nearby Riemann problem. -/
def elementaryRiemannIntermediateState
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (left right : ℝ^2) : ℝ^2 :=
  elementaryWaveState stress 0
    (elementaryRiemannStrength
      hstress hpositive left right 0) left

/-- The selected intermediate state varies continuously with the nearby
right state. -/
theorem continuousOn_elementaryRiemannIntermediateState {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    ContinuousOn (elementaryRiemannIntermediateState hstress hpositive left)
      (elementaryRiemannHomeomorph hstress hpositive left).target := by
  have hstrength := continuousOn_elementaryRiemannStrength hstress hpositive left
  have hfirst : ContinuousOn (fun right ↦ elementaryRiemannStrength hstress hpositive left right 0)
        (elementaryRiemannHomeomorph hstress hpositive left).target :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) (0 : Fin 2)
      ).continuousOn.comp hstrength (fun _ _ ↦ Set.mem_univ _)
  have hinput : ContinuousOn (fun right ↦ (elementaryRiemannStrength
            hstress hpositive left right 0, left))
        (elementaryRiemannHomeomorph hstress hpositive left).target :=
    hfirst.prodMk continuousOn_const
  exact (contDiff_elementaryWaveState hstress hpositive 0 ).continuous.continuousOn.comp hinput
        (fun _ _ ↦ Set.mem_univ _)

/-- When the two Riemann states coincide, the selected intermediate state is
the same state. -/
@[simp]
theorem elementaryRiemannIntermediateState_self {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    elementaryRiemannIntermediateState hstress hpositive left left = left := by
  rw [elementaryRiemannIntermediateState, elementaryRiemannStrength_self hstress hpositive left]
  exact elementaryWaveState_zero_strength stress 0 left

/-- The family-zero wave selected by the local p-system solver joins the left
state to the intermediate state. -/
theorem isElementaryConnection_elementaryRiemannIntermediateState_zero
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left right : ℝ^2) :
    IsElementaryConnection
        (characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive) 0
        left
        (elementaryRiemannIntermediateState
          hstress hpositive left right) := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  have hconnection := (elementaryWaveFamily stress hstress hpositive
      ).isElementaryConnection_intermediateState (elementaryWaveFamily_isElementary
          hstress hpositive hsecond) left strength (0 : Fin 2)
  simpa [strength, elementaryRiemannIntermediateState,
    elementaryWaveFamily_intermediateState_one] using hconnection

/-- The family-one wave selected by the local p-system solver joins the
intermediate state to the prescribed right state. -/
theorem isElementaryConnection_elementaryRiemannIntermediateState_one
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {right : ℝ^2}
    (hright :
      right ∈ (elementaryRiemannHomeomorph
        hstress hpositive left).target) :
    IsElementaryConnection
        (characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive) 1
        (elementaryRiemannIntermediateState
          hstress hpositive left right)
        right := by
  let strength := elementaryRiemannStrength hstress hpositive left right
  have hconnections (k : Fin 2) := (elementaryWaveFamily stress hstress hpositive
      ).isElementaryConnection_intermediateState (elementaryWaveFamily_isElementary
          hstress hpositive hsecond) left strength k
  have hmap :
      elementaryWaveMap stress left strength = right := by
    simpa only [strength] using elementaryWaveMap_elementaryRiemannStrength
        hstress hpositive left hright
  simpa [strength, elementaryRiemannIntermediateState, elementaryWaveFamily_intermediateState_one,
    LocalWaveFamily.intermediateState_eq_composedWaveMap,
    elementaryWaveFamily_composedWaveMap, hmap] using hconnections 1

/-- The physical p-system wave map gives locally unique wave strengths near
every strictly hyperbolic left state. -/
theorem existsUnique_elementaryWaveMap_strength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    ∃ source target : Set (ℝ^2), IsOpen source ∧ IsOpen target ∧ 0 ∈ source ∧ left ∈ target ∧
      ∀ right ∈ target, ∃! strength : ℝ^2, strength ∈ source ∧
      elementaryWaveMap stress left strength = right := by
  let e := elementaryRiemannHomeomorph hstress hpositive left
  refine ⟨e.source, e.target, e.open_source, e.open_target, ?_, ?_, ?_⟩
  · simpa only [e] using zero_mem_elementaryRiemannHomeomorph_source hstress hpositive left
  · simpa only [e] using left_mem_elementaryRiemannHomeomorph_target hstress hpositive left
  · intro right hright
    refine ⟨elementaryRiemannStrength hstress hpositive left right, ⟨?_, ?_⟩, ?_⟩
    · exact elementaryRiemannStrength_mem_source hstress hpositive left hright
    · exact elementaryWaveMap_elementaryRiemannStrength hstress hpositive left hright
    · exact fun strength hstrength ↦ elementaryRiemannStrength_unique
        hstress hpositive left hstrength.1 hstrength.2

/-- Nearby right states are joined to the left state by unique ordered
physical wave strengths, and both resulting connections are admissible. -/
theorem existsUnique_elementaryRiemann_strength
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) :
    ∃ source target : Set (ℝ^2),
      IsOpen source ∧ IsOpen target ∧
      0 ∈ source ∧ left ∈ target ∧
      ∀ right ∈ target,
        ∃! strength : ℝ^2,
          strength ∈ source ∧
            elementaryWaveMap stress left strength = right ∧
            IsElementaryConnection
              (characteristicField stress
                (hstress.differentiable (by norm_num)) hpositive) 0
              left
              (elementaryWaveState stress 0 (strength 0) left) ∧
            IsElementaryConnection
              (characteristicField stress
                (hstress.differentiable (by norm_num)) hpositive) 1
              (elementaryWaveState stress 0 (strength 0) left)
              right := by
  let family := elementaryWaveFamily stress hstress hpositive
  let basis := eigenbasis (soundSpeed stress (left 0)) (soundSpeed_pos (hpositive (left 0)))
  have hfamily : family.IsElementary := by
    simpa only [family] using elementaryWaveFamily_isElementary hstress hpositive hsecond
  have hbasis : ∀ k, ((characteristicField stress (hstress.differentiable (by norm_num))
      hpositive k).rightEigenvector left) = basis k := by
    simpa only [basis] using
      elementaryWaveFamily_rightEigenvector_eq_eigenbasis hstress hpositive left
  obtain ⟨source, target, hopenSource, hopenTarget, hzero, hleft, hsolve⟩ :=
    family.existsUnique_localRiemann_strength_with_elementary_connections
      hfamily left (Set.mem_univ left) basis hbasis
  refine ⟨source, target, hopenSource, hopenTarget, hzero, hleft, fun right hright ↦ ?_⟩
  obtain ⟨strength, ⟨hsource, hmap, hconnections⟩, hunique⟩ := hsolve right hright
  have hfinal : family.intermediateState left strength 2 = right := by
    rw [family.intermediateState_eq_composedWaveMap]
    exact hmap
  have hconnection := hconnections (1 : Fin 2)
  change IsElementaryConnection _ _ (family.intermediateState left strength 1)
    (family.intermediateState left strength 2) at hconnection
  rw [hfinal] at hconnection
  exact ⟨strength, ⟨hsource,
      by simpa only [family, elementaryWaveFamily_composedWaveMap] using hmap,
      by simpa [family, elementaryWaveFamily_intermediateState_one] using hconnections (0 : Fin 2),
      by simpa [family, elementaryWaveFamily_intermediateState_one] using hconnection⟩,
    fun candidate hcandidate ↦ hunique candidate ⟨hcandidate.1,
      by simpa only [family, elementaryWaveFamily_composedWaveMap] using hcandidate.2.1,
      fun k ↦ family.isElementaryConnection_intermediateState hfamily left candidate k⟩⟩

end PDE.Hyperbolic.ConservationLaw.System.PSystem
