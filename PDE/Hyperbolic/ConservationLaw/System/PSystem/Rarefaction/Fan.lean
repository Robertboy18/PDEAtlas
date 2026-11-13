/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Piecewise
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.Rarefaction.Profile
public import PDE.Hyperbolic.ConservationLaw.AffineFan
public import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
import PDE.Hyperbolic.ConservationLaw.System.AffineFan
import PDE.Hyperbolic.ConservationLaw.System.EntropyAffineFan
import PDE.Hyperbolic.ConservationLaw.System.PSystem.WaveGeometry

/-!
# Rarefaction fans for the one-dimensional p-system

A `k`-rarefaction fan joins a left state to the point of its `k`th
characteristic curve at the given strength. It is constant on either side of
the wedge bounded by the characteristic speeds of the two endpoint states and
equal to the self-similar profile `rarefactionProfile` inside the wedge, so
the state depends on `x / t` alone. The fan is physical exactly when the two
speeds are ordered, `λₖ(left) ≤ λₖ(right)`; for `p'' > 0` this means a
nonpositive strain increment in family zero and a nonnegative one in family
one.

The self-similar profile is extended by its endpoint tangent lines, producing
a global `C¹` middle state without changing its value or derivative on the
physical fan interval. The affine-fan integration theorem then adjoins the
constant endpoint states and proves that the resulting rarefaction fan is a
global entropy weak solution on positive time.

An ordered fan with distinct endpoint speeds is the centered `k`-rarefaction wave of Theorem 1 of
Evans, §11.2.2, whose hypothesis (ii) is `u_r ∈ Rₖ⁺(u_l)`. Evans obtains it from the rarefaction
solution of the scalar law (7) of §11.2.1; we integrate the affine fan directly. The zero
entropy production is the equality case of the entropy inequalities (29) of §11.4.2.

## Main results

* `rarefactionFan`: the fan profile, assembled with `AffineFan.profile`.
* `isWeakSolution_rarefactionFan`: an ordered fan is a weak solution of the
  p-system on `t > 0`.
* `isEntropyWeakSolution_rarefactionFan`: an ordered fan has zero entropy
  production for every entropy pair of the flux, hence is an entropy weak
  solution.
* `isEntropyWeakSolution_rarefactionFan_zero_of_nonpos`,
  `isEntropyWeakSolution_rarefactionFan_one_of_nonneg`: on the physical
  branches the ordering hypothesis follows from `p' > 0` and `p'' > 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (7)-(9); §11.2.2, Theorem 1 and its
  proof; §11.4.2, equations (25)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.System

/-! ## Global weak rarefaction fans -/

/-- Extend the rarefaction profile globally by its endpoint tangent lines.

The extension is an analytic device for the weak gluing theorem. On the
physical fan interval it is exactly the rarefaction profile, while outside
that interval the assembled solution uses the constant endpoint states. -/
def extendedRarefactionProfile
    (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2)
    (strength : ℝ) : ℝ → ℝ^2 :=
  PDE.Analysis.tangentExtension (rarefactionProfile stress k left)
    (rarefactionSpeed stress k (left 0))
    (rarefactionSpeed stress k (left 0 + strength))

/-- The extended profile agrees with the rarefaction profile throughout the
closed fan interval. -/
theorem extendedRarefactionProfile_eq_of_mem_Icc {stress : ℝ → ℝ} {k : Fin 2} {left : ℝ^2}
    {strength speed : ℝ}
    (hspeed : speed ∈ Set.Icc (rarefactionSpeed stress k (left 0))
      (rarefactionSpeed stress k (left 0 + strength))) :
    extendedRarefactionProfile stress k left strength speed =
      rarefactionProfile stress k left speed :=
  PDE.Analysis.tangentExtension_eq_of_mem_Icc hspeed

/-- An ordered rarefaction profile has a global `C¹` tangent extension. -/
theorem contDiff_extendedRarefactionProfile {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength)) :
    ContDiff ℝ 1 (extendedRarefactionProfile stress k left strength) := by
  apply PDE.Analysis.contDiff_tangentExtension horder
  intro speed hspeed
  apply contDiffAt_rarefactionProfile hstress hpositive hsecond
  exact mem_range_rarefactionSpeed_of_mem_Icc
    hstress k (left 0) (left 0 + strength) hspeed

/-- Tangent extension preserves the rarefaction ODE on the closed fan
interval, including at both interfaces. -/
theorem extendedRarefactionProfile_ode {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength))
    {speed : ℝ}
    (hspeed : speed ∈ Set.Icc (rarefactionSpeed stress k (left 0))
      (rarefactionSpeed stress k (left 0 + strength))) :
    fderiv ℝ (flux stress)
        (extendedRarefactionProfile stress k left strength speed)
        (curveTangent
          (extendedRarefactionProfile stress k left strength) speed) =
      speed •
        curveTangent
          (extendedRarefactionProfile stress k left strength) speed := by
  have hrange : speed ∈ Set.range (rarefactionSpeed stress k) :=
    mem_range_rarefactionSpeed_of_mem_Icc hstress k (left 0) (left 0 + strength) hspeed
  have hdifferentiable : DifferentiableAt ℝ (rarefactionProfile stress k left) speed :=
    (contDiffAt_rarefactionProfile hstress hpositive hsecond k left hrange).differentiableAt_one
  have hderiv : curveTangent (extendedRarefactionProfile stress k left strength) speed =
        curveTangent (rarefactionProfile stress k left) speed := by
    exact PDE.Analysis.deriv_tangentExtension_eq_of_mem_Icc horder hspeed hdifferentiable
  rw [extendedRarefactionProfile_eq_of_mem_Icc hspeed, hderiv]
  exact rarefactionProfile_ode hstress hpositive hsecond k left hrange

/-- The self-similar tangent extension solves the p-system throughout the
closed fan interval. -/
theorem fluxResidual_selfSimilar_extendedRarefactionProfile_eq_zero_of_mem_Icc {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2) (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength))
    {p : ℝ^2} (htime : p 0 ≠ 0)
    (hspeed : similarityVariable p ∈ Set.Icc (rarefactionSpeed stress k (left 0))
      (rarefactionSpeed stress k (left 0 + strength))) :
    fluxResidual (flux stress) (selfSimilarWave (extendedRarefactionProfile stress k left strength))
      p = 0 := by
  apply fluxResidual_selfSimilarWave_eq_zero htime
  · exact differentiableAt_flux
      (hstress.differentiable (by norm_num)
        (extendedRarefactionProfile stress k left strength
          (similarityVariable p) 0))
  · exact
      (contDiff_extendedRarefactionProfile
        hstress hpositive hsecond k left strength horder).differentiable
        (by norm_num) (similarityVariable p)
  · exact extendedRarefactionProfile_ode
      hstress hpositive hsecond k left strength horder hspeed

/-- The p-system rarefaction fan with constant endpoint states and the
self-similar rarefaction profile between them. -/
def rarefactionFan
    (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2)
    (strength : ℝ) : ℝ^2 → ℝ^2 :=
  AffineFan.profile (rarefactionSpeed stress k (left 0))
    (rarefactionSpeed stress k (left 0 + strength))
    left
    (selfSimilarWave (extendedRarefactionProfile stress k left strength))
    (characteristicCurve stress k strength left)

/-- A p-system rarefaction fan is invariant under positive spacetime
dilation. -/
theorem rarefactionFan_smul_of_pos {stress : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (k : Fin 2) (left : ℝ^2)
    (strength : ℝ) (p : ℝ^2) :
    rarefactionFan stress k left strength (a • p) = rarefactionFan stress k left strength p := by
  unfold rarefactionFan
  apply AffineFan.profile_smul_of_pos ha
  intro q
  exact selfSimilarWave_smul ha.ne' _ q

/-- An ordered rarefaction fan is measurable on spacetime. -/
theorem measurable_rarefactionFan {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength)) :
    Measurable (rarefactionFan stress k left strength) := by
  have hsimilarity : Measurable similarityVariable := by
    change Measurable (fun p : ℝ^2 ↦ p 1 * (p 0)⁻¹)
    fun_prop
  have hmiddle : Measurable (selfSimilarWave (extendedRarefactionProfile stress k left strength)) :=
    (contDiff_extendedRarefactionProfile
      hstress hpositive hsecond k left strength horder).continuous.measurable.comp hsimilarity
  unfold rarefactionFan AffineFan.profile
  exact Measurable.ite (AffineInterface.measurableSet_leftHalfSpace
      (rarefactionSpeed stress k (left 0))) measurable_const
    (Measurable.ite (AffineInterface.measurableSet_leftHalfSpace
        (rarefactionSpeed stress k (left 0 + strength))) hmiddle measurable_const)

/-- On positive time, a rarefaction fan has a uniform norm bound. If the speeds are not
ordered, the middle region is empty and only the two end states occur. -/
theorem exists_norm_rarefactionFan_le_of_pos_time {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ) :
    ∃ C : ℝ, ∀ p : ℝ^2, 0 < p 0 → ‖rarefactionFan stress k left strength p‖ ≤ C := by
  let leftSpeed := rarefactionSpeed stress k (left 0)
  let rightSpeed := rarefactionSpeed stress k (left 0 + strength)
  let middle := extendedRarefactionProfile stress k left strength
  let right := characteristicCurve stress k strength left
  by_cases horder : leftSpeed ≤ rightSpeed
  swap
  · refine ⟨max ‖left‖ ‖right‖, fun p htime ↦ ?_⟩
    change ‖AffineFan.profile leftSpeed rightSpeed left (selfSimilarWave middle) right p‖ ≤
      max ‖left‖ ‖right‖
    by_cases hleft : p ∈ AffineInterface.leftHalfSpace leftSpeed
    · rw [AffineFan.profile_eq_left hleft]
      exact le_max_left _ _
    · by_cases hright : p ∈ AffineInterface.leftHalfSpace rightSpeed
      · have h1 : leftSpeed * p 0 ≤ p 1 := le_of_not_gt hleft
        have h2 : p 1 < rightSpeed * p 0 := hright
        exact absurd (lt_of_mul_lt_mul_right (h1.trans_lt h2) htime.le).le horder
      · rw [AffineFan.profile_eq_right hleft hright]
        exact le_max_right _ _
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (contDiff_extendedRarefactionProfile
        hstress hpositive hsecond k left strength horder).continuous.continuousOn
  refine ⟨max ‖left‖ (max C ‖right‖), ?_⟩
  intro p htime
  change ‖AffineFan.profile leftSpeed rightSpeed left (selfSimilarWave middle) right p‖ ≤
      max ‖left‖ (max C ‖right‖)
  by_cases hleft : p ∈ AffineInterface.leftHalfSpace leftSpeed
  · rw [AffineFan.profile_eq_left hleft]
    exact le_max_left _ _
  · by_cases hright : p ∈ AffineInterface.leftHalfSpace rightSpeed
    · rw [AffineFan.profile_eq_middle hleft hright]
      apply (hC (similarityVariable p) ?_).trans
      · exact (le_max_left C ‖right‖).trans (le_max_right ‖left‖ (max C ‖right‖))
      · constructor
        · rw [similarityVariable, le_div_iff₀ htime]
          exact le_of_not_gt hleft
        · rw [similarityVariable, div_le_iff₀ htime]
          exact hright.le
    · rw [AffineFan.profile_eq_right hleft hright]
      exact (le_max_right C ‖right‖).trans (le_max_right _ _)

/-- A nonpositive family-zero strength orders the two rarefaction speeds. -/
theorem rarefactionSpeed_zero_le_of_nonpos {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2)
    {strength : ℝ} (hstrength : strength ≤ 0) :
    rarefactionSpeed stress 0 (left 0) ≤ rarefactionSpeed stress 0 (left 0 + strength) := by
  rcases hstrength.eq_or_lt with hzero | hneg
  · subst strength
    simp
  · have hspeed :=
      characteristicSpeed_lt_characteristicCurve_zero_of_neg hstress hpositive hsecond left hneg
    simpa [characteristicField, rarefactionSpeed] using hspeed.le

/-- A nonnegative family-one strength orders the two rarefaction speeds. -/
theorem rarefactionSpeed_one_le_of_nonneg {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2)
    {strength : ℝ} (hstrength : 0 ≤ strength) :
    rarefactionSpeed stress 1 (left 0) ≤ rarefactionSpeed stress 1 (left 0 + strength) := by
  rcases hstrength.eq_or_lt with hzero | hpos
  · subst strength
    simp
  · have hspeed :=
      characteristicSpeed_lt_characteristicCurve_one_of_pos hstress hpositive hsecond left hpos
    simpa [characteristicField, rarefactionSpeed] using hspeed.le

private theorem contDiffAt_rarefactionFan_middle {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength))
    (p : ℝ^2) (hp : p ∈ forwardHalfSpace) :
    ContDiffAt ℝ 1 (selfSimilarWave (extendedRarefactionProfile stress k left strength)) p := by
  apply contDiffAt_selfSimilarWave (contDiff_extendedRarefactionProfile
      hstress hpositive hsecond k left strength horder).contDiffAt
  exact ne_of_gt hp

private theorem fluxResidual_rarefactionFan_middle_eq_zero {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2) (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength))
    (p : ℝ^2)
    (hp : p ∈ AffineFan.middleRegion (rarefactionSpeed stress k (left 0))
      (rarefactionSpeed stress k (left 0 + strength))) :
    fluxResidual (flux stress) (selfSimilarWave (extendedRarefactionProfile stress k left strength))
      p = 0 := by
  rcases hp with ⟨htime, hright, hleft⟩
  change 0 < p 0 at htime
  have hspeed : similarityVariable p ∈ Set.Icc (rarefactionSpeed stress k (left 0))
        (rarefactionSpeed stress k (left 0 + strength)) := by
    constructor
    · rw [similarityVariable, le_div_iff₀ htime]
      exact le_of_not_gt hleft
    · rw [similarityVariable, div_le_iff₀ htime]
      exact hright.le
  exact fluxResidual_selfSimilar_extendedRarefactionProfile_eq_zero_of_mem_Icc
      hstress hpositive hsecond k left strength horder (ne_of_gt htime) hspeed

private theorem rarefactionFan_middle_left_trace {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength))
    (t : ℝ) (ht : 0 < t) :
    selfSimilarWave (extendedRarefactionProfile stress k left strength)
      (AffineInterface.interface (rarefactionSpeed stress k (left 0)) t) = left := by
  have hsimilarity : similarityVariable (AffineInterface.interface
            (rarefactionSpeed stress k (left 0)) t) =
        rarefactionSpeed stress k (left 0) := by
    rw [similarityVariable]
    simp only [AffineInterface.interface_time, AffineInterface.interface_space]
    exact mul_div_cancel_right₀ (rarefactionSpeed stress k (left 0)) ht.ne'
  change extendedRarefactionProfile stress k left strength (similarityVariable
      (AffineInterface.interface (rarefactionSpeed stress k (left 0)) t)) = left
  rw [hsimilarity]
  rw [extendedRarefactionProfile_eq_of_mem_Icc ⟨le_rfl, horder⟩]
  exact rarefactionProfile_leftSpeed hstress hpositive hsecond k left

private theorem rarefactionFan_middle_right_trace {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength))
    (t : ℝ) (ht : 0 < t) :
    selfSimilarWave (extendedRarefactionProfile stress k left strength)
      (AffineInterface.interface (rarefactionSpeed stress k (left 0 + strength)) t) =
      characteristicCurve stress k strength left := by
  have hsimilarity : similarityVariable (AffineInterface.interface
            (rarefactionSpeed stress k (left 0 + strength)) t) =
        rarefactionSpeed stress k (left 0 + strength) := by
    rw [similarityVariable]
    simp only [AffineInterface.interface_time, AffineInterface.interface_space]
    exact mul_div_cancel_right₀ (rarefactionSpeed stress k (left 0 + strength)) ht.ne'
  change extendedRarefactionProfile stress k left strength (similarityVariable
      (AffineInterface.interface (rarefactionSpeed stress k (left 0 + strength)) t)) =
      characteristicCurve stress k strength left
  rw [hsimilarity]
  rw [extendedRarefactionProfile_eq_of_mem_Icc ⟨horder, le_rfl⟩]
  exact rarefactionProfile_rightSpeed hstress hpositive hsecond k left strength

/-- Every ordered p-system rarefaction fan is a weak solution on positive
time. -/
theorem isWeakSolution_rarefactionFan {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength)) :
    IsWeakSolution (flux stress) forwardHalfSpace (rarefactionFan stress k left strength) := by
  let leftSpeed := rarefactionSpeed stress k (left 0)
  let rightSpeed := rarefactionSpeed stress k (left 0 + strength)
  let profile := extendedRarefactionProfile stress k left strength
  let middle := selfSimilarWave profile
  let right := characteristicCurve stress k strength left
  have hflux : ContDiff ℝ 1 (flux stress) :=
    contDiff_flux (hstress.of_le (by norm_num))
  change IsWeakSolution (flux stress) forwardHalfSpace
    (AffineFan.profile leftSpeed rightSpeed left middle right)
  apply isWeakSolution_affineFan (flux stress) hflux leftSpeed rightSpeed horder left right middle
  · intro p hp
    exact contDiffAt_rarefactionFan_middle hstress hpositive hsecond k left strength horder p hp
  · intro p hp
    exact fluxResidual_rarefactionFan_middle_eq_zero
      hstress hpositive hsecond k left strength horder p hp
  · intro t ht
    exact rarefactionFan_middle_left_trace hstress hpositive hsecond k left strength horder t ht
  · intro t ht
    exact rarefactionFan_middle_right_trace hstress hpositive hsecond k left strength horder t ht

/-- Every ordered p-system rarefaction fan satisfies the entropy inequality
for any compatible entropy pair, in fact with zero entropy production. -/
theorem satisfiesEntropyInequalityFor_rarefactionFan {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (E : EntropyPair (flux stress)) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength)) :
    SatisfiesEntropyInequalityFor forwardHalfSpace (rarefactionFan stress k left strength) E := by
  let leftSpeed := rarefactionSpeed stress k (left 0)
  let rightSpeed := rarefactionSpeed stress k (left 0 + strength)
  let profile := extendedRarefactionProfile stress k left strength
  let middle := selfSimilarWave profile
  let right := characteristicCurve stress k strength left
  change SatisfiesEntropyInequalityFor forwardHalfSpace
    (AffineFan.profile leftSpeed rightSpeed left middle right) E
  apply satisfiesEntropyInequalityFor_affineFan E leftSpeed rightSpeed horder left right middle
  · intro p hp
    exact contDiffAt_rarefactionFan_middle hstress hpositive hsecond k left strength horder p hp
  · intro p hp
    exact fluxResidual_rarefactionFan_middle_eq_zero
      hstress hpositive hsecond k left strength horder p hp
  · intro t ht
    exact rarefactionFan_middle_left_trace hstress hpositive hsecond k left strength horder t ht
  · intro t ht
    exact rarefactionFan_middle_right_trace hstress hpositive hsecond k left strength horder t ht

/-- Every ordered p-system rarefaction fan is an entropy weak solution.

The fan satisfies the conservation law weakly and has zero production for
every compatible entropy pair, and not only for the mechanical entropy. -/
theorem isEntropyWeakSolution_rarefactionFan {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ)
    (horder : rarefactionSpeed stress k (left 0) ≤ rarefactionSpeed stress k (left 0 + strength)) :
    IsEntropyWeakSolution (flux stress) forwardHalfSpace
      (rarefactionFan stress k left strength) := by
  exact ⟨isWeakSolution_rarefactionFan hstress hpositive hsecond k left strength horder, fun E ↦
        satisfiesEntropyInequalityFor_rarefactionFan hstress hpositive hsecond E.toEntropyPair
          k left strength horder⟩

/-- A nonpositive family-zero rarefaction fan is a weak solution. -/
theorem isWeakSolution_rarefactionFan_zero_of_nonpos {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {strength : ℝ}
    (hstrength : strength ≤ 0) :
    IsWeakSolution (flux stress) forwardHalfSpace (rarefactionFan stress 0 left strength) := by
  apply isWeakSolution_rarefactionFan hstress hpositive hsecond 0 left strength
  exact rarefactionSpeed_zero_le_of_nonpos hstress hpositive hsecond left hstrength

/-- A nonpositive family-zero rarefaction fan satisfies every compatible
entropy inequality. -/
theorem satisfiesEntropyInequalityFor_rarefactionFan_zero_of_nonpos {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (E : EntropyPair (flux stress)) (left : ℝ^2)
    {strength : ℝ} (hstrength : strength ≤ 0) :
    SatisfiesEntropyInequalityFor forwardHalfSpace (rarefactionFan stress 0 left strength) E := by
  apply satisfiesEntropyInequalityFor_rarefactionFan hstress hpositive hsecond E 0 left strength
  exact rarefactionSpeed_zero_le_of_nonpos hstress hpositive hsecond left hstrength

/-- A nonpositive family-zero rarefaction fan is an entropy weak solution. -/
theorem isEntropyWeakSolution_rarefactionFan_zero_of_nonpos {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {strength : ℝ}
    (hstrength : strength ≤ 0) :
    IsEntropyWeakSolution (flux stress) forwardHalfSpace
      (rarefactionFan stress 0 left strength) := by
  apply isEntropyWeakSolution_rarefactionFan hstress hpositive hsecond 0 left strength
  exact rarefactionSpeed_zero_le_of_nonpos hstress hpositive hsecond left hstrength

/-- A nonnegative family-one rarefaction fan is a weak solution. -/
theorem isWeakSolution_rarefactionFan_one_of_nonneg {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2)
    {strength : ℝ} (hstrength : 0 ≤ strength) :
    IsWeakSolution (flux stress) forwardHalfSpace (rarefactionFan stress 1 left strength) := by
  apply isWeakSolution_rarefactionFan hstress hpositive hsecond 1 left strength
  exact rarefactionSpeed_one_le_of_nonneg hstress hpositive hsecond left hstrength

/-- A nonnegative family-one rarefaction fan satisfies every compatible
entropy inequality. -/
theorem satisfiesEntropyInequalityFor_rarefactionFan_one_of_nonneg {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (E : EntropyPair (flux stress)) (left : ℝ^2)
    {strength : ℝ} (hstrength : 0 ≤ strength) :
    SatisfiesEntropyInequalityFor forwardHalfSpace (rarefactionFan stress 1 left strength) E := by
  apply satisfiesEntropyInequalityFor_rarefactionFan hstress hpositive hsecond E 1 left strength
  exact rarefactionSpeed_one_le_of_nonneg hstress hpositive hsecond left hstrength

/-- A nonnegative family-one rarefaction fan is an entropy weak solution. -/
theorem isEntropyWeakSolution_rarefactionFan_one_of_nonneg {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {strength : ℝ}
    (hstrength : 0 ≤ strength) :
    IsEntropyWeakSolution (flux stress) forwardHalfSpace
      (rarefactionFan stress 1 left strength) := by
  apply isEntropyWeakSolution_rarefactionFan hstress hpositive hsecond 1 left strength
  exact rarefactionSpeed_one_le_of_nonneg hstress hpositive hsecond left hstrength

end PDE.Hyperbolic.ConservationLaw.System.PSystem
