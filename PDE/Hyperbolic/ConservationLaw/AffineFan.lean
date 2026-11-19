/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Geometry
public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm
import PDE.DistributionTheory.TestFunction
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Hyperbolic.ConservationLaw.AffineInterface.BoundaryIntegral
import PDE.Hyperbolic.ConservationLaw.AffineInterface.Trace

/-!
# Affine self-similar fans

We give the integration theorem behind piecewise smooth rarefaction
fans in one space dimension. An affine fan has a constant left state, a smooth
middle profile, and a constant right state, separated by the lines
`x = leftSpeed * t` and `x = rightSpeed * t`.

The middle state need not extend smoothly through either interface. It is
enough that its conserved quantity and flux are smooth for `t > 0`, satisfy
the conservation law there, and have the prescribed traces on both
interfaces. The boundary contributions then vanish because the adjacent
traces agree.

The half-space `leftHalfSpace s` is `{x < s t}` and `interface s t = (t, s t)`
parametrizes its boundary. Speeds enter only through these sets, so the fan
is defined on all of spacetime and the ordering `leftSpeed ≤ rightSpeed` is
used only when the three regions have to be disjoint on positive time.

`integral_conservative_pair_profile_eq_zero` gives the integral identity on `t > 0` for fans
such as the rarefaction wave (56) of Evans, §3.4.4, Theorem 4(ii). The fan is split as the
constant right state plus two half-space corrections,
`setIntegral_conservative_pair_add_residual_leftHalfSpace` turns each correction into an
interface trace, and the traces vanish because the middle state matches the outer constants
there (`hu_left`, `hq_left`, `hu_right`, `hq_right`). Nothing is assumed of the middle profile
beyond `C¹` on `t > 0` and conservation in `middleRegion`, so the theorem covers every fan with
matching traces.

## Main results

* `profile`: the three-region fan, with `profile_eq_left`, `profile_eq_middle`,
  `profile_eq_right` describing its regions.
* `setIntegral_conservative_pair_add_residual_leftHalfSpace`: integration by
  parts on `{x < speed t}` for a pair `(u, q)` that is `C¹` on `t > 0`, keeping
  the interior residual `uₜ + qₓ` and producing the boundary term
  `(q - speed · u)` times the interface trace of the test function.
* `integral_conservative_pair_profile_eq_zero`: a fan whose middle pair is
  conservative between the interfaces and matches the constant outer states
  along them is a weak conservative pair on `t > 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.4, Theorem 4(ii), equation (56); §3.4.1, Example 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.AffineFan

noncomputable section

open MeasureTheory
open PDE.Common
open TopologicalSpace

open scoped Distributions Topology

/-- The positive-time region between the two affine interfaces. -/
def middleRegion (leftSpeed rightSpeed : ℝ) : Set ℝ^2 :=
  forwardHalfSpace ∩
    (AffineInterface.leftHalfSpace rightSpeed \
      AffineInterface.leftHalfSpace leftSpeed)

/-- A three-region profile bounded by two affine interfaces.

The ordering of the speeds matters only on positive time. The definition is
total on spacetime so that it can be used directly as a coefficient in weak
integrals.
-/
def profile
    {E : Type*} (leftSpeed rightSpeed : ℝ) (leftValue : E)
    (middle : ℝ^2 → E) (rightValue : E) :
    ℝ^2 → E := by
  classical
  exact fun p ↦
    if p ∈ AffineInterface.leftHalfSpace leftSpeed then leftValue
    else if p ∈ AffineInterface.leftHalfSpace rightSpeed then middle p
    else rightValue

/-- Strictly to the left of the first interface, `x < leftSpeed * t`, the fan takes the left
state. -/
@[simp]
theorem profile_eq_left {E : Type*} {leftSpeed rightSpeed : ℝ} {leftValue rightValue : E}
    {middle : ℝ^2 → E} {p : ℝ^2} (hp : p ∈ AffineInterface.leftHalfSpace leftSpeed) :
    profile leftSpeed rightSpeed leftValue middle rightValue p = leftValue := by
  simp [profile, hp]

/-- Between the interfaces, `leftSpeed * t ≤ x < rightSpeed * t`, the fan takes the value of
the middle profile. -/
@[simp]
theorem profile_eq_middle {E : Type*} {leftSpeed rightSpeed : ℝ} {leftValue rightValue : E}
    {middle : ℝ^2 → E} {p : ℝ^2} (hleft : p ∉ AffineInterface.leftHalfSpace leftSpeed)
    (hright : p ∈ AffineInterface.leftHalfSpace rightSpeed) :
    profile leftSpeed rightSpeed leftValue middle rightValue p = middle p := by
  simp [profile, hleft, hright]

/-- On and to the right of the second interface, `rightSpeed * t ≤ x`, and not strictly left of
the first, the fan takes the right state. -/
@[simp]
theorem profile_eq_right {E : Type*} {leftSpeed rightSpeed : ℝ} {leftValue rightValue : E}
    {middle : ℝ^2 → E} {p : ℝ^2} (hleft : p ∉ AffineInterface.leftHalfSpace leftSpeed)
    (hright : p ∉ AffineInterface.leftHalfSpace rightSpeed) :
    profile leftSpeed rightSpeed leftValue middle rightValue p = rightValue := by
  simp [profile, hleft, hright]

/-- Applying a map to a fan transforms each of its three profiles. -/
theorem comp_profile {E F : Type*} (g : E → F) (leftSpeed rightSpeed : ℝ) (leftValue rightValue : E)
    (middle : ℝ^2 → E) (p : ℝ^2) :
    g (profile leftSpeed rightSpeed leftValue middle rightValue p) =
      profile leftSpeed rightSpeed (g leftValue) (fun x ↦ g (middle x)) (g rightValue) p := by
  classical
  unfold profile
  split_ifs <;> rfl

/-- An affine fan is invariant under positive spacetime dilation whenever its
middle profile is. -/
theorem profile_smul_of_pos {E : Type*} {a : ℝ} (ha : 0 < a) (leftSpeed rightSpeed : ℝ)
    (leftValue rightValue : E) (middle : ℝ^2 → E) (hmiddle : ∀ p, middle (a • p) = middle p)
    (p : ℝ^2) :
    profile leftSpeed rightSpeed leftValue middle rightValue (a • p) =
      profile leftSpeed rightSpeed leftValue middle rightValue p := by
  by_cases hleft : p ∈ AffineInterface.leftHalfSpace leftSpeed
  · have hleftScaled : a • p ∈ AffineInterface.leftHalfSpace leftSpeed :=
      (AffineInterface.smul_mem_leftHalfSpace_iff ha p).2 hleft
    rw [profile_eq_left hleftScaled, profile_eq_left hleft]
  · have hleftScaled : a • p ∉ AffineInterface.leftHalfSpace leftSpeed :=
      fun hmem ↦ hleft <| (AffineInterface.smul_mem_leftHalfSpace_iff ha p).1 hmem
    by_cases hright : p ∈ AffineInterface.leftHalfSpace rightSpeed
    · have hrightScaled : a • p ∈ AffineInterface.leftHalfSpace rightSpeed :=
        (AffineInterface.smul_mem_leftHalfSpace_iff ha p).2 hright
      rw [profile_eq_middle hleftScaled hrightScaled, profile_eq_middle hleft hright, hmiddle p]
    · have hrightScaled : a • p ∉ AffineInterface.leftHalfSpace rightSpeed := fun hmem ↦ hright <|
          (AffineInterface.smul_mem_leftHalfSpace_iff ha p).1 hmem
      rw [profile_eq_right hleftScaled hrightScaled, profile_eq_right hleft hright]

/-- Integration by parts for a smooth pair on an affine half-space.

The coefficient functions need regularity only on `t > 0`, since the test
function and all its derivatives vanish outside that open set. The interior
residual is retained explicitly; conservative pairs are obtained as a
corollary.
-/
theorem setIntegral_conservative_pair_add_residual_leftHalfSpace (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    (speed : ℝ) (u q : ℝ^2 → ℝ) (hu : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 u p)
    (hq : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 q p) (uTrace qTrace : ℝ)
    (hu_interface : ∀ t : ℝ, 0 < t → u (AffineInterface.interface speed t) = uTrace)
    (hq_interface : ∀ t : ℝ, 0 < t → q (AffineInterface.interface speed t) = qTrace) :
    (∫ p in AffineInterface.leftHalfSpace speed,
        (u p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
          q p * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
          φ p *
            ((∂[(0 : Fin 2)] u) p +
              (∂[(1 : Fin 2)] q) p)) ∂volume) =
      (qTrace - speed * uTrace) *
        ∫ t : ℝ, φ (AffineInterface.interface speed t) ∂volume := by
  let mulφ (w : ℝ^2 → ℝ) (hw : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 w p) :
      𝓓^{1}((⊤ : Opens ℝ^2), ℝ) :=
    TestFunction.monoCLM ℝ (TestFunction.mulLeft w φ fun p hp ↦ hw p (φ.tsupport_subset hp))
  have hmul {w : ℝ^2 → ℝ} (hw : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 w p) (i : Fin 2) (p : ℝ^2) :
      (∂[i] (mulφ w hw : ℝ^2 → ℝ)) p = w p * (∂[i] (φ : ℝ^2 → ℝ)) p + φ p * (∂[i] w) p := by
    by_cases hp : p ∈ forwardHalfSpace
    · simpa [mulφ] using TestFunction.partialDeriv_mulLeft w φ
        (fun y hy ↦ hw y (φ.tsupport_subset hy)) i (hw p hp).differentiableAt_one
    · simpa [mulφ, φ.zero_on_compl hp, φ.partialDeriv_eq_zero_of_notMem hp] using
        (TestFunction.mulLeft w φ fun y hy ↦
          hw y (φ.tsupport_subset hy)).partialDeriv_eq_zero_of_notMem hp i
  have hline (t : ℝ) : -speed * mulφ u hu (AffineInterface.interface speed t) +
          mulφ q hq (AffineInterface.interface speed t) =
        (qTrace - speed * uTrace) * φ (AffineInterface.interface speed t) := by
    by_cases ht : 0 < t
    · simp only [mulφ, TestFunction.monoCLM_apply, le_refl, le_top, and_self, ↓reduceIte,
        TestFunction.mulLeft_apply, hu_interface t ht, hq_interface t ht]
      ring
    · simp [mulφ, φ.zero_on_compl (show AffineInterface.interface speed t ∉ forwardHalfSpace by
        simpa [forwardHalfSpace] using ht)]
  have htrace (w : ℝ^2 → ℝ) (hw : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 w p) :=
    AffineInterface.integrable_interface_trace (mulφ w hw) speed
  calc
    _ = ∫ p in AffineInterface.leftHalfSpace speed, ((∂[(0 : Fin 2)] (mulφ u hu : ℝ^2 → ℝ)) p +
            (∂[(1 : Fin 2)] (mulφ q hq : ℝ^2 → ℝ)) p) :=
      integral_congr_ae (.of_forall fun p ↦ by simp only [hmul]; ring)
    _ = -speed * (∫ t, mulφ u hu (AffineInterface.interface speed t)) +
          ∫ t, mulφ q hq (AffineInterface.interface speed t) := by
      rw [integral_add ((mulφ u hu).integrable_partialDeriv 0).integrableOn
        ((mulφ q hq).integrable_partialDeriv 1).integrableOn]
      congr 1
      · simpa using AffineInterface.setIntegral_linearCombination_partialDeriv_leftHalfSpace
          (mulφ u hu) speed 1 0
      · simpa using AffineInterface.setIntegral_linearCombination_partialDeriv_leftHalfSpace
          (mulφ q hq) speed 0 1
    _ = _ := by
      rw [← integral_const_mul, ← integral_add ((htrace u hu).const_mul _) (htrace q hq)]
      simp_rw [hline]
      exact integral_const_mul _ _

/-- A smooth conservative pair on positive time contributes only its
affine-interface trace. -/
theorem setIntegral_conservative_pair_leftHalfSpace (φ : 𝓓^{1}(forwardHalfSpace, ℝ)) (speed : ℝ)
    (u q : ℝ^2 → ℝ) (hu : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 u p)
    (hq : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 q p)
    (hconservation : ∀ p ∈ forwardHalfSpace, (∂[(0 : Fin 2)] u) p + (∂[(1 : Fin 2)] q) p = 0)
    (uTrace qTrace : ℝ)
    (hu_interface : ∀ t : ℝ, 0 < t → u (AffineInterface.interface speed t) = uTrace)
    (hq_interface : ∀ t : ℝ, 0 < t → q (AffineInterface.interface speed t) = qTrace) :
    (∫ p in AffineInterface.leftHalfSpace speed, (u p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p + q p *
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) = (qTrace - speed * uTrace) * ∫ t : ℝ,
      φ (AffineInterface.interface speed t) ∂volume := by
  have hboundary := setIntegral_conservative_pair_add_residual_leftHalfSpace
      φ speed u q hu hq uTrace qTrace hu_interface hq_interface
  have hresidual (p : ℝ^2) : φ p * ((∂[(0 : Fin 2)] u) p +
            (∂[(1 : Fin 2)] q) p) = 0 := by
    by_cases hp : p ∈ forwardHalfSpace
    · simp [hconservation p hp]
    · simp [φ.zero_on_compl hp]
  simpa only [hresidual, add_zero] using hboundary

/-- The half-space correction of a pair that is `C¹` on positive time and vanishes on the
interface `speed`: it is integrable, and its integral over the half-space is zero. -/
private theorem integrable_correction_and_integral_eq_zero (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    (speed : ℝ) {u q : ℝ^2 → ℝ} (hu : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 u p)
    (hq : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 q p)
    (hu_interface : ∀ t : ℝ, 0 < t → u (AffineInterface.interface speed t) = 0)
    (hq_interface : ∀ t : ℝ, 0 < t → q (AffineInterface.interface speed t) = 0) :
    Integrable ((AffineInterface.leftHalfSpace speed).indicator fun p ↦
      u p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p + q p * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
        φ p * ((∂[(0 : Fin 2)] u) p + (∂[(1 : Fin 2)] q) p)) ∧
    ∫ p, (AffineInterface.leftHalfSpace speed).indicator (fun p ↦
      u p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p + q p * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
        φ p * ((∂[(0 : Fin 2)] u) p + (∂[(1 : Fin 2)] q) p)) p = 0 := by
  have hlocal {w : ℝ^2 → ℝ} (hw : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 w p) :
      LocallyIntegrableOn w forwardHalfSpace volume :=
    ContinuousOn.locallyIntegrableOn (fun p hp ↦ (hw p hp).continuousAt.continuousWithinAt)
      forwardHalfSpace.isOpen.measurableSet
  have hmeas := AffineInterface.measurableSet_leftHalfSpace speed
  refine ⟨Integrable.indicator ?_ hmeas, ?_⟩
  · refine (((φ.integrable_mul_partialDeriv (hlocal hu) 0).add
      (φ.integrable_mul_partialDeriv (hlocal hq) 1)).add
      ((φ.integrable_mul_partialDeriv_of_contDiffAt hu 0).add
        (φ.integrable_mul_partialDeriv_of_contDiffAt hq 1))).congr (.of_forall fun p ↦ ?_)
    simp only [Pi.add_apply]
    ring
  · simpa [integral_indicator hmeas] using
      setIntegral_conservative_pair_add_residual_leftHalfSpace φ speed u q hu hq 0 0
        hu_interface hq_interface

/-- Matching traces and conservation between the interfaces produce a global
weak conservative pair across an ordered affine fan.

The middle pair is required to be `C¹` on positive time, but it need only
satisfy the conservation law in `middleRegion`. The two half-space corrections
retain their residuals: these cancel to the left of the fan and vanish inside
the fan.
-/
theorem integral_conservative_pair_profile_eq_zero (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    (leftSpeed rightSpeed : ℝ) (hspeed : leftSpeed ≤ rightSpeed) (u q : ℝ^2 → ℝ)
    (uLeft qLeft uRight qRight : ℝ) (hu : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 u p)
    (hq : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 q p)
    (hconservation : ∀ p ∈ middleRegion leftSpeed rightSpeed,
      (∂[(0 : Fin 2)] u) p + (∂[(1 : Fin 2)] q) p = 0)
    (hu_left : ∀ t : ℝ, 0 < t → u (AffineInterface.interface leftSpeed t) = uLeft)
    (hq_left : ∀ t : ℝ, 0 < t → q (AffineInterface.interface leftSpeed t) = qLeft)
    (hu_right : ∀ t : ℝ, 0 < t → u (AffineInterface.interface rightSpeed t) = uRight)
    (hq_right : ∀ t : ℝ, 0 < t → q (AffineInterface.interface rightSpeed t) = qRight) :
    (∫ p : ℝ^2, (profile leftSpeed rightSpeed uLeft u uRight p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
      profile leftSpeed rightSpeed qLeft q qRight p * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) =
      0 := by
  classical
  obtain ⟨hrightIntegrable, hrightIntegral⟩ :=
    integrable_correction_and_integral_eq_zero φ rightSpeed
      (u := fun p ↦ u p - uRight) (q := fun p ↦ q p - qRight)
      (fun p hp ↦ (hu p hp).sub contDiffAt_const) (fun p hp ↦ (hq p hp).sub contDiffAt_const)
      (fun t ht ↦ by simp [hu_right t ht]) (fun t ht ↦ by simp [hq_right t ht])
  obtain ⟨hleftIntegrable, hleftIntegral⟩ := integrable_correction_and_integral_eq_zero φ leftSpeed
      (u := fun p ↦ uLeft - u p) (q := fun p ↦ qLeft - q p)
      (fun p hp ↦ contDiffAt_const.sub (hu p hp)) (fun p hp ↦ contDiffAt_const.sub (hq p hp))
      (fun t ht ↦ by simp [hu_left t ht]) (fun t ht ↦ by simp [hq_left t ht])
  have htime := (φ.integrable_partialDeriv (0 : Fin 2)).const_mul uRight
  have hspace := (φ.integrable_partialDeriv (1 : Fin 2)).const_mul qRight
  have hzero (i : Fin 2) : ∫ p : ℝ^2, (∂[i] (φ : ℝ^2 → ℝ)) p = 0 := by
    simpa using (TestFunction.monoCLM ℝ φ :
      𝓓^{1}((⊤ : Opens ℝ^2), ℝ)).integral_partialDeriv_eq_zero i
  have hsum := integral_add ((htime.add hspace).add hrightIntegrable) hleftIntegrable
  rw [integral_add' (htime.add hspace) hrightIntegrable, integral_add' htime hspace,
    integral_const_mul, integral_const_mul, hzero, hzero, hrightIntegral, hleftIntegral] at hsum
  refine (integral_congr_ae (.of_forall fun p ↦ ?_)).trans (hsum.trans (by ring))
  by_cases hp : p ∈ forwardHalfSpace
  swap
  · simp [Set.indicator, φ.partialDeriv_eq_zero_of_notMem hp, φ.zero_on_compl hp]
  have hsub (i : Fin 2) (w : ℝ^2 → ℝ) (c : ℝ) : (∂[i] fun p ↦ w p - c) p = (∂[i] w) p := by
    simp [partialDeriv, fderiv_sub_const]
  have hcsub (i : Fin 2) (w : ℝ^2 → ℝ) (c : ℝ) : (∂[i] fun p ↦ c - w p) p = -(∂[i] w) p := by
    simp [partialDeriv, fderiv_const_sub]
  simp only [Pi.add_apply, Set.indicator_apply, hsub, hcsub]
  by_cases hleft : p ∈ AffineInterface.leftHalfSpace leftSpeed
  · have hright : p ∈ AffineInterface.leftHalfSpace rightSpeed :=
      lt_of_lt_of_le hleft (mul_le_mul_of_nonneg_right hspeed (le_of_lt hp))
    simp only [profile_eq_left hleft, hleft, hright, ↓reduceIte]
    ring
  · by_cases hright : p ∈ AffineInterface.leftHalfSpace rightSpeed
    · simp only [profile_eq_middle hleft hright, hleft, hright, ↓reduceIte]
      linear_combination -φ p * hconservation p ⟨hp, hright, hleft⟩
    · simp only [profile_eq_right hleft hright, hleft, hright, ↓reduceIte]
      ring

end

end PDE.Hyperbolic.ConservationLaw.AffineFan
