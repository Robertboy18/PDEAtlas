/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Regularity
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Return
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Switch.Monotonicity
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Denominator

/-!
# A prescribed clock with the lower equation `g - 4 - 4 * cutoff`

The added term uses the same squared-state outer transition as `clockFeedback`.
It vanishes along the common clock up to its descending 205 crossing: the outer
transition is zero before the switch, and the cutoff is zero during the remaining
comparison interval. Global Lipschitz existence and interval uniqueness therefore
extend that same trajectory by the prescribed lower equation.

A separate barrier and first-hit argument constructs the new terminal zero.
The field contains no signed gate.

-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.NormalizedPulse
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- The outer transition already occurring in the squared-state feedback.
Here `a` and `b` are fast-coordinate thresholds, not gate coefficients. -/
def outerTransition (a b z : ℝ) : ℝ :=
  transition ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))

/-- A smooth field independent of the signed gate. -/
def prescribedClockField (a b z y : ℝ) : ℝ :=
  g y + clockFeedback a b z - 4 * cutoff y * outerTransition a b z

/-- The autonomous field after the outer switch has finished. -/
def lowerClockField (y : ℝ) : ℝ := g y - 4 - 4 * cutoff y

/-- Smoothness in the fast coordinate does not require division by a variable. -/
theorem contDiff_outerTransition (a b : ℝ) : ContDiff ℝ ∞ (outerTransition a b) :=
  contDiff_transition.comp (((contDiff_id.pow 2).sub contDiff_const).div_const (b ^ 2 - a ^ 2))

/-- The correction multiplier lies between zero and one. -/
theorem outerTransition_mem_Icc (a b z : ℝ) : outerTransition a b z ∈ Icc 0 1 :=
  ⟨transition_nonneg _, transition_le_one _⟩

/-- At and before the inner squared threshold, the added term is switched off. -/
theorem outerTransition_of_sq_le {a b z : ℝ}
    (hab : a ^ 2 < b ^ 2) (hz : z ^ 2 ≤ a ^ 2) : outerTransition a b z = 0 :=
  transition_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) (sub_pos.mpr hab).le)

/-- At and after the outer squared threshold, the added term is fully switched on. -/
theorem outerTransition_of_le_sq {a b z : ℝ}
    (hab : a ^ 2 < b ^ 2) (hz : b ^ 2 ≤ z ^ 2) : outerTransition a b z = 1 := by
  apply transition_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hab)).2
  linarith only [hz]

/-- The surrogate field is jointly smooth in its two state coordinates. -/
theorem contDiff_prescribedClockField (a b : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ prescribedClockField a b p.1 p.2) :=
  ((contDiff_g.comp contDiff_snd).add ((contDiff_clockFeedback a b).comp contDiff_fst)).sub
    ((contDiff_const.mul (contDiff_cutoff.comp contDiff_snd)).mul
      ((contDiff_outerTransition a b).comp contDiff_fst))

/-- The ordinary state derivative retains the full factor four. -/
theorem hasDerivAt_prescribedClockField (a b z y : ℝ) :
    HasDerivAt (prescribedClockField a b z)
      (deriv g y - 4 * deriv cutoff y * outerTransition a b z) y :=
  ((hasDerivAt_g y).differentiableAt.hasDerivAt.add_const _).sub
    (((hasDerivAt_cutoff y).differentiableAt.hasDerivAt.const_mul 4).mul_const _)

/-- A uniform global state Lipschitz constant, independent of the fast path and thresholds. -/
theorem lipschitzWith_prescribedClockField (a b z : ℝ) :
    LipschitzWith (361 / 4000) (prescribedClockField a b z) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun y ↦ (hasDerivAt_prescribedClockField a b z y).differentiableAt) fun y ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    (hasDerivAt_prescribedClockField a b z y).deriv]
  change |deriv g y - 4 * deriv cutoff y * outerTransition a b z| ≤ (361 / 4000 : ℝ)
  have hg := abs_le.mp (abs_deriv_g_le y)
  have ho := outerTransition_mem_Icc a b z
  have hpLower := mul_le_mul_of_nonneg_right (neg_one_div_le_deriv_cutoff y) ho.1
  have hpUpper := mul_nonpos_of_nonpos_of_nonneg (deriv_cutoff_nonpos y) ho.1
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith only [hg.1, hg.2, ho.2, hpLower, hpUpper]

/-- The nonautonomous existence theorem constructs a global surrogate
through any state. -/
theorem exists_prescribed_clock {Z : ℝ → ℝ} (hZ : Continuous Z) (a b t₀ y₀ : ℝ) :
    ∃ X : ℝ → ℝ, X t₀ = y₀ ∧ ∀ t, HasDerivAt X (prescribedClockField a b (Z t) (X t)) t := by
  have hF : Continuous (fun p : ℝ × ℝ ↦ prescribedClockField a b (Z p.1) p.2) :=
    (contDiff_prescribedClockField a b).continuous.comp
      ((hZ.comp continuous_fst).prodMk continuous_snd)
  exact PDE.Analysis.Evolution.exists_eq_hasDerivAt_of_lipschitz hF
    (fun t ↦ lipschitzWith_prescribedClockField a b (Z t)) t₀ y₀

/-- Smoothness of the fast solution follows from its equation. -/
theorem contDiff_fast_clock {δ : ℝ} {Z : ℝ → ℝ}
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) : ContDiff ℝ ∞ Z :=
  contDiffOn_univ.mp <| PDE.Analysis.Evolution.contDiffOn_of_hasDerivAt (n := ⊤)
    (f := fun _ z ↦ fastLogCosh δ z) isOpen_univ
    ((contDiff_fastLogCosh δ).comp contDiff_snd).contDiffOn (fun t _ ↦ hZ t)

/-- A smooth fast path makes the constructed surrogate smooth in time.
The proof uses the general regularity theorem for integral curves. -/
theorem contDiff_prescribed_clock {X Z : ℝ → ℝ} {a b : ℝ} (hZ : ContDiff ℝ ∞ Z)
    (hX : ∀ t, HasDerivAt X (prescribedClockField a b (Z t) (X t)) t) :
    ContDiff ℝ ∞ X :=
  contDiffOn_univ.mp <| PDE.Analysis.Evolution.contDiffOn_of_hasDerivAt (n := ⊤)
    (f := fun t y ↦ prescribedClockField a b (Z t) y) isOpen_univ
    ((contDiff_prescribedClockField a b).comp
      ((hZ.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn (fun t _ ↦ hX t)

/-- At every level at least 205 the ordinary derivative has the common-clock formula.
This also applies at the endpoint of the comparison interval. -/
theorem hasDerivAt_eq_common_of_ge {X : ℝ → ℝ} {a b z t : ℝ}
    (hX : HasDerivAt X (prescribedClockField a b z (X t)) t) (hy : 205 ≤ X t) :
    HasDerivAt X (g (X t) + clockFeedback a b z) t := by
  simpa only [prescribedClockField, cutoff_of_ge hy, mul_zero, zero_mul, sub_zero] using hX

/-- Once the outer threshold is passed, both feedback terms have their prescribed values. -/
theorem prescribedClockField_eq_lower {a b z : ℝ}
    (hab : a ^ 2 < b ^ 2) (hz : b ^ 2 ≤ z ^ 2) (y : ℝ) :
    prescribedClockField a b z y = lowerClockField y := by
  simp only [prescribedClockField, lowerClockField, clockFeedback_of_le_sq hab hz,
    outerTransition_of_le_sq hab hz, mul_one, sub_eq_add_neg]

/-- Along the unprescribed clock the correction is zero through the descending 205 hit,
including both endpoints. This is a scalar identity, not coupled-family agreement. -/
theorem prescribedClockField_eq_common_on {Y Z : ℝ → ℝ} {T τ205 : ℝ}
    (hZsq : MonotoneOn (fun t ↦ Z t ^ 2) (Ici 0)) (hT : 0 ≤ T) (hsq : Z T ^ 2 < Z (T + 1 / 2) ^ 2)
    (hhit : Y τ205 = 205) (hbefore : ∀ t ∈ Ico T τ205, 205 < Y t) :
    ∀ t ∈ Icc 0 τ205, prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) (Y t) =
      g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t) := by
  intro t ht
  by_cases htT : t ≤ T
  · simp only [prescribedClockField, outerTransition_of_sq_le hsq (hZsq ht.1 hT htT), mul_zero,
      sub_zero]
  · have hy : 205 ≤ Y t := by
      rcases ht.2.lt_or_eq with hlt | rfl
      · exact (hbefore t ⟨(lt_of_not_ge htT).le, hlt⟩).le
      · exact hhit.ge
    simp only [prescribedClockField, cutoff_of_ge hy, mul_zero, zero_mul, sub_zero]

/-- Reuse any given common clock, rather than selecting new common-clock witnesses. -/
theorem exists_prescribed_clock_eqOn_common {Y Z : ℝ → ℝ} {T τ205 : ℝ} (hZ : Continuous Z)
    (hZsq : MonotoneOn (fun t ↦ Z t ^ 2) (Ici 0)) (hT : 0 ≤ T) (hsq : Z T ^ 2 < Z (T + 1 / 2) ^ 2)
    (hYzero : Y 0 = 0)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hhit : Y τ205 = 205) (hbefore : ∀ t ∈ Ico T τ205, 205 < Y t) :
    ∃ X : ℝ → ℝ, X 0 = 0 ∧
      (∀ t, HasDerivAt X (prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) (X t)) t) ∧
      EqOn X Y (Icc 0 τ205) := by
  obtain ⟨X, hXzero, hX⟩ := exists_prescribed_clock hZ (Z T) (Z (T + 1 / 2)) 0 0
  have hXd : Differentiable ℝ X := fun t ↦ (hX t).differentiableAt
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  refine ⟨X, hXzero, hX, ODE_solution_unique
    (v := fun t y ↦ prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) y)
    (fun t ↦ lipschitzWith_prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t))
    hXd.continuous.continuousOn (fun t _ ↦ (hX t).hasDerivWithinAt)
    hYd.continuous.continuousOn (fun t ht ↦ ?_) (hXzero.trans hYzero.symm)⟩
  rw [prescribedClockField_eq_common_on hZsq hT hsq hhit hbefore t ⟨ht.1, ht.2.le⟩]
  exact (hY t).hasDerivWithinAt

/-- The lower field is uniformly negative throughout the nonnegative clock range. -/
theorem lowerClockField_lt {y : ℝ} (hy0 : 0 ≤ y) (hy210 : y ≤ 210) :
    lowerClockField y < -(13 / 5) := by
  unfold lowerClockField
  linarith only [MiddleClock.thirteen_fifths_lt_lower_denominator hy0 hy210]

/-- At zero the two negative plateau contributions add to minus eight. -/
theorem lowerClockField_zero : lowerClockField 0 = -8 := by
  rw [lowerClockField, g_zero, cutoff_of_le (by norm_num : (0 : ℝ) ≤ 100)]
  norm_num

/-- A new first zero is forced after the descending 205 hit. -/
theorem exists_first_lower_zero {X : ℝ → ℝ} {A : ℝ} (hXd : Differentiable ℝ X)
    (hX : ∀ t ≥ A, HasDerivAt X (lowerClockField (X t)) t) (hstart : X A = 205) :
    ∃ τ ∈ Ioc A (A + 205 / 2), X τ = 0 ∧ (∀ t ∈ Ico A τ, 0 < X t) ∧ StrictAntiOn X (Icc A τ) ∧
      HasDerivAt X (-8) τ := by
  have hupper (t : ℝ) (ht : A ≤ t) : X t ≤ 205 :=
    image_le_of_deriv_right_lt_deriv_boundary (f := X) (f' := fun t ↦ lowerClockField (X t))
      (B := fun _ : ℝ ↦ 205) (B' := fun _ ↦ 0) (a := A) (b := t)
      hXd.continuous.continuousOn (fun s hs ↦ (hX s hs.1).hasDerivWithinAt) hstart.le
      (fun s ↦ hasDerivAt_const s (205 : ℝ)) (fun s _ heq ↦ by
        rw [heq]
        linarith only [lowerClockField_lt (y := 205) (by norm_num) (by norm_num)]) ⟨ht, le_rfl⟩
  have hneg (t : ℝ) (ht : A ≤ t) (hpos : 0 < X t) : deriv X t < -2 := by
    rw [(hX t ht).deriv]
    linarith only [lowerClockField_lt hpos.le (by linarith only [hupper t ht])]
  have hAL : A < A + 205 / 2 := by linarith
  have hex : ∃ t ∈ Icc A (A + 205 / 2), X t ≤ 0 := by
    by_contra! habove
    have hmean := (convex_Icc A (A + 205 / 2)).image_sub_lt_mul_sub_of_deriv_lt
      hXd.continuous.continuousOn hXd.differentiableOn
      (fun t ht ↦ hneg t (interior_subset ht).1 (habove t (interior_subset ht)))
      A ⟨le_rfl, hAL.le⟩ _ ⟨hAL.le, le_rfl⟩ hAL
    linarith only [hmean, hstart, habove _ ⟨hAL.le, le_rfl⟩]
  obtain ⟨τ, hτ, hmin⟩ := (isCompact_Icc.inter_right
    (isClosed_le hXd.continuous continuous_const)).exists_isMinOn hex
    (f := fun t : ℝ ↦ t) continuous_id.continuousOn
  have hτA : A < τ := hτ.1.1.lt_of_ne fun h ↦ by
    linarith only [show X τ ≤ 0 from hτ.2, h ▸ hstart]
  have hhit : X τ = 0 := by
    obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc' hτA.le hXd.continuous.continuousOn
      (show (0 : ℝ) ∈ Icc (X τ) (X A) from ⟨hτ.2, by rw [hstart]; norm_num⟩)
    rwa [← le_antisymm hs.2 (isMinOn_iff.mp hmin s ⟨⟨hs.1, hs.2.trans hτ.1.2⟩, hxs.le⟩)]
  have hbefore (t : ℝ) (ht : t ∈ Ico A τ) : 0 < X t := not_le.mp fun h ↦
    (isMinOn_iff.mp hmin t ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, h⟩).not_gt ht.2
  refine ⟨τ, ⟨hτA, hτ.1.2⟩, hhit, hbefore, strictAntiOn_of_deriv_neg (convex_Icc A τ)
    hXd.continuous.continuousOn fun t ht ↦ ?_, ?_⟩
  · rw [interior_Icc] at ht
    exact (hneg t ht.1.le (hbefore t ⟨ht.1.le, ht.2⟩)).trans (by norm_num)
  · simpa only [hhit, lowerClockField_zero] using hX τ hτA.le

/-- Construct the lower return for supplied trajectories `Y`, `Z`, a switch time `T`,
and their descending 205 crossing. The trajectory is preserved up to
that crossing. -/
theorem exists_prescribed_clock_lower_return {δ : ℝ} {Y Z : ℝ → ℝ} {T τ205 : ℝ} (hδ : |δ| < 1 / 4)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hT : 1 ≤ T) (hYzero : Y 0 = 0)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hτ205 : T + 1 / 2 < τ205) (hhit205 : Y τ205 = 205) (hbefore205 : ∀ t ∈ Ico T τ205, 205 < Y t) :
    ∃ (X : ℝ → ℝ) (τ0 : ℝ), X 0 = 0 ∧
      (∀ t, HasDerivAt X
        (prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) (X t)) t) ∧
      EqOn X Y (Icc 0 τ205) ∧
      (∀ t ≥ T + 1 / 2, HasDerivAt X (lowerClockField (X t)) t) ∧
      τ0 ∈ Ioc τ205 (τ205 + 205 / 2) ∧ X τ0 = 0 ∧
      (∀ t ∈ Ico T τ0, 0 < X t) ∧ StrictAntiOn X (Icc τ205 τ0) ∧
      HasDerivAt X (-8) τ0 := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hS0 : 0 ≤ T + 1 / 2 := by linarith only [hT]
  have hτ205zero : 0 ≤ τ205 := hS0.trans hτ205.le
  have hZsq := (ClockSwitch.strictMonoOn_fast_clock_sq hδ hZ hZlower).monotoneOn
  have hsq := (ClockSwitch.feedback_switch_properties hδ hZ hZlower hT).1
  have hZd : Differentiable ℝ Z := fun t ↦ (hZ t).differentiableAt
  obtain ⟨X, hXzero, hX, heq⟩ := exists_prescribed_clock_eqOn_common
    hZd.continuous hZsq hT0 hsq hYzero hY hhit205 hbefore205
  have hpost (t : ℝ) (ht : T + 1 / 2 ≤ t) : HasDerivAt X (lowerClockField (X t)) t := by
    simpa only [prescribedClockField_eq_lower hsq (hZsq hS0 (hS0.trans ht) ht)] using hX t
  have hX205 : X τ205 = 205 := (heq ⟨hτ205zero, le_rfl⟩).trans hhit205
  obtain ⟨τ0, hτ0, hzero, hpositive, hanti, hd0⟩ := exists_first_lower_zero
    (fun t ↦ (hX t).differentiableAt) (fun t ht ↦ hpost t (hτ205.le.trans ht)) hX205
  refine ⟨X, τ0, hXzero, hX, heq, hpost, hτ0, hzero, fun t ht ↦ ?_, hanti, hd0⟩
  by_cases hlt : t < τ205
  · rw [heq ⟨hT0.trans ht.1, hlt.le⟩]
    linarith only [hbefore205 t ⟨ht.1, hlt⟩]
  · exact hpositive t ⟨le_of_not_gt hlt, ht.2⟩

/-- The prescribed clock with linear fast coordinate `Z' = 2Z`, `Z 0 = 1`, starting from
`X 0 = 0`. It first reaches `415/2` at `T ∈ (1, 417/2]`, descends through `205` at `τ205`,
and reaches zero at `τ0 ∈ (τ205, τ205 + 205/2]` with derivative `-8`, staying positive on
`[T, τ0)`. -/
theorem exists_linear_fast_prescribed_clock :
    ∃ (X Z : ℝ → ℝ) (T τ205 τ0 : ℝ), X 0 = 0 ∧ Z 0 = 1 ∧
      (∀ t, HasDerivAt Z (2 * Z t) t) ∧
      (∀ t, 0 ≤ t → 1 + t ≤ Z t) ∧ T ∈ Ioc 1 (417 / 2) ∧
      Z T ^ 2 < Z (T + 1 / 2) ^ 2 ∧
      (∀ t, HasDerivAt X
        (prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) (X t)) t) ∧
      X T = 415 / 2 ∧ (∀ t ∈ Ico 0 T, X t < 415 / 2) ∧
      T + 1 / 2 < τ205 ∧ X τ205 = 205 ∧
      (∀ t ∈ Ico T τ205, 205 < X t) ∧
      (∀ t ≥ T + 1 / 2, HasDerivAt X (lowerClockField (X t)) t) ∧
      τ0 ∈ Ioc τ205 (τ205 + 205 / 2) ∧ X τ0 = 0 ∧
      (∀ t ∈ Ico T τ0, 0 < X t) ∧ StrictAntiOn X (Icc τ205 τ0) ∧
      HasDerivAt X (-8) τ0 := by
  have hδ : |(0 : ℝ)| < 1 / 4 := by norm_num
  obtain ⟨Y, Z, T, τ205, _τOld, hYzero, hZzero, hZ, hY, hZlower,
    hT, hYT, hbeforeT, _hdT, _hvT, hsq, _hoff, _hband, hτ205, _hOldOrder,
    hhit205, _hOldZero, hbefore205, _hOldPositive, _hd205, _hv205, _hdOld⟩ :=
    ClockSwitch.exists_clock_upward_and_return hδ
  obtain ⟨X, τ0, hXzero, hX, heq, hpost, hτ0, hzero, hpositive, hanti, hd0⟩ :=
    exists_prescribed_clock_lower_return hδ hZ hZlower hT.1.le hYzero hY hτ205 hhit205 hbefore205
  have hT0 : 0 ≤ T := by linarith only [hT.1]
  have hT205 : T ≤ τ205 := by linarith only [hτ205]
  have hτ205zero : 0 ≤ τ205 := hT0.trans hT205
  refine ⟨X, Z, T, τ205, τ0, hXzero, hZzero,
    fun t ↦ by simpa only [fastLogCosh, zero_mul, add_zero] using hZ t, hZlower, hT, hsq, hX,
    (heq ⟨hT0, hT205⟩).trans hYT, fun t ht ↦ (heq ⟨ht.1, ht.2.le.trans hT205⟩).trans_lt
      (hbeforeT t ht), hτ205, (heq ⟨hτ205zero, le_rfl⟩).trans hhit205,
    fun t ht ↦ (hbefore205 t ht).trans_eq (heq ⟨hT0.trans ht.1, ht.2.le⟩).symm, hpost, hτ0,
    hzero, hpositive, hanti, hd0⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
