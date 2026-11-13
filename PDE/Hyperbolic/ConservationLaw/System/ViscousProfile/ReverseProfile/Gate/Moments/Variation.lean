/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.ParameterRegularity

import CAS.ExactTactic

/-!
# Signed gate moments of the prescribed clock weights

The moment is the whole-line integral of the parameterized weights
against one fixed, possibly signed smooth function supported inside the gate.
Local smoothness of the supplied event maps gives a common neighborhood for
both weights. The local integration theorem then differentiates the moment.

The lower primitive retains its full cutoff. The speed coefficient is the
event-derived constant; displacement retains the derivative
of the same event gap.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights

/-- The whole-line signed gate moment of the weight family. -/
def prescribedClockWeightMoment (b : ℝ → ℝ) (L Bhit : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ∫ y : ℝ, b y *
    ((parameterizedClockPassageData L Bhit p).wMinus y +
      (parameterizedClockPassageData L Bhit p).wPlus y)

variable {b : ℝ → ℝ} {L Bhit : ℝ × ℝ → ℝ}

/-- The support removes the endpoints from the pointwise derivative calculation.
The closed gate remains the domain of the shared integration theorem. -/
private theorem prescribedClockWeightMoment_direction {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h0 : (0, 0) ∈ U) (hb : ContDiff ℝ ∞ b) (hbcompact : HasCompactSupport b)
    (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10))
    (hw : ContDiffOn ℝ 1 (fun z : (ℝ × ℝ) × ℝ ↦ ((parameterizedClockPassageData L Bhit z.1).wMinus
      z.2, (parameterizedClockPassageData L Bhit z.1).wPlus z.2)) (U ×ˢ Icc (205 : ℝ) (2051 / 10)))
    (ξ : ℝ × ℝ) (V : ℝ → ℝ)
    (hV : ∀ y ∈ Ioo (205 : ℝ) (2051 / 10), HasDerivAt (fun r : ℝ ↦
      (parameterizedClockPassageData L Bhit (r * ξ.1, r * ξ.2)).wMinus y +
      (parameterizedClockPassageData L Bhit (r * ξ.1, r * ξ.2)).wPlus y) (V y) 0) :
    Integrable (fun y ↦ b y * V y) ∧
      HasDerivAt (fun r : ℝ ↦ prescribedClockWeightMoment b L Bhit (r * ξ.1, r * ξ.2)) (∫ y : ℝ,
        b y * V y) 0 := by
  let S : Set ((ℝ × ℝ) × ℝ) := U ×ˢ uIcc (205 : ℝ) (2051 / 10)
  let H : (ℝ × ℝ) × ℝ → ℝ := fun z ↦ b z.2 *
    ((parameterizedClockPassageData L Bhit z.1).wMinus z.2 +
      (parameterizedClockPassageData L Bhit z.1).wPlus z.2)
  let J : (ℝ × ℝ) × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z ↦
    (fderivWithin ℝ H S z).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)
  have hseg : uIcc (205 : ℝ) (2051 / 10) = Icc (205 : ℝ) (2051 / 10) :=
    uIcc_of_le (by norm_num)
  have hw' : ContDiffOn ℝ 1 (fun z : (ℝ × ℝ) × ℝ ↦
        ((parameterizedClockPassageData L Bhit z.1).wMinus z.2,
          (parameterizedClockPassageData L Bhit z.1).wPlus z.2)) S := by
    simpa only [S, hseg] using hw
  have hb' : ContDiffOn ℝ 1 (fun z : (ℝ × ℝ) × ℝ ↦ b z.2) S :=
    (hb.of_le (by simp)).comp_contDiffOn contDiffOn_snd
  have hH : ContDiffOn ℝ 1 H S := hb'.mul (hw'.fst.add hw'.snd)
  have hS : UniqueDiffOn ℝ S :=
    hU.uniqueDiffOn.prod (uniqueDiffOn_uIcc (by norm_num : (205 : ℝ) ≠ 2051 / 10))
  have hJ : ContinuousOn J S := (hH.continuousOn_fderivWithin hS le_rfl).clm_comp continuousOn_const
  have hJ0 : ContinuousOn (fun y ↦ J ((0, 0), y)) (uIcc (205 : ℝ) (2051 / 10)) :=
    hJ.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy ↦ ⟨h0, hy⟩)
  have haxis : HasDerivAt (fun r : ℝ ↦ (r * ξ.1, r * ξ.2)) ξ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ξ.1).prodMk
      ((hasDerivAt_id (0 : ℝ)).mul_const ξ.2)
  have hJdir (y : ℝ) (hy : y ∈ uIcc (205 : ℝ) (2051 / 10)) :
      J ((0, 0), y) ξ = b y * V y := by
    have hd : HasFDerivWithinAt H (fderivWithin ℝ H S ((0, 0), y)) S ((0, 0), y) :=
      (hH.differentiableOn one_ne_zero ((0, 0), y) ⟨h0, hy⟩).hasFDerivWithinAt
    have hslice : HasFDerivAt (fun p : ℝ × ℝ ↦ H (p, y)) (J ((0, 0), y)) (0, 0) := by
      simpa only [J, Function.comp_def] using hd.comp_hasFDerivAt (0, 0)
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) ((0, 0) : ℝ × ℝ) y)
        (by filter_upwards [hU.mem_nhds h0] with p hp using ⟨hp, hy⟩)
    have hleft : HasDerivAt (fun r : ℝ ↦ H ((r * ξ.1, r * ξ.2), y))
        (J ((0, 0), y) ξ) 0 := by
      simpa only [Function.comp_def] using
        hslice.comp_hasDerivAt_of_eq (0 : ℝ) haxis (by simp)
    have hright : HasDerivAt (fun r : ℝ ↦ H ((r * ξ.1, r * ξ.2), y))
        (b y * V y) 0 := by
      by_cases hby : b y = 0
      · simpa only [H, hby, zero_mul] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
      · simpa only [H] using (hV y (hbsupp (subset_tsupport b hby))).const_mul (b y)
    exact hleft.unique hright
  have hsub : tsupport b ⊆ uIcc (205 : ℝ) (2051 / 10) := hseg ▸ hbsupp.trans Ioo_subset_Icc_self
  have hVc : ContinuousOn (fun y ↦ b y * V y) (tsupport b) :=
    ((hJ0.clm_apply (show ContinuousOn (fun _ : ℝ ↦ ξ)
      (uIcc (205 : ℝ) (2051 / 10)) from continuousOn_const)).mono hsub).congr
      (fun y hy ↦ (hJdir y (hsub hy)).symm)
  have hVint : Integrable (fun y ↦ b y * V y) := (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left b V).trans (subset_tsupport b))).mp
        (ContinuousOn.integrableOn_compact hbcompact hVc)
  have hsupp (f : ℝ → ℝ) : Function.support (fun y ↦ b y * f y) ⊆ Ioc (205 : ℝ) (2051 / 10) :=
    (Function.support_mul_subset_left b f).trans
      ((subset_tsupport b).trans (fun y hy ↦ ⟨(hbsupp hy).1, (hbsupp hy).2.le⟩))
  have hi : HasFDerivAt (fun p : ℝ × ℝ ↦ ∫ y in (205 : ℝ)..(2051 / 10), H (p, y))
      (∫ y in (205 : ℝ)..(2051 / 10), J ((0, 0), y)) (0, 0) :=
    PDE.Analysis.hasFDerivAt_intervalIntegral_of_contDiffOn hU hH h0
  have haxisI : HasDerivAt (fun r : ℝ ↦ ∫ y in (205 : ℝ)..(2051 / 10), H ((r * ξ.1, r * ξ.2), y))
      ((∫ y in (205 : ℝ)..(2051 / 10), J ((0, 0), y)) ξ) 0 := by
    simpa only [Function.comp_def] using hi.comp_hasDerivAt_of_eq (0 : ℝ) haxis (by simp)
  have hvalue : (∫ y in (205 : ℝ)..(2051 / 10), J ((0, 0), y)) ξ = ∫ y : ℝ, b y * V y := by
    rw [ContinuousLinearMap.intervalIntegral_apply hJ0.intervalIntegrable]
    exact (intervalIntegral.integral_congr fun y hy ↦ hJdir y hy).trans
      (intervalIntegral.integral_eq_integral_of_support_subset (hsupp V))
  have hwhole (p : ℝ × ℝ) : (∫ y in (205 : ℝ)..(2051 / 10), H (p, y)) =
      prescribedClockWeightMoment b L Bhit p :=
    intervalIntegral.integral_eq_integral_of_support_subset
      (hsupp (fun y ↦ (parameterizedClockPassageData L Bhit p).wMinus y +
        (parameterizedClockPassageData L Bhit p).wPlus y))
  exact ⟨hVint, by simpa only [hwhole] using haxisI.congr_deriv hvalue⟩

/-- Local smoothness of the same event maps makes the whole-line moment integrable
on one open parameter neighborhood. The fixed gate function may have either sign. -/
theorem exists_integrable_prescribedClockWeightMoment {N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (hb : ContDiff ℝ ∞ b) (hbcompact : HasCompactSupport b)
    (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧ ∀ p ∈ U,
      Integrable (fun y ↦ b y * ((parameterizedClockPassageData L Bhit p).wMinus y +
      (parameterizedClockPassageData L Bhit p).wPlus y)) := by
  obtain ⟨U, hU, h0U, hUN, _ht, hw⟩ :=
    exists_contDiffOn_parameterizedClockPassageData L Bhit hN h0 hL hBhit
  refine ⟨U, hU, h0U, hUN, fun p hp ↦ ?_⟩
  have hpair := hw.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hy ↦ ⟨hp, hy⟩ : MapsTo (fun y ↦ (p, y)) (Icc (205 : ℝ) (2051 / 10))
      (U ×ˢ Icc (205 : ℝ) (2051 / 10)))
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left b _).trans (subset_tsupport b))).mp
      (ContinuousOn.integrableOn_compact hbcompact (hb.continuous.continuousOn.mul
        ((hpair.fst.add hpair.snd).mono (hbsupp.trans Ioo_subset_Icc_self))))

/-- The speed derivative is the signed `qMinus/qPlus` moment of the same base data.
Its speed constant is already derived from `L - Bhit`, rather than supplied here. -/
theorem prescribedClockWeightMoment_speed_variation {N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (hb : ContDiff ℝ ∞ b) (hbcompact : HasCompactSupport b)
    (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) :
    Integrable (fun y ↦ b y *
      ((parameterizedClockPassageData L Bhit (0, 0)).wMinus y *
          (parameterizedClockPassageData L Bhit (0, 0)).qMinus y +
        (parameterizedClockPassageData L Bhit (0, 0)).wPlus y *
          (parameterizedClockPassageData L Bhit (0, 0)).qPlus y)) ∧
      HasDerivAt (fun μ ↦ prescribedClockWeightMoment b L Bhit (μ, 0))
        (∫ y : ℝ, b y *
          ((parameterizedClockPassageData L Bhit (0, 0)).wMinus y *
              (parameterizedClockPassageData L Bhit (0, 0)).qMinus y +
            (parameterizedClockPassageData L Bhit (0, 0)).wPlus y *
              (parameterizedClockPassageData L Bhit (0, 0)).qPlus y)) 0 := by
  obtain ⟨U, hU, h0U, _hUN, _ht, hw⟩ :=
    exists_contDiffOn_parameterizedClockPassageData L Bhit hN h0 hL hBhit
  have hLd : DifferentiableAt ℝ L (0, 0) :=
    (hL.contDiffAt (hN.mem_nhds h0)).differentiableAt (by simp)
  have hBd : DifferentiableAt ℝ Bhit (0, 0) :=
    (hBhit.contDiffAt (hN.mem_nhds h0)).differentiableAt (by simp)
  simpa only [mul_one, mul_zero] using prescribedClockWeightMoment_direction hU h0U hb hbcompact
    hbsupp (hw.of_le (by simp)) (1, 0)
    (fun y ↦ (parameterizedClockPassageData L Bhit (0, 0)).wMinus y *
        (parameterizedClockPassageData L Bhit (0, 0)).qMinus y +
      (parameterizedClockPassageData L Bhit (0, 0)).wPlus y *
        (parameterizedClockPassageData L Bhit (0, 0)).qPlus y)
    (fun y hy ↦ by
      simpa only [mul_one, mul_zero] using
        (hasDerivAt_parameterizedClockWeightMinus_speed L Bhit hy).fun_add
          (hasDerivAt_parameterizedClockWeightPlus_speed hLd hBd hy))

/-- Only the upper weight contributes to displacement. Its coefficient is the
displacement derivative of the same event gap, with the exact factor `-4`. -/
theorem prescribedClockWeightMoment_displacement_variation {N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (hb : ContDiff ℝ ∞ b) (hbcompact : HasCompactSupport b)
    (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) :
    Integrable (fun y ↦ b y * (parameterizedClockPassageData L Bhit (0, 0)).wPlus y) ∧
      HasDerivAt (fun a ↦ prescribedClockWeightMoment b L Bhit (0, a))
        (-4 * deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0 *
          ∫ y : ℝ, b y * (parameterizedClockPassageData L Bhit (0, 0)).wPlus y) 0 := by
  obtain ⟨U, hU, h0U, _hUN, _ht, hw⟩ :=
    exists_contDiffOn_parameterizedClockPassageData L Bhit hN h0 hL hBhit
  have hLd : DifferentiableAt ℝ L (0, 0) :=
    (hL.contDiffAt (hN.mem_nhds h0)).differentiableAt (by simp)
  have hBd : DifferentiableAt ℝ Bhit (0, 0) :=
    (hBhit.contDiffAt (hN.mem_nhds h0)).differentiableAt (by simp)
  let c : ℝ := -4 * deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0
  have h := prescribedClockWeightMoment_direction hU h0U hb hbcompact hbsupp
    (hw.of_le (by simp)) (0, 1) (fun y ↦ c * (parameterizedClockPassageData L Bhit (0, 0)).wPlus y)
    (fun y _hy ↦ by
      simpa only [mul_one, mul_zero, zero_add, c] using
        (hasDerivAt_parameterizedClockWeightMinus_displacement L Bhit y).fun_add
          (hasDerivAt_parameterizedClockWeightPlus_displacement hLd hBd y))
  have hpair := hw.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hy ↦ ⟨h0U, hy⟩ : MapsTo (fun y ↦ ((0, 0), y)) (Icc (205 : ℝ) (2051 / 10))
      (U ×ˢ Icc (205 : ℝ) (2051 / 10)))
  have hfactor : (∫ y : ℝ, b y * (c * (parameterizedClockPassageData L Bhit (0, 0)).wPlus y)) =
      c * ∫ y : ℝ, b y * (parameterizedClockPassageData L Bhit (0, 0)).wPlus y :=
    (integral_congr_ae (.of_forall fun y ↦ mul_left_comm _ _ _)).trans (integral_const_mul c _)
  exact ⟨(integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left b _).trans (subset_tsupport b))).mp
      (ContinuousOn.integrableOn_compact hbcompact (hb.continuous.continuousOn.mul
        (hpair.snd.mono (hbsupp.trans Ioo_subset_Icc_self)))),
    by simpa only [mul_one, mul_zero, c] using h.2.congr_deriv hfactor⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
