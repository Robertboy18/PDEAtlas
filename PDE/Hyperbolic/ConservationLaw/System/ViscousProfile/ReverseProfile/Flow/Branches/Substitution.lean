/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.ParameterVariation

import CAS.ExactTactic

/-!
# Substitution on the supplied prescribed clock branches

Closed-level image and hit identities identify the passage maps with
levels of the same supplied family. Quotient FTC and interval substitution then
identify each oriented time integral with its value weight. Reversing
both the downward Jacobian and its endpoints gives the lower weight with a positive sign.

The lower primitive retains its full cutoff. Compact gate support permits a whole-line state
integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights MiddleClock

variable {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ}
  {p : ℝ × ℝ} {b : ℝ → ℝ} {s e : ℝ}

section Up

variable
  (hF : ContinuousOn (fun t ↦ (F (t, p)).1) (Icc s e))
  (hb : Continuous b)
  (himage : MapsTo (parameterizedClockPassageData L Bhit p).tPlus
    (Icc (205 : ℝ) (2051 / 10)) (Icc s e))
  (hhit : ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
    (F ((parameterizedClockPassageData L Bhit p).tPlus y, p)).1 = y)
  (hden : ∀ v ∈ Icc (0 : ℝ) 210,
    (parameterizedClockPassageData L Bhit p).g v + 1 ≠ 0)

include hF hb himage hhit hden

/-- The upward passage map substitutes into the same supplied family's forcing
integral. The gate function may be signed. -/
theorem prescribed_speed_up_branch_integral_eq :
    let D := parameterizedClockPassageData L Bhit p; (∫ t in D.tPlus 205..D.tPlus (2051 / 10),
      b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) = ∫ y in (205 : ℝ)..(2051 / 10),
      b y * D.wPlus y := by
  intro D
  let H : ℝ → ℝ := fun t ↦ b ((F (t, p)).1) * Real.exp (-4 * (L p - t))
  have hseg : uIcc (205 : ℝ) (2051 / 10) = Icc (205 : ℝ) (2051 / 10) :=
    uIcc_of_le (by norm_num)
  have hK : Icc (205 : ℝ) (2051 / 10) ⊆ Icc (0 : ℝ) 210 :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have hg : Continuous D.g := contDiff_g.continuous.sub (continuous_const.mul continuous_id)
  have hd : Continuous (fun y ↦ D.g y + 1) := hg.add continuous_const
  have ht (y : ℝ) (hy : y ∈ Icc (205 : ℝ) (2051 / 10)) :
      HasDerivAt D.tPlus (1 / (D.g y + 1)) y := by
    have hne : ∀ v ∈ uIcc (205 : ℝ) y, D.g v + 1 ≠ 0 := fun v hv ↦
      hden v (ordConnected_Icc.uIcc_subset
        (show (205 : ℝ) ∈ Icc (0 : ℝ) 210 from ⟨by norm_num, by norm_num⟩) (hK hy) hv)
    exact (PDE.Analysis.hasDerivAt_integral_quotient
      (f := fun _ : ℝ ↦ 1) (a := 205) continuous_const hd hne).const_add D.upBaseTime
  have hJ : ContinuousOn (fun y ↦ 1 / (D.g y + 1)) (Icc (205 : ℝ) (2051 / 10)) :=
    continuousOn_const.div hd.continuousOn (fun y hy ↦ hden y (hK hy))
  have hH : ContinuousOn H (Icc s e) := (hb.comp_continuousOn hF).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hHimage : ContinuousOn H (D.tPlus '' uIcc (205 : ℝ) (2051 / 10)) :=
    hH.mono fun _ ⟨y, hy, hxy⟩ ↦ hxy ▸ himage (hseg ▸ hy)
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 205) (b := 2051 / 10) (f := D.tPlus)
    (f' := fun y ↦ 1 / (D.g y + 1)) (g := H) (fun y hy ↦ ht y (hseg ▸ hy)) (hseg ▸ hJ) hHimage
  change (∫ t in D.tPlus 205..D.tPlus (2051 / 10), H t) = _
  rw [← hsub]
  refine intervalIntegral.integral_congr fun y hy ↦ ?_
  dsimp only [Function.comp_def, H]
  rw [hhit y (hseg ▸ hy)]
  simp only [PassageData.wPlus, show D.terminalTime = L p from rfl, div_eq_mul_inv, one_mul,
    mul_assoc]

/-- Open gate support turns the upward identity into a whole-line state integral. -/
theorem prescribed_speed_up_branch_integral_eq_integral
    (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) :
    let D := parameterizedClockPassageData L Bhit p; (∫ t in D.tPlus 205..D.tPlus (2051 / 10),
      b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) = ∫ y : ℝ, b y * D.wPlus y := by
  exact (prescribed_speed_up_branch_integral_eq hF hb himage hhit hden).trans
    (intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_left b _).trans ((subset_tsupport b).trans
          (fun y hy ↦ ⟨(hbsupp hy).1, (hbsupp hy).2.le⟩))))

end Up

section Down

variable
  (hF : ContinuousOn (fun t ↦ (F (t, p)).1) (Icc s (L p)))
  (hb : Continuous b)
  (himage : MapsTo (parameterizedClockPassageData L Bhit p).tMinus
    (Icc (205 : ℝ) (2051 / 10)) (Icc s (L p)))
  (hhit : ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
    (F ((parameterizedClockPassageData L Bhit p).tMinus y, p)).1 = y)
  (hden : ∀ v ∈ Icc (0 : ℝ) 210,
    (parameterizedClockPassageData L Bhit p).downSpeed v ≠ 0)

include hF hb himage hhit hden

/-- The reversed downward passage interval has the lower value weight.
The primitive uses the full cutoff; its Jacobian simplifies only on the gate. -/
theorem prescribed_speed_down_branch_integral_eq :
    let D := parameterizedClockPassageData L Bhit p; (∫ t in D.tMinus (2051 / 10)..D.tMinus 205,
      b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) = ∫ y in (205 : ℝ)..(2051 / 10),
      b y * D.wMinus y := by
  intro D
  let H : ℝ → ℝ := fun t ↦ b ((F (t, p)).1) * Real.exp (-4 * (L p - t))
  have hseg : uIcc (205 : ℝ) (2051 / 10) = Icc (205 : ℝ) (2051 / 10) :=
    uIcc_of_le (by norm_num)
  have hK : Icc (205 : ℝ) (2051 / 10) ⊆ Icc (0 : ℝ) 210 :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have hg : Continuous D.g := contDiff_g.continuous.sub (continuous_const.mul continuous_id)
  have hd : Continuous D.downSpeed :=
    (continuous_const.sub hg).add (continuous_const.mul contDiff_cutoff.continuous)
  have ht (y : ℝ) (hy : y ∈ Icc (205 : ℝ) (2051 / 10)) :
      HasDerivAt D.tMinus (-(1 / D.downSpeed y)) y := by
    have hne : ∀ v ∈ uIcc (0 : ℝ) y, D.downSpeed v ≠ 0 := fun v hv ↦
      hden v (ordConnected_Icc.uIcc_subset
        (show (0 : ℝ) ∈ Icc (0 : ℝ) 210 from ⟨le_rfl, by norm_num⟩) (hK hy) hv)
    exact (PDE.Analysis.hasDerivAt_integral_quotient
      (f := fun _ : ℝ ↦ 1) (a := 0) continuous_const hd hne).const_sub D.terminalTime
  have hJ : ContinuousOn (fun y ↦ -(1 / D.downSpeed y)) (Icc (205 : ℝ) (2051 / 10)) :=
    (continuousOn_const.div hd.continuousOn (fun y hy ↦ hden y (hK hy))).neg
  have hH : ContinuousOn H (Icc s (L p)) := (hb.comp_continuousOn hF).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hHimage : ContinuousOn H (D.tMinus '' uIcc (205 : ℝ) (2051 / 10)) :=
    hH.mono fun _ ⟨y, hy, hxy⟩ ↦ hxy ▸ himage (hseg ▸ hy)
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 205) (b := 2051 / 10) (f := D.tMinus)
    (f' := fun y ↦ -(1 / D.downSpeed y)) (g := H) (fun y hy ↦ ht y (hseg ▸ hy)) (hseg ▸ hJ) hHimage
  change (∫ t in D.tMinus (2051 / 10)..D.tMinus 205, H t) = _
  rw [intervalIntegral.integral_symm (D.tMinus 205), ← hsub, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun y hy ↦ ?_
  have hyK : y ∈ Icc (205 : ℝ) (2051 / 10) := hseg ▸ hy
  dsimp only [Function.comp_def, H]
  rw [hhit y hyK]
  simp only [PassageData.wMinus, show D.terminalTime = L p from rfl, PassageData.downSpeed,
    show D.C y = 0 from cutoff_of_ge hyK.1, mul_zero, add_zero, mul_neg, neg_neg, div_eq_mul_inv,
    one_mul, mul_assoc]

/-- Open gate support also yields the whole-line lower state integral, with the
same supplied terminal time and the same reversed passage endpoints. -/
theorem prescribed_speed_down_branch_integral_eq_integral
    (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) :
    let D := parameterizedClockPassageData L Bhit p; (∫ t in D.tMinus (2051 / 10)..D.tMinus 205,
      b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) = ∫ y : ℝ, b y * D.wMinus y := by
  exact (prescribed_speed_down_branch_integral_eq hF hb himage hhit hden).trans
    (intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_left b _).trans ((subset_tsupport b).trans
          (fun y hy ↦ ⟨(hbsupp hy).1, (hbsupp hy).2.le⟩))))

end Down

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
