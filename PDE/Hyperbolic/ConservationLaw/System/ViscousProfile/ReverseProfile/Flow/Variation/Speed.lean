/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.Displacement

import CAS.ExactTactic

/-!
# Speed variation of the supplied prescribed clock

The parameter is `(μ,a)` and all derivatives are at `(0,0)`. The fast
speed variation equals `-t*Z(t)` by the shared scalar ODE uniqueness theorem.
The slow equation retains both the feedback derivative and the outer-switch
derivative. Its initial value is zero, as follows from the supplied initial map.

The speed anchor constant is defined from the event-gap derivative.
The supplied event identities determine its two boundary contributions.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff NNReal Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- The base fast equation follows by projection of the family equation. -/
theorem hasDerivAt_prescribed_base_fast {A B : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {I : Set ℝ} (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ I,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s ↦ (F (s, (0, 0))).2) (2 * (F (t, (0, 0))).2) t := by
  simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', prescribedSpeedField, sub_zero] using
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hode (0, 0) hbase t ht)

/-- The same supplied initial map gives zero initial speed variation in both states. -/
theorem prescribedVariation_speed_initial {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) :
    prescribedVariation F (1, 0) 0 = (0, 0) :=
  fderiv_prescribed_initial_state hN hbase hinitial (1, 0)

/-- The fast speed variation is identified by uniqueness, using the
base equation `Z'=2Z` and the zero initial parameter derivative. -/
theorem prescribedVariation_speed_fast_eq_neg_mul {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {N : Set (ℝ × ℝ)} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) :
    EqOn (fun t ↦ (prescribedVariation F (1, 0) t).2)
      (fun t ↦ -t * (F (t, (0, 0))).2) (Icc 0 b) := by
  have hlin : LipschitzWith (2 : ℝ≥0) (fun z : ℝ ↦ 2 * z) := by
    simpa using (lipschitzWith_smul (β := ℝ) (2 : ℝ))
  have hlip (t : ℝ) : LipschitzWith (2 : ℝ≥0)
      (fun z : ℝ ↦ 2 * z - (F (t, (0, 0))).2) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hlin.dist_le_mul x y
  have hZc : Continuous (fun t ↦ (F (t, (0, 0))).2) :=
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).snd
  have hzero : (prescribedVariation F (1, 0) 0).2 =
      -(0 : ℝ) * (F (0, (0, 0))).2 := by
    simpa using congrArg Prod.snd (prescribedVariation_speed_initial hN hbase hinitial)
  refine ODE_solution_unique (v := fun t z : ℝ ↦ 2 * z - (F (t, (0, 0))).2)
    hlip (continuous_prescribedVariation hF (1, 0)).snd.continuousOn ?_
    (continuous_id.neg.mul hZc).continuousOn ?_ hzero
  · intro t ht
    have h := hasDerivAt_prescribedVariation_fast hF hN hbase hode (Ico_subset_Icc_self ht) (1, 0)
    simpa only [one_mul] using h.hasDerivWithinAt
  · intro t ht
    have h := (hasDerivAt_id t).neg.mul
      (hasDerivAt_prescribed_base_fast hbase hode (Ico_subset_Icc_self ht))
    have hd : HasDerivAt (fun s ↦ -s * (F (s, (0, 0))).2)
        (2 * (-t * (F (t, (0, 0))).2) - (F (t, (0, 0))).2) t := by
      apply h.congr_deriv
      simp only [Pi.neg_apply, id_eq]
      ring
    exact hd.hasDerivWithinAt

/-- The same reference equality identifies the derived fast variation with `-t*Z`. -/
theorem prescribedVariation_speed_fast_eq_neg_mul_of_eqOn {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {N : Set (ℝ × ℝ)} {X Z : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1))
    (hsame : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc 0 b)) :
    EqOn (fun t ↦ (prescribedVariation F (1, 0) t).2) (fun t ↦ -t * Z t) (Icc 0 b) := by
  intro t ht
  simpa only [hsame ht] using prescribedVariation_speed_fast_eq_neg_mul hF hN hbase hode hinitial ht

/-- The ordinary fast-state derivative retains both smooth transition derivatives. -/
theorem hasDerivAt_prescribedClockField_fast (A B x z : ℝ) :
    HasDerivAt (fun s ↦ prescribedClockField A B s x)
      (deriv (clockFeedback A B) z - 4 * cutoff x * deriv (outerTransition A B) z) z := by
  have hφ := (((contDiff_clockFeedback A B).differentiable (by simp)) z).hasDerivAt
  have hO := (((contDiff_outerTransition A B).differentiable (by simp)) z).hasDerivAt
  exact (hφ.const_add (g x)).sub (hO.const_mul (4 * cutoff x))

/-- The slow field differential combines the displacement derivative
with the fast-state derivative and the direct speed term. No switch is frozen. -/
theorem fderiv_prescribedSpeedField_fst (A B x z ν : ℝ) (w : ℝ × ℝ) :
    (fderiv ℝ (prescribedSpeedField A B) (0, (x, z)) (ν, w)).1 =
      (deriv g x - 4 * deriv cutoff x * outerTransition A B z) * w.1 +
        (deriv (clockFeedback A B) z -
          4 * cutoff x * deriv (outerTransition A B) z) * w.2 - ν * x := by
  let D := fderiv ℝ (prescribedSpeedField A B) (0, (x, z))
  have hf := (((contDiff_prescribedSpeedField A B).differentiable (by simp))
    (0, (x, z))).hasFDerivAt.fst
  have hZ : (D (0, (0, 1))).1 =
      deriv (clockFeedback A B) z - 4 * cutoff x * deriv (outerTransition A B) z := by
    have hchain : HasDerivAt (fun s ↦ (prescribedSpeedField A B (0, (x, s))).1)
        (D (0, (0, 1))).1 z := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst'] using
        hf.comp_hasDerivAt z ((hasDerivAt_const z (0 : ℝ)).prodMk
          ((hasDerivAt_const z x).prodMk (hasDerivAt_id z)))
    have hslice : HasDerivAt (fun s ↦ (prescribedSpeedField A B (0, (x, s))).1)
        (deriv (clockFeedback A B) z -
          4 * cutoff x * deriv (outerTransition A B) z) z := by
      simpa only [prescribedSpeedField, zero_mul, sub_zero] using
        hasDerivAt_prescribedClockField_fast A B x z
    exact hchain.unique hslice
  have hμ : (D (1, (0, 0))).1 = -x := by
    have hchain : HasDerivAt (fun s ↦ (prescribedSpeedField A B (s, (x, z))).1)
        (D (1, (0, 0))).1 (0 : ℝ) := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst'] using hf.comp_hasDerivAt_of_eq (0 : ℝ)
          ((hasDerivAt_id (0 : ℝ)).prodMk
            ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_const (0 : ℝ) z))) rfl
    have hslice : HasDerivAt (fun s ↦ (prescribedSpeedField A B (s, (x, z))).1)
        (-x) (0 : ℝ) := by
      simpa only [prescribedSpeedField, id_eq, one_mul] using
        (((hasDerivAt_id (0 : ℝ)).mul_const x).const_sub (prescribedClockField A B z x))
    exact hchain.unique hslice
  have hX : (D (0, (w.1, 0))).1 = (deriv g x - 4 * deriv cutoff x * outerTransition A B z) * w.1 :=
    congrArg Prod.fst (fderiv_prescribedSpeedField_displacement A B x z w.1)
  have hsplit : (ν, w) = (0, (w.1, 0)) + w.2 • ((0 : ℝ), (0, (1 : ℝ))) +
        ν • ((1 : ℝ), (0, (0 : ℝ))) := by
    ext <;> simp
  change (D (ν, w)).1 = _
  calc
    (D (ν, w)).1 = (D (0, (w.1, 0))).1 +
        w.2 * (D (0, (0, 1))).1 + ν * (D (1, (0, 0))).1 := by
      calc
        _ = (D ((0, (w.1, 0)) + w.2 • ((0 : ℝ), (0, (1 : ℝ))) + ν • ((1 : ℝ), (0, (0 : ℝ))))).1 :=
          congrArg (fun v ↦ (D v).1) hsplit
        _ = _ := by
          rw [map_add, map_add, map_smul, map_smul]
          rfl
    _ = _ := by
      rw [hX, hZ, hμ]
      generalize deriv g x - 4 * deriv cutoff x * outerTransition A B z = a
      generalize deriv (clockFeedback A B) z - 4 * cutoff x * deriv (outerTransition A B) z = b
      ring

/-- The slow speed equation, with the derived fast speed variation
substituted and the entire feedback and outer-switch derivative retained. -/
theorem hasDerivAt_prescribed_speed {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivAt (fun s ↦ (prescribedVariation F (1, 0) s).1)
      (prescribedDisplacementRate A B F t * (prescribedVariation F (1, 0) t).1 +
        (deriv (clockFeedback A B) (F (t, (0, 0))).2 -
          4 * cutoff (F (t, (0, 0))).1 * deriv (outerTransition A B) (F (t, (0, 0))).2) *
          (-t * (F (t, (0, 0))).2) - (F (t, (0, 0))).1) t := by
  have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_prescribedVariation hF hN hbase hode ht (1, 0))
  have hfield : (fderiv ℝ (prescribedSpeedField A B) (0, F (t, (0, 0)))
        (1, prescribedVariation F (1, 0) t)).1 = (deriv g (F (t, (0, 0))).1 -
          4 * deriv cutoff (F (t, (0, 0))).1 * outerTransition A B (F (t, (0, 0))).2) *
            (prescribedVariation F (1, 0) t).1 + (deriv (clockFeedback A B) (F (t, (0, 0))).2 -
            4 * cutoff (F (t, (0, 0))).1 * deriv (outerTransition A B) (F (t, (0, 0))).2) *
                (prescribedVariation F (1, 0) t).2 - 1 * (F (t, (0, 0))).1 :=
    fderiv_prescribedSpeedField_fst A B
      (F (t, (0, 0))).1 (F (t, (0, 0))).2 1 (prescribedVariation F (1, 0) t)
  have hz := prescribedVariation_speed_fast_eq_neg_mul hF hN hbase hode hinitial ht
  simpa only [Function.comp_def, ContinuousLinearMap.coe_fst',
    hfield, hz, one_mul, prescribedDisplacementRate] using h

/-- Rewriting only by the supplied reference equality gives the physical reference
forcing. The coefficient is the same `prescribedDisplacementRate` as before. -/
theorem hasDerivAt_prescribed_speed_of_eqOn {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {X Z : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1))
    (hsame : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc 0 b)) {t : ℝ}
    (ht : t ∈ Icc 0 b) :
    HasDerivAt (fun s ↦ (prescribedVariation F (1, 0) s).1)
      (prescribedDisplacementRate A B F t * (prescribedVariation F (1, 0) t).1 +
        (deriv (clockFeedback A B) (Z t) -
          4 * cutoff (X t) * deriv (outerTransition A B) (Z t)) * (-t * Z t) - X t) t := by
  simpa only [hsame ht] using hasDerivAt_prescribed_speed hF hN hbase hode hinitial ht

/-- The anchor constant is fixed by the speed derivative of the supplied
late-event time minus upward-passage time, with displacement held at zero. -/
def prescribedSpeedAnchorConstant (L Bhit : ℝ × ℝ → ℝ) : ℝ :=
  -4 * deriv (fun μ ↦ L (μ, 0) - Bhit (μ, 0)) 0

/-- The scalar speed derivative of the same two event maps. Its two
boundary terms are the fixed-time slow speed variations. -/
theorem hasDerivAt_prescribed_event_gap_speed {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {L Bhit : ℝ × ℝ → ℝ} {τ0 b₀ : ℝ} (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hFL : ContDiffAt ℝ 1 F (τ0, (0, 0))) (hFB : ContDiffAt ℝ 1 F (b₀, (0, 0)))
    (hL : ContDiffOn ℝ 1 L N) (hBhit : ContDiffOn ℝ 1 Bhit N) (hLbase : L (0, 0) = τ0)
    (hBbase : Bhit (0, 0) = b₀) (hLlevel : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hBlevel : ∀ p ∈ N, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) τ0)
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (g 205 + 1) b₀) :
    HasDerivAt (fun μ ↦ L (μ, 0) - Bhit (μ, 0)) ((prescribedVariation F (1, 0) τ0).1 / 8 +
      (prescribedVariation F (1, 0) b₀).1 / (g 205 + 1)) 0 := by
  have hevents := fderiv_prescribed_speed_events hN hbase hFL hFB
    hL hBhit hLbase hBbase hLlevel hBlevel hLtime hBtime (1, 0)
  have hLd := (hL.contDiffAt (hN.mem_nhds hbase)).differentiableAt_one
  have hBd := (hBhit.contDiffAt (hN.mem_nhds hbase)).differentiableAt_one
  have h : HasDerivAt (fun μ ↦ L (μ, 0) - Bhit (μ, 0))
      ((fderiv ℝ L (0, 0) - fderiv ℝ Bhit (0, 0)) (1, 0)) 0 := by
    simpa only [Function.comp_def, id_eq] using
      (hLd.hasFDerivAt.fun_sub hBd.hasFDerivAt).comp_hasDerivAt_of_eq (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))) rfl
  apply h.congr_deriv
  change fderiv ℝ L (0, 0) (1, 0) - fderiv ℝ Bhit (0, 0) (1, 0) = _
  simp only [hevents.1, hevents.2, neg_div, sub_neg_eq_add, prescribedVariation]

/-- The derived anchor constant has the two boundary contributions dictated by
event motion. It is a value determined by the supplied family and events. -/
theorem prescribedSpeedAnchorConstant_eq {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {L Bhit : ℝ × ℝ → ℝ} {τ0 b₀ : ℝ} (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hFL : ContDiffAt ℝ 1 F (τ0, (0, 0))) (hFB : ContDiffAt ℝ 1 F (b₀, (0, 0)))
    (hL : ContDiffOn ℝ 1 L N) (hBhit : ContDiffOn ℝ 1 Bhit N) (hLbase : L (0, 0) = τ0)
    (hBbase : Bhit (0, 0) = b₀) (hLlevel : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hBlevel : ∀ p ∈ N, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) τ0)
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (g 205 + 1) b₀) :
    prescribedSpeedAnchorConstant L Bhit = -4 * ((prescribedVariation F (1, 0) τ0).1 / 8 +
      (prescribedVariation F (1, 0) b₀).1 / (g 205 + 1)) := by
  rw [prescribedSpeedAnchorConstant, (hasDerivAt_prescribed_event_gap_speed hN hbase hFL hFB
      hL hBhit hLbase hBbase hLlevel hBlevel hLtime hBtime).deriv]

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
