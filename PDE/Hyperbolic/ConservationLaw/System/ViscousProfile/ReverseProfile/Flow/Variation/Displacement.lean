/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar.Barrier
public import PDE.Analysis.ODE.SmoothDependence.Variation
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Events.Speed
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Events.Variation

/-!
# Variations of the supplied prescribed clock

The parameter is `(μ,a)` and the initial state is `(a,1)`. Differentiation of the
family gives a common directional ODE, with the direct speed variation
retained. For the displacement direction, scalar uniqueness proves that the fast
variation is zero. The slow variation then solves a homogeneous scalar equation
whose coefficient retains the outer switch throughout its transition.

The Gronwall bounds identify this slow variation with a positive
exponential. The event identities for the same family give a positive
displacement derivative of the late-zero time minus the upward-passage time.
-/

@[expose] public noncomputable section

open Filter Set
open PDE.Analysis.Evolution
open scoped ContDiff NNReal Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- The parameter derivative of the supplied family, with time held fixed. -/
def prescribedVariation (F : ℝ × (ℝ × ℝ) → ℝ × ℝ) (ξ : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  fderiv ℝ (fun p ↦ F (t, p)) (0, 0) ξ

/-- The state coefficient along the base family, including the full outer transition. -/
def prescribedDisplacementRate (A B : ℝ) (F : ℝ × (ℝ × ℝ) → ℝ × ℝ) (t : ℝ) : ℝ :=
  deriv g (F (t, (0, 0))).1 -
    4 * deriv cutoff (F (t, (0, 0))).1 * outerTransition A B (F (t, (0, 0))).2

/-- Smoothness of the given family supplies continuity of its variation. -/
theorem continuous_prescribedVariation {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    (hF : ContDiff ℝ ∞ F) (ξ : ℝ × ℝ) : Continuous (prescribedVariation F ξ) :=
  (contDiffOn_univ.mp (PDE.Analysis.ODE.contDiffOn_parameterVariation
    (F := fun t p ↦ F (t, p)) (I := univ) (U := univ) (p := (0, 0))
    hF.contDiffOn isOpen_univ (mem_univ _) ξ)).continuous

/-- The coefficient is continuous even during the switching interval. -/
theorem continuous_prescribedDisplacementRate (A B : ℝ)
    {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} (hF : ContDiff ℝ ∞ F) :
    Continuous (prescribedDisplacementRate A B F) := by
  have hbase : Continuous (fun t ↦ F (t, (0, 0))) :=
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  exact ((contDiff_g.continuous_deriv (by simp)).comp hbase.fst).sub ((continuous_const.mul
      ((contDiff_cutoff.continuous_deriv (by simp)).comp hbase.fst)).mul
      ((contDiff_outerTransition A B).continuous.comp hbase.snd))

/-- The time equation near the parameter gives its directional variational
ODE. Global smoothness allows the germ theorem at every supplied time, including
endpoints of a closed time interval. The field differential is kept intact. -/
theorem hasDerivAt_prescribedVariation {A B : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {I : Set ℝ} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ I,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    {t : ℝ} (ht : t ∈ I) (ξ : ℝ × ℝ) :
    HasDerivAt (prescribedVariation F ξ) (fderiv ℝ (prescribedSpeedField A B) (0, F (t, (0, 0)))
      (ξ.1, prescribedVariation F ξ t)) t := by
  let v : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun q ↦ prescribedSpeedField A B (q.1.1, q.2)
  have hmap : HasFDerivAt (fun q : (ℝ × ℝ) × (ℝ × ℝ) ↦ (q.1.1, q.2))
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))).prod
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))) ((0, 0), F (t, (0, 0))) :=
    hasFDerivAt_fst.fst.prodMk hasFDerivAt_snd
  have hv := (((contDiff_prescribedSpeedField A B).differentiable (by simp))
    (0, F (t, (0, 0)))).hasFDerivAt.comp ((0, 0), F (t, (0, 0))) hmap
  refine (PDE.Analysis.ODE.hasDerivAt_parameterVariation_of_contDiffAt
    (F := fun s p ↦ F (s, p)) (v := v) (hF.contDiffAt.of_le (by simp)) hv.differentiableAt
    (Filter.Eventually.mono (hN.mem_nhds hbase) fun p hp ↦ hode p hp t ht) ξ).congr_deriv ?_
  simpa [v, Function.comp_def, prescribedVariation] using
    congrArg (fun D : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) ↦
      D (ξ, prescribedVariation F ξ t)) hv.fderiv

/-- The fast component retains the direct speed contribution `-ν*z`. -/
theorem fderiv_prescribedSpeedField_snd (A B x z ν : ℝ) (w : ℝ × ℝ) :
    (fderiv ℝ (prescribedSpeedField A B) (0, (x, z)) (ν, w)).2 = 2 * w.2 - ν * z := by
  have hz : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) ↦ p.2.2) ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (0, (x, z)) := hasFDerivAt_snd.snd
  have hfast := ((hasFDerivAt_const (2 : ℝ) (0, (x, z))).sub (hasFDerivAt_fst (𝕜 := ℝ))).mul hz
  have hfield := (((contDiff_prescribedSpeedField A B).differentiable (by simp))
    (0, (x, z))).hasFDerivAt.snd
  simpa [sub_eq_add_neg, mul_comm] using
    congrArg (fun D : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ ↦ D (ν, w)) (hfield.unique hfast)

/-- Restricting the field differential to the middle-state direction uses the
ordinary state-derivative theorem, without freezing a transition. -/
theorem fderiv_prescribedSpeedField_displacement (A B x z u : ℝ) :
    fderiv ℝ (prescribedSpeedField A B) (0, (x, z)) (0, (u, 0)) =
      ((deriv g x - 4 * deriv cutoff x * outerTransition A B z) * u, 0) := by
  have hcurve : HasDerivAt (fun y ↦ prescribedSpeedField A B (0, (y, z)))
      (fderiv ℝ (prescribedSpeedField A B) (0, (x, z)) (0, (1, 0))) x := by
    simpa only [Function.comp_def, id_eq] using
      (((contDiff_prescribedSpeedField A B).differentiable (by simp))
        (0, (x, z))).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x (0 : ℝ)).prodMk
          ((hasDerivAt_id x).prodMk (hasDerivAt_const x z)))
  have hslice : HasDerivAt (fun y ↦ prescribedSpeedField A B (0, (y, z)))
      (deriv g x - 4 * deriv cutoff x * outerTransition A B z, 0) x := by
    simpa only [prescribedSpeedField, zero_mul, sub_zero] using
      (hasDerivAt_prescribedClockField A B z x).prodMk (hasDerivAt_const x (2 * z))
  rw [show ((0 : ℝ), (u, (0 : ℝ))) = u • ((0 : ℝ), (1, (0 : ℝ))) by simp, map_smul,
    hcurve.unique hslice]
  simp [mul_comm]

/-- The fast variational equation follows from the common directional ODE. -/
theorem hasDerivAt_prescribedVariation_fast {A B : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {I : Set ℝ} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ I,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    {t : ℝ} (ht : t ∈ I) (ξ : ℝ × ℝ) :
    HasDerivAt (fun s ↦ (prescribedVariation F ξ s).2)
      (2 * (prescribedVariation F ξ t).2 - ξ.1 * (F (t, (0, 0))).2) t :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_prescribedVariation hF hN hbase hode ht ξ)).congr_deriv
      (fderiv_prescribedSpeedField_snd A B _ _ ξ.1 _)

/-- Zero fast displacement is a consequence of the derived scalar equation and
its zero initial value. Uniqueness is the shared Mathlib ODE theorem. -/
theorem prescribedVariation_displacement_fast_eq_zero {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {N : Set (ℝ × ℝ)} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) :
    EqOn (fun t ↦ (prescribedVariation F (0, 1) t).2) (fun _ ↦ 0) (Icc 0 b) := by
  have hlip : LipschitzWith (2 : ℝ≥0) (fun z : ℝ ↦ 2 * z) := by
    simpa using (lipschitzWith_smul (β := ℝ) (2 : ℝ))
  refine ODE_solution_unique (v := fun _ z : ℝ ↦ 2 * z) (fun _ ↦ hlip)
    (continuous_prescribedVariation hF (0, 1)).snd.continuousOn (fun t ht ↦ ?_)
    continuousOn_const (fun t _ ↦ ?_)
    (congrArg Prod.snd (fderiv_prescribed_initial_state hN hbase hinitial (0, 1)))
  · simpa only [zero_mul, sub_zero] using (hasDerivAt_prescribedVariation_fast hF hN hbase hode
      (Ico_subset_Icc_self ht) (0, 1)).hasDerivWithinAt
  · simpa only [mul_zero] using (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt

/-- The slow displacement satisfies the scalar homogeneous equation.
The fast displacement is first proved zero, then removed from the field action. -/
theorem hasDerivAt_prescribed_displacement {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivAt (fun s ↦ (prescribedVariation F (0, 1) s).1)
      (prescribedDisplacementRate A B F t * (prescribedVariation F (0, 1) t).1) t := by
  have hz := prescribedVariation_displacement_fast_eq_zero hF hN hbase hode hinitial ht
  have h := hasDerivAt_prescribedVariation hF hN hbase hode ht (0, 1)
  rw [show prescribedVariation F (0, 1) t = (_, 0) from Prod.ext rfl hz,
    fderiv_prescribedSpeedField_displacement] at h
  simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', prescribedDisplacementRate] using
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- The supplied reference equality identifies the coefficient with
`g'(X) - 4*C'(X)*O(Z)` on the same time interval. -/
theorem hasDerivAt_prescribed_displacement_of_eqOn {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {N : Set (ℝ × ℝ)} {X Z : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1))
    (hsame : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc 0 b)) {t : ℝ}
    (ht : t ∈ Icc 0 b) :
    HasDerivAt (fun s ↦ (prescribedVariation F (0, 1) s).1) ((deriv g (X t) - 4 *
      deriv cutoff (X t) * outerTransition A B (Z t)) * (prescribedVariation F (0, 1) t).1) t := by
  simpa only [prescribedDisplacementRate, hsame ht] using
    hasDerivAt_prescribed_displacement hF hN hbase hode hinitial ht

/-- Applying the two signed-coefficient Gronwall bounds identifies the
unit-initialized displacement with its integrating-factor exponential. -/
theorem prescribed_displacement_eq_exp_integral {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {N : Set (ℝ × ℝ)} (hb : 0 ≤ b) (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) {t : ℝ} (ht : t ∈ Icc 0 b) :
    (prescribedVariation F (0, 1) t).1 =
      Real.exp (∫ s in 0..t, prescribedDisplacementRate A B F s) := by
  let q : ℝ → ℝ := fun s ↦ (prescribedVariation F (0, 1) s).1
  let k : ℝ → ℝ := prescribedDisplacementRate A B F
  have hq : ContinuousOn q (Icc 0 b) := (continuous_prescribedVariation hF (0, 1)).fst.continuousOn
  have hk : ContinuousOn k (Icc 0 b) := (continuous_prescribedDisplacementRate A B hF).continuousOn
  have hd (s : ℝ) (hs : s ∈ Ico 0 b) : HasDerivWithinAt q (k s * q s) (Icc 0 b) s :=
    (hasDerivAt_prescribed_displacement hF hN hbase hode hinitial
      (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hinit : q 0 = 1 :=
    congrArg Prod.fst (fderiv_prescribed_initial_state hN hbase hinitial (0, 1))
  have hu := le_mul_exp_integral_of_hasDerivWithinAt_le hb hq hk hd (fun _ _ ↦ le_rfl)
  have hl := dissipative_lower_barrier_variable_rate
    (q := q) (dq := fun s ↦ k s * q s) (r := fun s ↦ -k s) (β := 0) (κ := 1)
    hb hq hk.neg hd (by rw [hinit]; norm_num) (fun s _ ↦ by simp)
  apply le_antisymm
  · simpa only [hinit, one_mul] using hu t ht
  · simpa only [zero_add, one_mul, intervalIntegral.integral_neg, neg_neg] using hl t ht

/-- The slow displacement is strictly positive throughout the closed interval. -/
theorem prescribed_displacement_pos {A B b : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    (hb : 0 ≤ b) (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) {t : ℝ} (ht : t ∈ Icc 0 b) :
    0 < (prescribedVariation F (0, 1) t).1 :=
  (prescribed_displacement_eq_exp_integral hb hF hN hbase hode hinitial ht) ▸ Real.exp_pos _

/-- The derivative of the supplied late-zero time minus upward-passage time is
positive in the displacement direction. The level identities and reference
velocities are the event data for this same family. -/
theorem fderiv_prescribed_event_gap_displacement_pos {A B b τ0 b₀ : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {N : Set (ℝ × ℝ)} {L Bhit : ℝ × ℝ → ℝ} (hb : 0 ≤ b) (hτ : τ0 ∈ Icc 0 b) (hb₀ : b₀ ∈ Icc 0 b)
    (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) (hL : ContDiffOn ℝ 1 L N)
    (hBhit : ContDiffOn ℝ 1 Bhit N) (hLbase : L (0, 0) = τ0) (hBbase : Bhit (0, 0) = b₀)
    (hLlevel : ∀ p ∈ N, (F (L p, p)).1 = 0) (hBlevel : ∀ p ∈ N, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) τ0)
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (g 205 + 1) b₀) :
    0 < fderiv ℝ (fun p ↦ L p - Bhit p) (0, 0) (0, 1) := by
  have hevents := fderiv_prescribed_speed_events hN hbase
    (hF.contDiffAt.of_le (by simp)) (hF.contDiffAt.of_le (by simp))
    hL hBhit hLbase hBbase hLlevel hBlevel hLtime hBtime (0, 1)
  rw [fderiv_fun_sub (hL.contDiffAt (hN.mem_nhds hbase)).differentiableAt_one
    (hBhit.contDiffAt (hN.mem_nhds hbase)).differentiableAt_one,
    sub_apply, hevents.1, hevents.2, neg_div, sub_neg_eq_add]
  exact add_pos (div_pos (prescribed_displacement_pos hb hF hN hbase hode hinitial hτ)
      (by norm_num)) (div_pos (prescribed_displacement_pos hb hF hN hbase hode hinitial hb₀)
      (by linarith only [g_nonneg (205 : ℝ)]))

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
