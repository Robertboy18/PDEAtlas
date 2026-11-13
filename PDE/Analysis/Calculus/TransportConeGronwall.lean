/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.TransportCone
public import PDE.Analysis.Evolution.Core.Gronwall
import CAS.ExactTactic

/-!
# Grönwall comparison on a shrinking cone

The smooth cone estimate is integrated on a compact positive-radius time interval.
The source budget is the integral of the actual transport residual on a fixed
spatial ball containing the cone. This form permits passage to a locally `L¹`
limit of the residual.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Metric Set

variable {n : ℕ}

/-- The joint transport derivative splits into its time and spatial parts. -/
theorem fderiv_uncurry_transport
    {w : ℝ → ℝ^n → ℝ} (hw : Differentiable ℝ (Function.uncurry w))
    (t : ℝ) (x v : ℝ^n) :
    fderiv ℝ (Function.uncurry w) (t, x) (1, v) =
      fderiv ℝ (Function.uncurry w) (t, x) (1, 0) + fderiv ℝ (w t) x v := by
  have hslice : HasFDerivAt (w t)
      ((fderiv ℝ (Function.uncurry w) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ^n))) x :=
    (hw (t, x)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  rw [hslice.fderiv]
  change _ = _ + fderiv ℝ (Function.uncurry w) (t, x) (0, v)
  rw [← map_add]
  simp

/-- A nonnegative smooth transported density is controlled by its initial cone
integral and the actual residual on a containing compact cylinder. All energy
inequalities are derived from the differential equation's residual. -/
theorem ballIntegral_shrinking_le_mul_exp
    [Fact (0 < n)] {w : ℝ → ℝ^n → ℝ} {b : ℝ × ℝ^n → ℝ^n}
    (hw : ContDiff ℝ 1 (Function.uncurry w)) (hb : ContDiff ℝ 1 b)
    (c : ℝ^n) {R T a d L K : ℝ} (hK : 0 ≤ K)
    (hr : ∀ s ∈ Icc a d, 0 < R * (T - s))
    (hrL : ∀ s ∈ Icc a d, R * (T - s) ≤ L)
    (hw0 : ∀ s ∈ Icc a d, ∀ x ∈ closedBall c (R * (T - s)), 0 ≤ w s x)
    (hbR : ∀ s ∈ Icc a d, ∀ x ∈ sphere c (R * (T - s)), ‖b (s, x)‖ ≤ R)
    (hbK : ∀ s ∈ Icc a d, ∀ x ∈ ball c (R * (T - s)),
      ∇· (fun y ↦ b (s, y)) x ≤ K) :
    ∀ t ∈ Icc a d,
      ballIntegral n (w t) c (R * (T - t)) ≤
        (ballIntegral n (w a) c (R * (T - a)) +
          ∫ s in a..d, ∫ x in closedBall c L,
            ‖fderiv ℝ (Function.uncurry w) (s, x) (1, b (s, x))‖) *
          Real.exp (K * (t - a)) := by
  let e : ℝ → ℝ := fun s ↦ ballIntegral n (w s) c (R * (T - s))
  let g : ℝ → ℝ := fun s ↦ ∫ x in closedBall c L,
    ‖fderiv ℝ (Function.uncurry w) (s, x) (1, b (s, x))‖
  have hdiff (s : ℝ) (hs : s ∈ Icc a d) : DifferentiableAt ℝ e s := by
    have hρ : HasDerivAt (fun s : ℝ ↦ R * (T - s)) (-R) s := by cas
    exact (hasDerivAt_ballIntegral_moving w hw c _ hρ (hr s hs)).differentiableAt
  have he : ContinuousOn e (Icc a d) := fun s hs ↦ (hdiff s hs).continuousAt.continuousWithinAt
  have hg : Continuous g := continuous_parametric_integral_of_continuous
    (((hw.continuous_fderiv one_ne_zero).clm_apply (continuous_const.prodMk hb.continuous)).norm)
    (isCompact_closedBall c L)
  have hgn (s : ℝ) : 0 ≤ g s := integral_nonneg fun _ ↦ norm_nonneg _
  have hderiv (s : ℝ) (hs : s ∈ Icc a d) : deriv e s ≤ K * e s + g s := by
    have hbs : ContDiff ℝ 1 (fun y ↦ b (s, y)) :=
      hb.comp (contDiff_const.prodMk contDiff_id)
    have hbase := deriv_ballIntegral_shrinking_le hw hbs c (hr s hs)
      (hw0 s hs) (hbR s hs) (hbK s hs)
    have hnorm : Continuous (fun x ↦
        ‖fderiv ℝ (Function.uncurry w) (s, x) (1, b (s, x))‖) :=
      (((hw.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const.prodMk hb.continuous)).norm).comp
          (continuous_const.prodMk continuous_id)
    have hsource : ballIntegral n (fun x ↦
        ‖fderiv ℝ (Function.uncurry w) (s, x) (1, 0) +
          fderiv ℝ (w s) x (b (s, x))‖) c (R * (T - s)) ≤ g s := by
      simp_rw [← fderiv_uncurry_transport (hw.differentiable one_ne_zero)]
      apply setIntegral_mono_set
        (hnorm.continuousOn.integrableOn_compact (isCompact_closedBall c L))
      · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
      · exact Filter.Eventually.of_forall fun x hx ↦
          closedBall_subset_closedBall (hrL s hs) (ball_subset_closedBall hx)
    exact hbase.trans (add_le_add le_rfl hsource)
  have hintegral (t : ℝ) (ht : t ∈ Icc a d) :
      e t ≤ (e a + ∫ s in a..d, g s) + K * ∫ s in a..t, e s := by
    have hsub : Icc a t ⊆ Icc a d := Icc_subset_Icc_right ht.2
    have heInt : IntervalIntegrable e volume a t :=
      (he.mono hsub).intervalIntegrable_of_Icc ht.1
    have hgInt : IntervalIntegrable g volume a t := hg.intervalIntegrable a t
    have hphi : IntegrableOn (fun s ↦ K * e s + g s) (Icc a t) volume :=
      (((he.mono hsub).const_mul K).add hg.continuousOn).integrableOn_Icc
    have hFTC := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1
      (he.mono hsub)
      (fun s hs ↦ (hdiff s (hsub (Ioo_subset_Icc_self hs))).hasDerivAt.hasDerivWithinAt)
      hphi
      (fun s hs ↦ hderiv s (hsub (Ioo_subset_Icc_self hs)))
    rw [intervalIntegral.integral_add (heInt.const_mul K) hgInt,
      intervalIntegral.integral_const_mul] at hFTC
    have hgAll : IntervalIntegrable g volume a d := hg.intervalIntegrable a d
    have hprefix := intervalIntegral.integral_mono_interval (le_refl a) ht.1 ht.2
      (Filter.Eventually.of_forall hgn) hgAll
    linarith
  exact Evolution.le_mul_exp_of_le_const_add_mul_intervalIntegral he hK hintegral

end PDE.Analysis
