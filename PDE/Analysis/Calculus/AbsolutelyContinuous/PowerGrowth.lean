/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AbsolutelyContinuous.Scalar
import CAS.IntegrationTactic

/-!
# Finite-time obstruction for absolutely continuous power growth

For `p > 1`, a positive curve satisfying `y' ≥ c y^p` almost everywhere cannot
remain finite beyond the time allowed by its initial negative power. The argument
uses the fundamental theorem for absolutely continuous curves, so no classical
pointwise differential inequality is required.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- Superlinear growth bounds the length of an absolutely continuous trajectory.
The strict inequality records that the terminal value is still finite and positive. -/
theorem mul_sub_lt_rpow_of_ae_power_le_deriv
    {y : ℝ → ℝ} {a b c p : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (hp : 1 < p)
    (hy : AbsolutelyContinuousOnInterval y a b) (hinit : 0 < y a)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ y t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Ioc a b), c * y t ^ p ≤ deriv y t) :
    (p - 1) * c * (b - a) < y a ^ (1 - p) := by
  have hm : MonotoneOn y (Icc a b) :=
    monotoneOn_of_absolutelyContinuous_of_ae_deriv_nonneg hab hy (by
      filter_upwards [hnonneg, hgrowth] with t ht hd
      exact (mul_nonneg hc (Real.rpow_nonneg ht p)).trans hd)
  have hpos : ∀ t ∈ Icc a b, 0 < y t := fun t ht ↦
    hinit.trans_le (hm (left_mem_Icc.mpr hab) ht ht.1)
  have hpow := absolutelyContinuous_rpow_of_pos_monotoneOn hab hy hm hinit (1 - p)
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b), DifferentiableAt ℝ y t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hy.ae_differentiableAt] with t ht hmem
    exact ht (by rw [uIcc_of_le hab]; exact ⟨hmem.1.le, hmem.2⟩)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (p - 1) * c ≤ deriv (fun s ↦ -(y s ^ (1 - p))) t := by
    filter_upwards [hdiff, hgrowth, ae_restrict_mem measurableSet_Ioc] with t hd hg ht
    have htpos := hpos t ⟨ht.1.le, ht.2⟩
    have hderiv := (hd.hasDerivAt.rpow_const (Or.inl htpos.ne') (p := 1 - p)).neg
    change HasDerivAt (fun s ↦ -(y s ^ (1 - p))) _ t at hderiv
    rw [hderiv.deriv]
    have hcancel : y t ^ ((1 - p) - 1) * y t ^ p = 1 := by
      rw [← Real.rpow_add htpos]
      simp
    have hmul := mul_le_mul_of_nonneg_left hg
      (mul_nonneg (sub_nonneg.mpr hp.le) (Real.rpow_nonneg htpos.le ((1 - p) - 1)))
    have hleft : (p - 1) * y t ^ ((1 - p) - 1) * (c * y t ^ p) =
        (p - 1) * c := by
      calc
        _ = ((p - 1) * c) * (y t ^ ((1 - p) - 1) * y t ^ p) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rw [hleft] at hmul
    convert hmul using 1
    ring
  have h := mul_sub_le_sub_of_ae_le_deriv hab hpow.neg hbound
  have hend := Real.rpow_pos_of_pos (hpos b (right_mem_Icc.mpr hab)) (1 - p)
  change (p - 1) * c * (b - a) ≤ -(y b ^ (1 - p)) - -(y a ^ (1 - p)) at h
  linarith

/-- A nonnegative absolutely continuous curve with superlinear production and
linear damping has a finite-horizon initial-moment bound. The exponential factor
is a uniform lower bound on the integrating-factor coefficient, not a sharp lifespan. -/
theorem mul_sub_lt_rpow_of_ae_damped_power_le_deriv
    {y : ℝ → ℝ} {a b c p lambda : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hp : 1 < p) (hlambda : 0 ≤ lambda)
    (hy : AbsolutelyContinuousOnInterval y a b) (hinit : 0 < y a)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ y t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Ioc a b),
      c * y t ^ p ≤ deriv y t + lambda * y t) :
    (p - 1) * (c * Real.exp (-(lambda * (b - a)) * (p - 1))) * (b - a) <
      y a ^ (1 - p) := by
  let z : ℝ → ℝ := fun t ↦ Real.exp (lambda * (t - a)) * y t
  have he : ContDiff ℝ 1 (fun t : ℝ ↦ Real.exp (lambda * (t - a))) := by fun_prop
  have hz : AbsolutelyContinuousOnInterval z a b :=
    he.contDiffOn.absolutelyContinuousOnInterval.mul hy
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b), DifferentiableAt ℝ y t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hy.ae_differentiableAt] with t ht hmem
    exact ht (by rw [uIcc_of_le hab]; exact ⟨hmem.1.le, hmem.2⟩)
  have hzinit : z a = y a := by simp [z]
  have hzgrowth : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (c * Real.exp (-(lambda * (b - a)) * (p - 1))) * z t ^ p ≤ deriv z t := by
    filter_upwards [hdiff, hnonneg, hgrowth, ae_restrict_mem measurableSet_Ioc]
      with t hd hn hg ht
    have hederiv : HasDerivAt (fun s : ℝ ↦ Real.exp (lambda * (s - a)))
        (lambda * Real.exp (lambda * (t - a))) t := by cas
    have hzderiv := hederiv.mul hd.hasDerivAt
    change HasDerivAt z _ t at hzderiv
    rw [hzderiv.deriv]
    have hexp : Real.exp (-(lambda * (b - a)) * (p - 1)) *
        (Real.exp (lambda * (t - a))) ^ p ≤ Real.exp (lambda * (t - a)) := by
      rw [← Real.exp_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hle := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht.2 hlambda) (sub_nonneg.mpr hp.le)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hc) (Real.rpow_nonneg hn p)
    have hg' := mul_le_mul_of_nonneg_left hg (Real.exp_pos (lambda * (t - a))).le
    dsimp only [z]
    rw [Real.mul_rpow (Real.exp_pos _).le hn]
    nlinarith
  have h := mul_sub_lt_rpow_of_ae_power_le_deriv hab
    (mul_nonneg hc (Real.exp_pos _).le) hp hz (hzinit.symm ▸ hinit)
    (hnonneg.mono fun t ht ↦ mul_nonneg (Real.exp_pos _).le ht) hzgrowth
  rwa [hzinit] at h

/-- The integrating-factor estimate with its time-dependent coefficient retained.
Unlike a constant lower bound for the coefficient, this estimate detects the exact
threshold between linear damping and superlinear production. -/
theorem integral_exp_lt_rpow_of_ae_damped_power_le_deriv
    {y : ℝ → ℝ} {a b c p lambda : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hp : 1 < p) (hy : AbsolutelyContinuousOnInterval y a b) (hinit : 0 < y a)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ y t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Ioc a b),
      c * y t ^ p ≤ deriv y t + lambda * y t) :
    (p - 1) * c * (∫ t in a..b, Real.exp (-(lambda * (t - a)) * (p - 1))) <
      y a ^ (1 - p) := by
  let z : ℝ → ℝ := fun t ↦ Real.exp (lambda * (t - a)) * y t
  have he : ContDiff ℝ 1 (fun t : ℝ ↦ Real.exp (lambda * (t - a))) := by fun_prop
  have hz : AbsolutelyContinuousOnInterval z a b :=
    he.contDiffOn.absolutelyContinuousOnInterval.mul hy
  have hzinit : z a = y a := by simp [z]
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b), DifferentiableAt ℝ y t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hy.ae_differentiableAt] with t ht hmem
    exact ht (by rw [uIcc_of_le hab]; exact ⟨hmem.1.le, hmem.2⟩)
  have hzgrowth : ∀ᵐ t ∂volume.restrict (Ioc a b),
      c * Real.exp (-(lambda * (t - a)) * (p - 1)) * z t ^ p ≤ deriv z t := by
    filter_upwards [hdiff, hnonneg, hgrowth] with t hd hn hg
    have hederiv : HasDerivAt (fun s : ℝ ↦ Real.exp (lambda * (s - a)))
        (lambda * Real.exp (lambda * (t - a))) t := by cas
    have hzderiv := hederiv.mul hd.hasDerivAt
    change HasDerivAt z _ t at hzderiv
    rw [hzderiv.deriv]
    have hexp : Real.exp (-(lambda * (t - a)) * (p - 1)) *
        (Real.exp (lambda * (t - a))) ^ p = Real.exp (lambda * (t - a)) := by
      cas
    have hg' := mul_le_mul_of_nonneg_left hg (Real.exp_pos (lambda * (t - a))).le
    dsimp only [z]
    rw [Real.mul_rpow (Real.exp_pos _).le hn]
    calc
      _ = c * (Real.exp (-(lambda * (t - a)) * (p - 1)) *
          (Real.exp (lambda * (t - a))) ^ p) * y t ^ p := by ring
      _ = c * Real.exp (lambda * (t - a)) * y t ^ p := by rw [hexp]
      _ ≤ _ := by nlinarith
  have hm : MonotoneOn z (Icc a b) :=
    monotoneOn_of_absolutelyContinuous_of_ae_deriv_nonneg hab hz (by
      filter_upwards [hzgrowth, hnonneg] with t hg hn
      exact (mul_nonneg (mul_nonneg hc (Real.exp_pos _).le)
        (Real.rpow_nonneg (mul_nonneg (Real.exp_pos _).le hn) p)).trans hg)
  have hpos : ∀ t ∈ Icc a b, 0 < z t := fun t ht ↦
    (hzinit.symm ▸ hinit).trans_le (hm (left_mem_Icc.mpr hab) ht ht.1)
  have hpow := absolutelyContinuous_rpow_of_pos_monotoneOn hab hz hm
    (hzinit.symm ▸ hinit) (1 - p)
  have hzdiff : ∀ᵐ t ∂volume.restrict (Ioc a b), DifferentiableAt ℝ z t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hz.ae_differentiableAt] with t ht hmem
    exact ht (by rw [uIcc_of_le hab]; exact ⟨hmem.1.le, hmem.2⟩)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (p - 1) * c * Real.exp (-(lambda * (t - a)) * (p - 1)) ≤
        deriv (fun s ↦ -(z s ^ (1 - p))) t := by
    filter_upwards [hzdiff, hzgrowth, ae_restrict_mem measurableSet_Ioc] with t hd hg ht
    have htpos := hpos t ⟨ht.1.le, ht.2⟩
    have hderiv := (hd.hasDerivAt.rpow_const (Or.inl htpos.ne') (p := 1 - p)).neg
    change HasDerivAt (fun s ↦ -(z s ^ (1 - p))) _ t at hderiv
    rw [hderiv.deriv]
    have hcancel : z t ^ ((1 - p) - 1) * z t ^ p = 1 := by
      rw [← Real.rpow_add htpos]
      simp
    have hmul := mul_le_mul_of_nonneg_left hg
      (mul_nonneg (sub_nonneg.mpr hp.le) (Real.rpow_nonneg htpos.le ((1 - p) - 1)))
    have hleft : (p - 1) * z t ^ ((1 - p) - 1) *
        (c * Real.exp (-(lambda * (t - a)) * (p - 1)) * z t ^ p) =
        (p - 1) * c * Real.exp (-(lambda * (t - a)) * (p - 1)) := by
      calc
        _ = ((p - 1) * c * Real.exp (-(lambda * (t - a)) * (p - 1))) *
            (z t ^ ((1 - p) - 1) * z t ^ p) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rw [hleft] at hmul
    convert hmul using 1
    ring
  have hi : IntervalIntegrable
      (fun t ↦ (p - 1) * c * Real.exp (-(lambda * (t - a)) * (p - 1))) volume a b :=
    (by fun_prop : Continuous _).intervalIntegrable a b
  have h := intervalIntegral.integral_mono_ae_restrict hab hi
    hpow.neg.intervalIntegrable_deriv ((ae_restrict_congr_set Ioc_ae_eq_Icc).mp hbound)
  rw [hpow.neg.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at h
  have hend := Real.rpow_pos_of_pos (hpos b (right_mem_Icc.mpr hab)) (1 - p)
  change _ ≤ -(z b ^ (1 - p)) - -(z a ^ (1 - p)) at h
  rw [hzinit] at h
  linarith

/-- Sharp finite-horizon necessary condition for a nonnegative trajectory with
positive linear damping and superlinear production. -/
theorem one_sub_exp_lt_mul_rpow_of_ae_damped_power_le_deriv
    {y : ℝ → ℝ} {a b c p lambda : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hp : 1 < p) (hlambda : 0 < lambda)
    (hy : AbsolutelyContinuousOnInterval y a b) (hinit : 0 < y a)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ y t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Ioc a b),
      c * y t ^ p ≤ deriv y t + lambda * y t) :
    c * (1 - Real.exp (-(lambda * (b - a)) * (p - 1))) < lambda * y a ^ (1 - p) := by
  have h := integral_exp_lt_rpow_of_ae_damped_power_le_deriv hab hc hp hy hinit
    hnonneg hgrowth
  have hp' : 0 < p - 1 := sub_pos.mpr hp
  have hi : (∫ t in a..b, Real.exp (-(lambda * (t - a)) * (p - 1))) =
      (1 - Real.exp (-(lambda * (b - a)) * (p - 1))) / (lambda * (p - 1)) := by
    cas using And.intro hlambda hp'
  rw [hi] at h
  have heq : lambda * ((p - 1) * c *
      ((1 - Real.exp (-(lambda * (b - a)) * (p - 1))) / (lambda * (p - 1)))) =
      c * (1 - Real.exp (-(lambda * (b - a)) * (p - 1))) := by
    cas using [hlambda, hp']
  have hmul := mul_lt_mul_of_pos_left h hlambda
  rwa [heq] at hmul

/-- If trajectories with a fixed positive initial value exist on every finite
interval, production cannot exceed damping at that initial value. The curves on
different intervals need not be identified. -/
theorem le_mul_rpow_of_global_damped_power_trajectories
    {m c p lambda : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hp : 1 < p)
    (hlambda : 0 < lambda)
    (hglobal : ∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ,
      AbsolutelyContinuousOnInterval y 0 T ∧ y 0 = m ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ y t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T),
        c * y t ^ p ≤ deriv y t + lambda * y t)) :
    c ≤ lambda * m ^ (1 - p) := by
  have hexp : Filter.Tendsto
      (fun T : ℝ ↦ Real.exp (-(lambda * T) * (p - 1))) Filter.atTop
      (nhds 0) := by
    simp_rw [neg_mul]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Filter.tendsto_id.const_mul_atTop hlambda).atTop_mul_const (sub_pos.mpr hp))
  have hlim : Filter.Tendsto
      (fun T : ℝ ↦ c * (1 - Real.exp (-(lambda * T) * (p - 1))))
      Filter.atTop (nhds c) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul c
  apply le_of_tendsto hlim
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  obtain ⟨y, hy, hzero, hn, hd⟩ := hglobal T hT
  have h := one_sub_exp_lt_mul_rpow_of_ae_damped_power_le_deriv hT.le hc hp hlambda
    hy (hzero.symm ▸ hm) hn hd
  simpa only [sub_zero, hzero] using h.le

/-- The sharp moment bound survives localization away from the initial time.
Only continuity, rather than absolute continuity or a derivative trace, is needed
at zero. -/
theorem one_sub_exp_le_mul_rpow_of_local_ae_damped_power_le_deriv
    {y : ℝ → ℝ} {T c p lambda : ℝ} (hT : 0 < T) (hc : 0 ≤ c)
    (hp : 1 < p) (hlambda : 0 < lambda) (hy : ContinuousOn y (Icc 0 T))
    (hlocal : ∀ a ∈ Ioc 0 T, AbsolutelyContinuousOnInterval y a T)
    (hinit : 0 < y 0)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ y t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      c * y t ^ p ≤ deriv y t + lambda * y t) :
    c * (1 - Real.exp (-(lambda * T) * (p - 1))) ≤ lambda * y 0 ^ (1 - p) := by
  let ε (k : ℕ) : ℝ := T / ((k : ℝ) + 1)
  have hε (k : ℕ) : ε k ∈ Ioc 0 T := by
    refine ⟨by dsimp [ε]; positivity, ?_⟩
    exact div_le_self hT.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa only [ε, div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
  have hylim : Filter.Tendsto (fun k ↦ y (ε k)) Filter.atTop (nhds (y 0)) :=
    (hy.continuousWithinAt (left_mem_Icc.mpr hT.le)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hεlim,
        Filter.Eventually.of_forall fun k ↦ Ioc_subset_Icc_self (hε k)⟩)
  have hleft : Filter.Tendsto
      (fun k ↦ c * (1 - Real.exp (-(lambda * (T - ε k)) * (p - 1))))
      Filter.atTop (nhds (c * (1 - Real.exp (-(lambda * T) * (p - 1))))) := by
    simpa only [sub_zero, ← Real.exp_eq_exp_ℝ] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (((hεlim.const_sub T).const_mul lambda).neg.mul_const (p - 1)).exp).const_mul c
  have hright : Filter.Tendsto (fun k ↦ lambda * y (ε k) ^ (1 - p))
      Filter.atTop (nhds (lambda * y 0 ^ (1 - p))) :=
    (hylim.rpow_const (Or.inl hinit.ne')).const_mul lambda
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hylim.eventually (lt_mem_nhds hinit)] with k hk
  exact (one_sub_exp_lt_mul_rpow_of_ae_damped_power_le_deriv (hε k).2 hc hp hlambda
    (hlocal (ε k) (hε k)) hk
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc (hε k).1.le le_rfl) hnonneg)
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc (hε k).1.le le_rfl) hgrowth)).le

/-- Global existence of curves locally absolutely continuous at positive times
already gives the sharp initial-moment restriction. No derivative at zero is assumed. -/
theorem le_mul_rpow_of_global_local_damped_power_trajectories
    {m c p lambda : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hp : 1 < p)
    (hlambda : 0 < lambda)
    (hglobal : ∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ,
      ContinuousOn y (Icc 0 T) ∧
      (∀ a ∈ Ioc 0 T, AbsolutelyContinuousOnInterval y a T) ∧ y 0 = m ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ y t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T),
        c * y t ^ p ≤ deriv y t + lambda * y t)) :
    c ≤ lambda * m ^ (1 - p) := by
  have hexp : Filter.Tendsto
      (fun T : ℝ ↦ Real.exp (-(lambda * T) * (p - 1))) Filter.atTop (nhds 0) := by
    simp_rw [neg_mul]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Filter.tendsto_id.const_mul_atTop hlambda).atTop_mul_const (sub_pos.mpr hp))
  have hlim : Filter.Tendsto
      (fun T : ℝ ↦ c * (1 - Real.exp (-(lambda * T) * (p - 1))))
      Filter.atTop (nhds c) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul c
  apply le_of_tendsto hlim
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  obtain ⟨y, hy, hlocal, hzero, hn, hd⟩ := hglobal T hT
  have h := one_sub_exp_le_mul_rpow_of_local_ae_damped_power_le_deriv hT hc hp hlambda
    hy hlocal (hzero.symm ▸ hm) hn hd
  simpa only [hzero] using h

/-- An interior derivative pointing strictly upward at a level prevents a
continuous curve from crossing below that level. No derivative at zero is needed. -/
theorem le_of_continuousOn_deriv_pos_at_level
    {y : ℝ → ℝ} {T k : ℝ} (hy : ContinuousOn y (Icc 0 T)) (hzero : k < y 0)
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ y t)
    (hlevel : ∀ t ∈ Ioo 0 T, y t = k → 0 < deriv y t) :
    ∀ t ∈ Ico 0 T, k ≤ y t := by
  intro t ht
  rcases ht.1.eq_or_lt with heq | htpos
  · simpa only [← heq] using hzero.le
  let ε (j : ℕ) : ℝ := t / ((j : ℝ) + 1)
  have hε (j : ℕ) : ε j ∈ Ioc 0 t := by
    refine ⟨by dsimp [ε]; positivity, ?_⟩
    exact div_le_self htpos.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa only [ε, div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
  have hylim : Filter.Tendsto (fun j ↦ y (ε j)) Filter.atTop (nhds (y 0)) :=
    (hy.continuousWithinAt ⟨le_rfl, (htpos.trans ht.2).le⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hεlim,
        Filter.Eventually.of_forall fun j ↦ ⟨(hε j).1.le, (hε j).2.trans ht.2.le⟩⟩)
  obtain ⟨j, hj⟩ := (hylim.eventually (lt_mem_nhds hzero)).exists
  have hf := image_le_of_deriv_right_lt_deriv_boundary (B := fun _ ↦ -k) (B' := fun _ ↦ 0)
    ((hy.mono (Icc_subset_Icc (hε j).1.le ht.2.le)).neg)
    (fun x hx ↦ ((hd x ⟨(hε j).1.trans_le hx.1, hx.2.trans ht.2⟩).hasDerivAt.neg).hasDerivWithinAt)
    (neg_le_neg hj.le) (fun x ↦ hasDerivAt_const x (-k)) (by
      intro x hx heq
      exact neg_lt_zero.mpr (hlevel x ⟨(hε j).1.trans_le hx.1, hx.2.trans ht.2⟩
        (neg_inj.mp heq))) (right_mem_Icc.mpr (hε j).2)
  exact neg_le_neg_iff.mp hf

/-- The global local moment bound also applies when the initial moments merely
have a common positive lower bound. -/
theorem le_mul_rpow_of_global_local_damped_power_trajectories_le
    {m c p lambda : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hp : 1 < p)
    (hlambda : 0 < lambda)
    (hglobal : ∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ,
      ContinuousOn y (Icc 0 T) ∧
      (∀ a ∈ Ioc 0 T, AbsolutelyContinuousOnInterval y a T) ∧ m ≤ y 0 ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ y t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T),
        c * y t ^ p ≤ deriv y t + lambda * y t)) :
    c ≤ lambda * m ^ (1 - p) := by
  have hexp : Filter.Tendsto
      (fun T : ℝ ↦ Real.exp (-(lambda * T) * (p - 1))) Filter.atTop (nhds 0) := by
    simp_rw [neg_mul]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Filter.tendsto_id.const_mul_atTop hlambda).atTop_mul_const (sub_pos.mpr hp))
  have hlim : Filter.Tendsto
      (fun T : ℝ ↦ c * (1 - Real.exp (-(lambda * T) * (p - 1))))
      Filter.atTop (nhds c) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul c
  apply le_of_tendsto hlim
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  obtain ⟨y, hy, hlocal, hzero, hn, hd⟩ := hglobal T hT
  have h := one_sub_exp_le_mul_rpow_of_local_ae_damped_power_le_deriv hT hc hp hlambda
    hy hlocal (hm.trans_le hzero) hn hd
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hm hzero (by linarith)) hlambda.le)

end PDE.Analysis
