/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Rectangular conservation balances

A planar local conservation law integrates to a finite rectangular balance.
Integrability at its two time caps and vanishing integrated endpoint flux then
identify the whole-line integrals. No spacetime integrability is imposed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff

namespace PDE.Analysis

/-- Integrating a planar local conservation law on a finite rectangle gives
its two spatial endpoint fluxes. -/
theorem integral_energy_sub_eq_integral_endpoint_flux
    {e j : ℝ × ℝ → ℝ} {a b l r : ℝ}
    (he : ContDiff ℝ 1 e) (hj : ContDiff ℝ 1 j)
    (hab : a ≤ b) (hlr : l ≤ r)
    (hbalance : ∀ p ∈ Icc (a, l) (b, r),
      fderiv ℝ e p (1, 0) = fderiv ℝ j p (0, 1)) :
    (∫ x in l..r, e (b, x)) - (∫ x in l..r, e (a, x)) =
      ∫ t in a..b, j (t, r) - j (t, l) := by
  have hzero : EqOn (fun p ↦ fderiv ℝ e p (1, 0) +
      (-fderiv ℝ j p) (0, 1)) 0 (Icc (a, l) (b, r)) := by
    intro p hp
    simp only [neg_apply, Pi.zero_apply]
    rw [hbalance p hp]
    exact add_neg_cancel _
  have hid := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    e (-j) (fderiv ℝ e) (fun p ↦ -fderiv ℝ j p) (a, l) (b, r)
    ⟨hab, hlr⟩ he.continuous.continuousOn hj.continuous.neg.continuousOn
    (fun p _ ↦ (he.differentiable one_ne_zero p).hasFDerivAt)
    (fun p _ ↦ (hj.differentiable one_ne_zero p).hasFDerivAt.neg)
    ((integrableOn_zero : IntegrableOn (fun _ : ℝ × ℝ ↦ (0 : ℝ))
      (Icc (a, l) (b, r))).congr_fun (fun p hp ↦ (hzero hp).symm) measurableSet_Icc)
  rw [setIntegral_congr_fun measurableSet_Icc hzero] at hid
  simp only [Pi.zero_apply, integral_zero] at hid
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hid
  have hjr : IntervalIntegrable (fun t ↦ j (t, r)) volume a b :=
    (hj.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hjl : IntervalIntegrable (fun t ↦ j (t, l)) volume a b :=
    (hj.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  rw [intervalIntegral.integral_sub hjr hjl]
  linarith

/-- Removing the spatial ends of a finite balance uses integrability only at
its two energy caps and the independently established endpoint-flux limit. -/
theorem integral_energy_eq_of_tendsto_endpoint_flux_zero
    {e j : ℝ × ℝ → ℝ} {a b : ℝ}
    (he : ContDiff ℝ 1 e) (hj : ContDiff ℝ 1 j) (hab : a ≤ b)
    (hbalance : ∀ p, p.1 ∈ Icc a b →
      fderiv ℝ e p (1, 0) = fderiv ℝ j p (0, 1))
    (ha : Integrable (fun x ↦ e (a, x)))
    (hb : Integrable (fun x ↦ e (b, x)))
    (hflux : Filter.Tendsto
      (fun R : ℝ ↦ ∫ t in Icc a b, j (t, R) - j (t, -R))
      Filter.atTop (nhds 0)) :
    (∫ x, e (b, x)) = ∫ x, e (a, x) := by
  have hcap (t : ℝ) (ht : Integrable (fun x ↦ e (t, x))) :
      Filter.Tendsto (fun R : ℝ ↦ ∫ x in -R..R, e (t, x))
        Filter.atTop (nhds (∫ x, e (t, x))) := by
    have hc := aecover_Ioc (μ := (volume : Measure ℝ))
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
    apply (hc.integral_tendsto_of_countably_generated ht).congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    exact (intervalIntegral.integral_of_le (by linarith : -R ≤ R)).symm
  have hlim := (hcap b hb).sub (hcap a ha)
  have heq : (fun R : ℝ ↦ (∫ x in -R..R, e (b, x)) -
      ∫ x in -R..R, e (a, x)) =ᶠ[Filter.atTop]
      (fun R : ℝ ↦ ∫ t in Icc a b, j (t, R) - j (t, -R)) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    rw [integral_energy_sub_eq_integral_endpoint_flux he hj hab
      (by linarith : -R ≤ R) (fun p hp ↦ hbalance p ⟨hp.1.1, hp.2.1⟩),
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim (hflux.congr' heq.symm))

end PDE.Analysis
