/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import PDE.Spaces.Sobolev.Inequalities.Hardy.SingularInterval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Singular Hardy domains from the weighted derivative

Cauchy–Schwarz controls the singular boundary product by a shrinking integral
of the weighted derivative. This supplies the vanishing endpoint flux required
by the sharp square-completion identities, without a Taylor expansion at the endpoint.
Integration by parts on truncated intervals then proves square integrability of
the singular primitive; its domain is not an additional assumption.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace SobolevSpace.Hardy

/-- A primitive vanishing at zero has a boundary flux bounded by the local square
integral of its weighted derivative. The weight exponent is any natural number. -/
theorem primitive_sq_div_pow_le_integral
    {v vX : ℝ → ℝ} (k : ℕ) (hv : ∀ x, HasDerivAt v (vX x) x) (hv0 : v 0 = 0)
    (hq : MemLp (fun x ↦ vX x / x ^ k) 2 volume) {x : ℝ} (hx : 0 < x) :
    v x ^ 2 / x ^ (2 * k + 1) ≤
      (∫ y in Ioo 0 x, (vX y / y ^ k) ^ 2) / (2 * k + 1 : ℕ) := by
  have hw : MemLp (fun y : ℝ ↦ y ^ k) 2 (volume.restrict (Ioo 0 x)) := by
    apply MemLp.of_bound (by fun_prop) (x ^ k)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1.le k)]
    exact pow_le_pow_left₀ hy.1.le hy.2.le k
  have hprod := (hq.restrict (Ioo 0 x)).integrable_mul hw
  have hprodEq : (fun y ↦ vX y / y ^ k * y ^ k) =ᵐ[volume.restrict (Ioo 0 x)] vX := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact div_mul_cancel₀ _ (pow_ne_zero k hy.1.ne')
  have hmean : (∫ y in Ioo 0 x, vX y / y ^ k * y ^ k) = v x := by
    rw [integral_congr_ae hprodEq]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hv y)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).mpr (hprod.congr hprodEq))
    rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, hv0, sub_zero] at h
    exact h
  have hweight : (∫ y in Ioo (0 : ℝ) x, (y ^ k) ^ 2) =
      x ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le]
    simp only [← pow_mul, mul_comm k 2, integral_pow, zero_pow (by omega : 2 * k + 1 ≠ 0),
      sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hcs := (abs_integral_le_integral_abs
    (f := fun y ↦ vX y / y ^ k * y ^ k) (μ := volume.restrict (Ioo 0 x))).trans
    (integral_abs_mul_le_sqrt_integral_sq (hq.restrict _) hw)
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hcs
  rw [sq_abs, hmean, mul_pow,
    Real.sq_sqrt (integral_nonneg fun y ↦ sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun y ↦ sq_nonneg _), hweight] at hsq
  apply (div_le_iff₀ (pow_pos hx _)).mpr
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsq

/-- The singular boundary flux tends to zero whenever the weighted derivative
is square integrable. This includes nonsmooth behavior of the derivative at zero. -/
theorem tendsto_primitive_sq_div_pow_zero
    {v vX : ℝ → ℝ} (k : ℕ) (hv : ∀ x, HasDerivAt v (vX x) x) (hv0 : v 0 = 0)
    (hq : MemLp (fun x ↦ vX x / x ^ k) 2 volume) :
    Tendsto (fun x ↦ v x ^ 2 / x ^ (2 * k + 1)) (𝓝[>] 0) (𝓝 0) := by
  have hmass : Tendsto (fun x ↦ (∫ y in Ioo 0 x, (vX y / y ^ k) ^ 2) /
      (2 * k + 1 : ℕ)) (𝓝[>] 0) (𝓝 0) := by
    have hcont := intervalIntegral.continuous_primitive
      (fun _ _ ↦ hq.integrable_sq.intervalIntegrable) 0
    have ht := ((hcont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).div_const
      ((2 * k + 1 : ℕ) : ℝ)
    simp only [intervalIntegral.integral_same, zero_div] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo]
  apply squeeze_zero' _ _ hmass
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_nonneg (sq_nonneg _) (pow_nonneg hx.le _)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact primitive_sq_div_pow_le_integral k hv hv0 hq hx

/-- Differentiating the flux exposes the two square-integrable Hardy factors. -/
theorem hasDerivAt_primitive_flux
    {v vX : ℝ → ℝ} (k : ℕ) {x : ℝ}
    (hv : HasDerivAt v (vX x) x) (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ v y ^ 2 / y ^ (2 * k + 1))
      (2 * (v x / x ^ (k + 1)) * (vX x / x ^ k) -
        (2 * k + 1 : ℕ) * (v x / x ^ (k + 1)) ^ 2) x := by
  apply ((hv.pow 2).div ((hasDerivAt_id x).pow (2 * k + 1))
    (pow_ne_zero _ hx)).congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, Nat.reduceSub, mul_one, pow_succ, pow_mul, mul_pow]
  field_simp
  ring

private theorem memLp_div_pow_away_zero {v : ℝ → ℝ} {ε L : ℝ}
    (hv : Continuous v) (hε : 0 < ε) (k : ℕ) :
    MemLp (fun x ↦ v x / x ^ k) 2 (volume.restrict (Ioo ε L)) := by
  apply (memLp_two_iff_integrable_sq
    (hv.measurable.div (measurable_id.pow_const k)).aestronglyMeasurable).mpr
  have hc : ContinuousOn (fun x ↦ v x / x ^ k) (Icc ε L) :=
    hv.continuousOn.div (continuous_id.pow k).continuousOn
      (fun x hx ↦ pow_ne_zero k (hε.trans_le hx.1).ne')
  exact (hc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- A uniform bound on truncated singular primitive norms. Its constant is used
only to prove domain membership; the sharp constants follow from square completion. -/
theorem integral_primitive_div_pow_sq_le
    {v vX : ℝ → ℝ} {k : ℕ} (hk : 0 < k)
    (hv : ∀ x, HasDerivAt v (vX x) x) (hv0 : v 0 = 0)
    (hq : MemLp (fun x ↦ vX x / x ^ k) 2 volume)
    {ε L : ℝ} (hε : 0 < ε) (hεL : ε < L) :
    (∫ x in Ioo ε L, (v x / x ^ (k + 1)) ^ 2) ≤
      ∫ x, (vX x / x ^ k) ^ 2 := by
  let F : ℝ → ℝ := fun x ↦ v x / x ^ (k + 1)
  let Q : ℝ → ℝ := fun x ↦ vX x / x ^ k
  let p : ℝ := (2 * k + 1 : ℕ)
  have hF : MemLp F 2 (volume.restrict (Ioo ε L)) :=
    memLp_div_pow_away_zero (continuous_iff_continuousAt.mpr fun x ↦ (hv x).continuousAt) hε _
  have hQ : MemLp Q 2 volume := hq
  have hQR := hQ.restrict (Ioo ε L)
  have hflux : IntegrableOn (fun x ↦ 2 * F x * Q x - p * F x ^ 2) (Ioo ε L) :=
    ((hF.integrable_mul hQR).const_mul 2).sub
      (hF.integrable_sq.const_mul p) |>.congr (Eventually.of_forall fun x ↦ by
        simp only [Pi.sub_apply, Pi.mul_apply]; ring)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hasDerivAt_primitive_flux k (hv x)
      (hε.trans_le ((uIcc_of_le hεL.le) ▸ hx).1).ne')
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hεL.le).mpr hflux)
  rw [intervalIntegral.integral_of_le hεL.le, integral_Ioc_eq_integral_Ioo] at hFTC
  have hp : 3 ≤ p := by dsimp only [p]; norm_cast; omega
  have hyoung :
      (∫ x in Ioo ε L, 2 * F x * Q x - p * F x ^ 2) ≤
        (∫ x in Ioo ε L, Q x ^ 2) - 2 * ∫ x in Ioo ε L, F x ^ 2 := by
    rw [← integral_const_mul, ← integral_sub hQR.integrable_sq (hF.integrable_sq.const_mul 2)]
    apply integral_mono hflux (hQR.integrable_sq.sub (hF.integrable_sq.const_mul 2))
    intro x
    dsimp only [Pi.sub_apply]
    have hpF := mul_le_mul_of_nonneg_right hp (sq_nonneg (F x))
    nlinarith [sq_nonneg (F x - Q x)]
  have hQmono (s : Set ℝ) : (∫ x in s, Q x ^ 2) ≤ ∫ x, Q x ^ 2 :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun x ↦ sq_nonneg _) hQ.integrable_sq
  have hεflux : v ε ^ 2 / ε ^ (2 * k + 1) ≤ ∫ x, Q x ^ 2 := by
    have hlocal := primitive_sq_div_pow_le_integral k hv hv0 hq hε
    have hp1 : (1 : ℝ) ≤ (2 * k + 1 : ℕ) := by norm_cast; omega
    exact hlocal.trans ((div_le_self (integral_nonneg fun x ↦ sq_nonneg _) hp1).trans (hQmono _))
  have hLflux : 0 ≤ v L ^ 2 / L ^ (2 * k + 1) :=
    div_nonneg (sq_nonneg _) (pow_nonneg (hε.trans hεL).le _)
  change (∫ x in Ioo ε L, F x ^ 2) ≤ ∫ x, Q x ^ 2
  change (∫ x in Ioo ε L, 2 * F x * Q x - p * F x ^ 2) =
    v L ^ 2 / L ^ (2 * k + 1) - v ε ^ 2 / ε ^ (2 * k + 1) at hFTC
  linarith [hQmono (Ioo ε L)]

/-- Square integrability of the weighted derivative supplies the singular Hardy
primitive domain on each finite positive interval. No primitive bound is assumed. -/
theorem memLp_primitive_div_pow
    {v vX : ℝ → ℝ} {k : ℕ} (hk : 0 < k)
    (hv : ∀ x, HasDerivAt v (vX x) x) (hv0 : v 0 = 0)
    (hq : MemLp (fun x ↦ vX x / x ^ k) 2 volume) {L : ℝ} (hL : 0 < L) :
    MemLp (fun x ↦ v x / x ^ (k + 1)) 2 (volume.restrict (Ioo 0 L)) := by
  have hc : Continuous v := continuous_iff_continuousAt.mpr fun x ↦ (hv x).continuousAt
  apply (memLp_two_iff_integrable_sq
    (hc.measurable.div (measurable_id.pow_const (k + 1))).aestronglyMeasurable).mpr
  have hε (n : ℕ) : 0 < 1 / (n + 1 : ℝ) := by positivity
  have hlocal (n : ℕ) :
      IntegrableOn (fun x ↦ (v x / x ^ (k + 1)) ^ 2) (Ioc (1 / (n + 1 : ℝ)) L) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr
      (memLp_div_pow_away_zero hc (hε n) (k + 1)).integrable_sq
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∫ x in Ioc (1 / (n + 1 : ℝ)) L, ‖(v x / x ^ (k + 1)) ^ 2‖) ≤
        ∫ x, (vX x / x ^ k) ^ 2 := by
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hL)]
      with n hn
    simp only [Real.norm_eq_abs, abs_sq, integral_Ioc_eq_integral_Ioo]
    exact integral_primitive_div_pow_sq_le hk hv hv0 hq (hε n) hn
  exact (integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
    hlocal tendsto_one_div_add_atTop_nhds_zero_nat hbound).mono_set Ioo_subset_Ioc_self

end SobolevSpace.Hardy
