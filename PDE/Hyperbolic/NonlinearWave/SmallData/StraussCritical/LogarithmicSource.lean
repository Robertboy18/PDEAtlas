/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.PolarMeans
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.PowerSource
import CAS.IntegrationTactic

/-!
# The logarithmic gain at the critical Strauss exponent

Spherical Jensen converts the interior radius-mean lower bound into a radial
source density. At `p(p-2)=1`, its dependence on `a=t-r` is exactly reciprocal.
Integration over `4R≤a≤t/4` gives a logarithm with a strictly positive coefficient.
The wave-specific module derives the interior hypothesis from the PDE.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

/-- The critical power identity in the spherical Jensen estimate. -/
theorem critical_spherical_power_identity {c a r p : ℝ}
    (hc : 0 ≤ c) (ha : 0 < a) (hr : 0 < r) (hp : p * (p - 2) = 1) :
    r ^ 2 * (c * a ^ (2 - p) / r) ^ p = c ^ p * r ^ (2 - p) / a := by
  rw [Real.div_rpow (mul_nonneg hc (Real.rpow_nonneg ha.le _)) hr.le,
    Real.mul_rpow hc (Real.rpow_nonneg ha.le _), ← Real.rpow_mul ha.le]
  have he : (2 - p) * p = -1 := by cas using hp
  rw [he, Real.rpow_neg_one]
  have hrpow : r ^ 2 / r ^ p = r ^ (2 - p) := by
    rw [Real.rpow_sub hr, Real.rpow_two]
  calc
    _ = c ^ p * (r ^ 2 / r ^ p) / a := by ring
    _ = _ := by rw [hrpow]

/-- At the critical exponent, the interior mean forces a reciprocal radial
source density. The spherical field need not be radial or nonnegative. -/
theorem critical_spherical_density_lower_bound {v : ℝ^3 → ℝ} {c a r t p : ℝ} (hv : Continuous v)
    (hc : 0 < c) (ha : 0 < a) (hr : 0 < r) (hrt : r ≤ t) (hp : 2 < p) (hcritical : p * (p - 2) = 1)
    (hlower : c * a ^ (2 - p) ≤ r * unitSphereAverage 3 v 0 r) :
    c ^ p * t ^ (2 - p) / a ≤ r ^ 2 * unitSphereAverage 3 (fun x ↦ |v x| ^ p) 0 r := by
  have hb : c * a ^ (2 - p) / r ≤ |unitSphereAverage 3 v 0 r| := by
    apply le_trans _ (le_abs_self _)
    exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hlower)
  have hpow := Real.rpow_le_rpow (div_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ha.le _)) hr.le) hb
    (by linarith only [hp] : 0 ≤ p)
  have hj := abs_unitSphereAverage_rpow_le hv (by linarith only [hp] : 1 ≤ p) r
  have hmain := mul_le_mul_of_nonneg_left (hpow.trans hj) (sq_nonneg r)
  rw [critical_spherical_power_identity hc.le ha hr hcritical] at hmain
  have hm := Real.rpow_le_rpow_of_nonpos hr hrt (by linarith only [hp] : 2 - p ≤ 0)
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hc.le _)) ha.le).trans hmain

/-- The reciprocal displacement integrates to the exact logarithmic difference. -/
theorem integral_reciprocal_displacement {R t : ℝ} (hR : 0 < R) (ht : 16 * R ≤ t) :
    (∫ r in (3 * t / 4)..(t - 4 * R), 1 / (t - r)) = Real.log (t / 4) - Real.log (4 * R) := by
  cas using And.intro hR ht

/-- The interior spherical estimate yields a logarithm in the spatial
power integral. This statement is an integration lemma; the wave characteristic formula gives its
interior hypothesis. -/
theorem power_integral_logarithmic_lower_bound {v : ℝ^3 → ℝ} {c R t p : ℝ} (hv : ContDiff ℝ 2 v)
    (hvi : Integrable (fun x ↦ |v x| ^ p)) (hc : 0 < c) (hR : 0 < R) (ht : 16 * R ≤ t) (hp : 2 < p)
    (hcritical : p * (p - 2) = 1)
    (hlower : ∀ a, 4 * R ≤ a → a ≤ t / 4 → c * a ^ (2 - p) ≤
      (t - a) * unitSphereAverage 3 v 0 (t - a)) :
    unitSphereArea 3 * c ^ p * t ^ (2 - p) * (Real.log (t / 4) - Real.log (4 * R)) ≤ ∫ x : ℝ^3,
      |v x| ^ p := by
  let g := fun x : ℝ^3 ↦ |v x| ^ p
  have hg : ContDiff ℝ 1 g := ((contDiff_two_abs_rpow hp).comp hv).of_le (by norm_num)
  have hm : Continuous (unitSphereAverage 3 g 0) := ((contDiff_unitSphereAverage hg).comp
      (contDiff_const.prodMk contDiff_id)).continuous
  have htpos : 0 < t := by linarith only [ht, hR]
  have hab : 3 * t / 4 ≤ t - 4 * R := by linarith only [ht]
  have hdensity := integrableOn_sphericalMean_density hvi
  have hsubset : Ioc (3 * t / 4) (t - 4 * R) ⊆ Ioi (0 : ℝ) :=
    fun r hr ↦ lt_of_lt_of_le (by linarith only [htpos]) hr.1.le
  have hwide := setIntegral_mono_set hdensity (Eventually.of_forall fun r ↦ mul_nonneg (sq_nonneg r)
        (unitSphereAverage_nonneg (fun x ↦ Real.rpow_nonneg (abs_nonneg _) _) r))
    hsubset.eventuallySubset
  rw [← intervalIntegral.integral_of_le hab] at hwide
  have hi : IntervalIntegrable (fun r : ℝ ↦ 1 / (t - r)) volume
      (3 * t / 4) (t - 4 * R) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_const.div (continuous_const.sub continuous_id).continuousOn
      (fun r hr ↦ by linarith only [hr.2, hR])
  have hinner := intervalIntegral.integral_mono_on hab (hi.const_mul (c ^ p * t ^ (2 - p)))
    (((continuous_pow 2).fun_mul hm).intervalIntegrable _ _) ?_
  · rw [intervalIntegral.integral_const_mul, integral_reciprocal_displacement hR ht] at hinner
    have htotal := mul_le_mul_of_nonneg_left (hinner.trans hwide) (unitSphereArea_pos (n := 3)).le
    rw [← integral_eq_sphericalMean_integral hvi] at htotal
    simpa only [mul_assoc] using htotal
  · intro r hr
    have ha : 4 * R ≤ t - r := by linarith only [hr.2]
    have hat : t - r ≤ t / 4 := by linarith only [hr.1]
    have hrpos : 0 < r := by linarith only [hr.1, htpos]
    have he := critical_spherical_density_lower_bound hv.continuous hc
      (by linarith only [ha, hR] : 0 < t - r) hrpos
      (by linarith only [hr.2, hR] : r ≤ t) hp hcritical
      (by simpa only [sub_sub_cancel] using hlower (t - r) ha hat)
    simpa only [g, mul_one_div] using he

end WaveEquation.SmallData
