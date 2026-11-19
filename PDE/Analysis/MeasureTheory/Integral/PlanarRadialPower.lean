/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Polar
public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial power integrals in the plane

Lebesgue integrals of powers of the distance `|x - y|` to a fixed point `x` of the plane, over
discs, exteriors of discs and annuli. They are `ℝ≥0∞`-valued, so they need no integrability
hypothesis; a measurable integrand dominated by one of these powers is integrable on the
corresponding set and its integral is bounded by the stated value.

## Main results

* `lintegral_fun_norm_sub_two`: radial integration in the plane about the point `x`.
* `lintegral_ball_rpow_sub_two`: `∫_{|x-y|<ρ} |x - y|^(β-2) dy = 2πρ^β/β` for `β > 0`.
* `lintegral_compl_ball_rpow_sub_three`: `∫_{|x-y|≥ρ} |x - y|^(β-3) dy = 2πρ^(β-1)/(1-β)` for
  `β < 1`.
* `lintegral_annulus_inv_sq`: `∫_{a≤|x-y|<b} |x - y|^(-2) dy = 2π log(b/a)`.
* `measureReal_ball_two`: the planar disc `B(x, r)` has area `πr²`.
* `lintegral_abs_sub_ge_inv_sq`: `∫_{|s-c|≥η} (s - c)⁻² ds = 2/η` for `η > 0`.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped ENNReal

namespace MeasureTheory

/-- The angular measure of the plane is `2π`. -/
theorem toSphere_univ_two :
    (volume : Measure (ℝ^2)).toSphere univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
    EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.ofReal_mul (by norm_num)]
  simp

/-- Radial integration in the plane about the point `x`. -/
theorem lintegral_fun_norm_sub_two (x : ℝ^2) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f ‖x - y‖ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi 0, ENNReal.ofReal r * f r := by
  have h := lintegral_fun_norm_sub_addHaar (volume : Measure (ℝ^2)) x hf
  simp only [finrank_euclideanSpace_fin, toSphere_univ_two] at h
  simp_rw [norm_sub_rev x]
  rw [h]
  simp

/-- Radial integration over the set of points whose distance to `x` lies in `S`. -/
theorem setLIntegral_fun_norm_sub_two (x : ℝ^2) {S : Set ℝ} (hS : MeasurableSet S)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y in {y | ‖x - y‖ ∈ S}, g ‖x - y‖ =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in S ∩ Ioi 0, ENNReal.ofReal r * g r := by
  have hmeas : MeasurableSet {y : ℝ^2 | ‖x - y‖ ∈ S} :=
    (measurable_const.sub measurable_id).norm hS
  rw [← lintegral_indicator hmeas]
  have hind : ({y : ℝ^2 | ‖x - y‖ ∈ S}.indicator fun y ↦ g ‖x - y‖) =
      fun y ↦ S.indicator g ‖x - y‖ := by
    funext y
    by_cases hy : ‖x - y‖ ∈ S
    · rw [indicator_of_mem (show y ∈ {y | ‖x - y‖ ∈ S} from hy), indicator_of_mem hy]
    · rw [indicator_of_notMem (show y ∉ {y | ‖x - y‖ ∈ S} from hy), indicator_of_notMem hy]
  rw [hind, lintegral_fun_norm_sub_two x (hg.indicator hS)]
  congr 1
  rw [← Measure.restrict_restrict hS, ← lintegral_indicator hS]
  congr 1
  funext r
  by_cases hr : r ∈ S <;> simp [hr]

/-- `∫₀^ρ r · r^(β-2) dr = ρ^β/β` for `β > 0`. -/
theorem lintegral_Iio_mul_rpow_sub_two {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β) :
    ∫⁻ r in Iio ρ ∩ Ioi 0, ENNReal.ofReal r * ENNReal.ofReal (r ^ (β - 2)) =
      ENNReal.ofReal (ρ ^ β / β) := by
  have hset : Iio ρ ∩ Ioi 0 = Ioo 0 ρ := by ext r; simp [and_comm]
  rw [hset]
  have hcongr : ∀ r ∈ Ioo (0 : ℝ) ρ,
      ENNReal.ofReal r * ENNReal.ofReal (r ^ (β - 2)) = ENNReal.ofReal (r ^ (β - 1)) := by
    intro r hr
    rw [← ENNReal.ofReal_mul hr.1.le]
    congr 1
    rw [show β - 1 = 1 + (β - 2) by ring, Real.rpow_add hr.1, Real.rpow_one]
  rw [setLIntegral_congr_fun measurableSet_Ioo hcongr]
  have hint : IntegrableOn (fun r : ℝ ↦ r ^ (β - 1)) (Ioo 0 ρ) := by
    rcases hρ.eq_or_lt with h | h
    · simp [← h]
    · exact (intervalIntegral.integrableOn_Ioo_rpow_iff h).2 (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le hρ,
      integral_rpow (Or.inl (by linarith))]
    rw [show β - 1 + 1 = β by ring, Real.zero_rpow hβ.ne', sub_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le _

/-- `∫_ρ^∞ r · r^(β-3) dr = ρ^(β-1)/(1-β)` for `ρ > 0` and `β < 1`. -/
theorem lintegral_Ici_mul_rpow_sub_three {ρ β : ℝ} (hρ : 0 < ρ) (hβ : β < 1) :
    ∫⁻ r in Ici ρ ∩ Ioi 0, ENNReal.ofReal r * ENNReal.ofReal (r ^ (β - 3)) =
      ENNReal.ofReal (ρ ^ (β - 1) / (1 - β)) := by
  have hset : Ici ρ ∩ Ioi 0 = Ici ρ := by
    ext r; simp only [mem_inter_iff, mem_Ici, mem_Ioi, and_iff_left_iff_imp]
    intro h; linarith
  rw [hset]
  have hcongr : ∀ r ∈ Ici ρ,
      ENNReal.ofReal r * ENNReal.ofReal (r ^ (β - 3)) = ENNReal.ofReal (r ^ (β - 2)) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hρ hr
    rw [← ENNReal.ofReal_mul hr0.le]
    congr 1
    rw [show β - 2 = 1 + (β - 3) by ring, Real.rpow_add hr0, Real.rpow_one]
  rw [setLIntegral_congr_fun measurableSet_Ici hcongr, ← setLIntegral_congr Ioi_ae_eq_Ici]
  have hint : IntegrableOn (fun r : ℝ ↦ r ^ (β - 2)) (Ioi ρ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hρ
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_Ioi_rpow_of_lt (by linarith) hρ, show β - 2 + 1 = β - 1 by ring]
    rw [neg_div, ← div_neg, neg_sub]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (hρ.trans hr).le _

/-- `∫_a^b r · r⁻² dr = log(b/a)` for `0 < a ≤ b`. -/
theorem lintegral_Ico_mul_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ r in Ico a b ∩ Ioi 0, ENNReal.ofReal r * ENNReal.ofReal (r ^ 2)⁻¹ =
      ENNReal.ofReal (Real.log (b / a)) := by
  have hset : Ico a b ∩ Ioi 0 = Ico a b := by
    ext r; simp only [mem_inter_iff, mem_Ico, mem_Ioi, and_iff_left_iff_imp]
    intro h; linarith [h.1]
  rw [hset]
  have hcongr : ∀ r ∈ Ico a b,
      ENNReal.ofReal r * ENNReal.ofReal (r ^ 2)⁻¹ = ENNReal.ofReal r⁻¹ := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    rw [← ENNReal.ofReal_mul hr0.le]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ico hcongr, setLIntegral_congr Ico_ae_eq_Ioc]
  have hint : IntegrableOn (fun r : ℝ ↦ r⁻¹) (Ioc a b) := by
    have := (intervalIntegral.intervalIntegrable_inv (μ := volume) (a := a) (b := b)
      (f := id) (fun r hr ↦ by
        rw [uIcc_of_le hab] at hr; exact (lt_of_lt_of_le ha hr.1).ne')
      continuousOn_id)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 this
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact inv_nonneg.2 (ha.trans hr.1).le

/-- **Disc integral of a subcritical power.** `∫_{|x-y|<ρ} |x - y|^(β-2) dy = 2πρ^β/β` for
`β > 0`. -/
theorem lintegral_ball_rpow_sub_two (x : ℝ^2) {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β) :
    ∫⁻ y in ball x ρ, ENNReal.ofReal (‖x - y‖ ^ (β - 2)) =
      ENNReal.ofReal (2 * Real.pi * ρ ^ β / β) := by
  have hball : ball x ρ = {y | ‖x - y‖ ∈ Iio ρ} := by
    ext y; simp [dist_eq_norm, norm_sub_rev y x]
  rw [hball, setLIntegral_fun_norm_sub_two x measurableSet_Iio
    (g := fun r ↦ ENNReal.ofReal (r ^ (β - 2))) (by fun_prop), lintegral_Iio_mul_rpow_sub_two hρ hβ,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **Exterior integral of a supercritical power.** `∫_{|x-y|≥ρ} |x - y|^(β-3) dy =
2πρ^(β-1)/(1-β)` for `ρ > 0` and `β < 1`. -/
theorem lintegral_compl_ball_rpow_sub_three (x : ℝ^2) {ρ β : ℝ} (hρ : 0 < ρ) (hβ : β < 1) :
    ∫⁻ y in (ball x ρ)ᶜ, ENNReal.ofReal (‖x - y‖ ^ (β - 3)) =
      ENNReal.ofReal (2 * Real.pi * ρ ^ (β - 1) / (1 - β)) := by
  have hball : (ball x ρ)ᶜ = {y | ‖x - y‖ ∈ Ici ρ} := by
    ext y; simp [dist_eq_norm, norm_sub_rev y x]
  rw [hball, setLIntegral_fun_norm_sub_two x measurableSet_Ici
    (g := fun r ↦ ENNReal.ofReal (r ^ (β - 3))) (by fun_prop),
    lintegral_Ici_mul_rpow_sub_three hρ hβ,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **Annulus integral of the critical power.** `∫_{a≤|x-y|<b} |x - y|^(-2) dy = 2π log(b/a)`
for `0 < a ≤ b`. -/
theorem lintegral_annulus_inv_sq (x : ℝ^2) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ y in ball x b \ ball x a, ENNReal.ofReal (‖x - y‖ ^ 2)⁻¹ =
      ENNReal.ofReal (2 * Real.pi * Real.log (b / a)) := by
  have hset : ball x b \ ball x a = {y | ‖x - y‖ ∈ Ico a b} := by
    ext y; simp [dist_eq_norm, norm_sub_rev y x, and_comm]
  rw [hset, setLIntegral_fun_norm_sub_two x measurableSet_Ico
    (g := fun r ↦ ENNReal.ofReal (r ^ 2)⁻¹) (by fun_prop), lintegral_Ico_mul_inv_sq ha hab,
    ← ENNReal.ofReal_mul (by positivity)]

/-- `∫_{|x-y|<ρ} c |x - y|^(β-2) dy = c · 2πρ^β/β` for `c ≥ 0` and `β > 0`. -/
theorem lintegral_ball_mul_rpow_sub_two (x : ℝ^2) {c ρ β : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hβ : 0 < β) :
    ∫⁻ y in ball x ρ, ENNReal.ofReal (c * ‖x - y‖ ^ (β - 2)) =
      ENNReal.ofReal (c * (2 * Real.pi * ρ ^ β / β)) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ball_rpow_sub_two x hρ hβ]

/-- `∫_{|x-y|≥ρ} c |x - y|^(β-3) dy = c · 2πρ^(β-1)/(1-β)` for `c ≥ 0`, `ρ > 0`, `β < 1`. -/
theorem lintegral_compl_ball_mul_rpow_sub_three (x : ℝ^2) {c ρ β : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hβ : β < 1) :
    ∫⁻ y in (ball x ρ)ᶜ, ENNReal.ofReal (c * ‖x - y‖ ^ (β - 3)) =
      ENNReal.ofReal (c * (2 * Real.pi * ρ ^ (β - 1) / (1 - β))) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_compl_ball_rpow_sub_three x hρ hβ]

/-- `∫_{a≤|x-y|<b} c |x - y|^(-2) dy = c · 2π log(b/a)` for `c ≥ 0` and `0 < a ≤ b`. -/
theorem lintegral_annulus_mul_inv_sq (x : ℝ^2) {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (hab : a ≤ b) :
    ∫⁻ y in ball x b \ ball x a, ENNReal.ofReal (c * (‖x - y‖ ^ 2)⁻¹) =
      ENNReal.ofReal (c * (2 * Real.pi * Real.log (b / a))) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_annulus_inv_sq x ha hab]

/-- The planar disc `B(x, r)` has area `πr²`. -/
theorem measureReal_ball_two (x : ℝ^2) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = Real.pi * r ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

/-- **The one-dimensional tail of the inverse square.** `∫_{|s-c|≥η} (s - c)⁻² ds = 2/η` for
`η > 0`. -/
theorem lintegral_abs_sub_ge_inv_sq (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ s in {s : ℝ | η ≤ |s - c|}, ENNReal.ofReal ((s - c) ^ 2)⁻¹ = ENNReal.ofReal (2 / η) := by
  have hmeas : MeasurableSet {s : ℝ | η ≤ |s - c|} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [← lintegral_indicator hmeas]
  have hind : ({s : ℝ | η ≤ |s - c|}.indicator fun s ↦ ENNReal.ofReal ((s - c) ^ 2)⁻¹) =
      fun s ↦ (Ici η).indicator (fun r ↦ ENNReal.ofReal (r ^ 2)⁻¹) ‖s - c‖ := by
    funext s
    rw [Real.norm_eq_abs]
    by_cases hs : η ≤ |s - c|
    · rw [indicator_of_mem (show s ∈ {s : ℝ | η ≤ |s - c|} from hs),
        indicator_of_mem (show |s - c| ∈ Ici η from hs), sq_abs]
    · rw [indicator_of_notMem (show s ∉ {s : ℝ | η ≤ |s - c|} from hs),
        indicator_of_notMem (show |s - c| ∉ Ici η from hs)]
  rw [hind, lintegral_fun_norm_sub_addHaar (volume : Measure ℝ) c
    ((Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ici)]
  rw [Measure.toSphere_apply_univ, Module.finrank_self, Real.volume_ball]
  have hrad : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (1 - 1)) *
      (Ici η).indicator (fun r ↦ ENNReal.ofReal (r ^ 2)⁻¹) r = ENNReal.ofReal η⁻¹ := by
    simp only [Nat.sub_self, pow_zero, ENNReal.ofReal_one, one_mul]
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici η ∩ Ioi (0 : ℝ) = Ici η := by
      ext r; simp only [mem_inter_iff, mem_Ici, mem_Ioi, and_iff_left_iff_imp]
      intro h; linarith
    rw [hset, ← setLIntegral_congr Ioi_ae_eq_Ici]
    have hcongr : ∀ r ∈ Ioi η, ENNReal.ofReal (r ^ 2)⁻¹ = ENNReal.ofReal (r ^ (-2 : ℝ)) := by
      intro r hr
      have hr0 : 0 < r := hη.trans hr
      rw [Real.rpow_neg hr0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
    have hint : IntegrableOn (fun r : ℝ ↦ r ^ (-2 : ℝ)) (Ioi η) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hη
    rw [← ofReal_integral_eq_lintegral_ofReal hint, integral_Ioi_rpow_of_lt (by norm_num) hη]
    · congr 1
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact Real.rpow_nonneg (hη.trans hr).le _
  rw [hrad]
  simp only [Nat.cast_one, one_mul]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end MeasureTheory
