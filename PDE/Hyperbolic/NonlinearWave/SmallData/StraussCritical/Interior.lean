/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Representation
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.ShellTransfer
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic

/-!
# An interior lower bound forced by the outgoing shell

For `a = t-r` between `4R` and `t/4`, the characteristic source cone contains
the free outgoing shell at every time between `a` and `2a`. Integrating its
radius-weighted lower bound gives `r M_u(t,r) ≥ c a^(2-p)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

/-- Joint continuity of the radius-weighted source in ordinary time-radius coordinates. -/
theorem continuous_radiusMean_uncurry {f : ℝ^4 → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : ℝ × ℝ ↦ z.2 * waveSphericalMean f 0 z.1 z.2) := by
  have hp : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦
      timeSpaceCons z.1 (EuclideanSpace.single (0 : Fin 1) z.2)) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · convert (contDiff_fst : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.1)) using 1
      funext z
      exact timeSpaceCons_zero _ _
    · convert (contDiff_snd : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.2)) using 1
      funext z
      exact timeSpaceCons_single_one _ _
  simpa only [Function.comp_def, radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one] using
    (contDiff_radiusMean hf).continuous.comp hp.continuous

/-- Continuous integrands remain continuous under two continuous moving endpoints. -/
theorem continuous_intervalIntegral_moving_endpoints {f : ℝ → ℝ → ℝ} {a b : ℝ → ℝ}
    (hf : Continuous f.uncurry) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun s ↦ ∫ r in a s..b s, f s r) := by
  have h₁ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf ha
  have h₂ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hb
  convert h₂.fun_sub h₁ using 1
  funext s
  have hc : Continuous (f s) := hf.comp (continuous_const.prodMk continuous_id)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (a s)) (hc.intervalIntegrable (a s) (b s))
  linarith only [he]

/-- The folded characteristic source is nonnegative on the forward cone. -/
theorem characteristic_source_integral_nonneg {f : ℝ^4 → ℝ} (hf : ∀ z, 0 ≤ f z) {t r s : ℝ}
    (hr : 0 ≤ r) (hs : s ∈ Icc 0 t) :
    0 ≤ ∫ ρ in |r - (t - s)|..(r + (t - s)), ρ * waveSphericalMean f 0 s ρ := by
  apply intervalIntegral.integral_nonneg
    (abs_le.mpr ⟨by linarith only [hr, hs.2], by linarith only [hr, hs.2]⟩)
  intro ρ hρ
  exact mul_nonneg ((abs_nonneg _).trans hρ.1)
    (unitSphereAverage_nonneg (fun x ↦ hf (timeSpaceCons s x)) ρ)

/-- The exact positive coefficient obtained by integrating the outgoing shell
over the times `[a,2a]`. -/
def interiorSourceCoefficient (R H p : ℝ) : ℝ :=
  shellSourceCoefficient R H p / (4 * unitSphereArea 3) * (2 : ℝ) ^ (1 - p)

/-- The interior coefficient is strictly positive for positive initial mass. -/
theorem interiorSourceCoefficient_pos {R H p : ℝ} (hR : 0 < R) (hH : 0 < H) :
    0 < interiorSourceCoefficient R H p :=
  mul_pos (div_pos (shellSourceCoefficient_pos hR hH)
    (mul_pos (by norm_num) unitSphereArea_pos)) (Real.rpow_pos_of_pos (by norm_num) _)

/-- A wave with positive compact velocity has an interior spherical-mean
lower bound. -/
theorem radiusMean_semilinear_interior_lower_bound {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p t a : ℝ}
    (hu : ContDiff ℝ 2 u) (hh : ContDiff ℝ 2 h) (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0)
    (hhn : ∀ y, 0 ≤ h y) (hR : 0 < R) (hp : 2 < p) (hH : 0 < ∫ y : ℝ^3, h y)
    (hwave : ∀ s, 0 < s → ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) =
      |u (timeSpaceCons s x)| ^ p)
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (ha : 4 * R ≤ a) (hat : a ≤ t / 4) :
    interiorSourceCoefficient R (∫ y : ℝ^3, h y) p * a ^ (2 - p) ≤
      (t - a) * waveSphericalMean u 0 t (t - a) := by
  let f := fun z : ℝ^4 ↦ |u z| ^ p
  let J := fun s ↦ (1 / 2 : ℝ) * ∫ ρ in |t - a - (t - s)|..(t - a + (t - s)),
      ρ * waveSphericalMean f 0 s ρ
  let c := shellSourceCoefficient R (∫ y : ℝ^3, h y) p / (2 * unitSphereArea 3)
  have hc : 0 < c := div_pos (shellSourceCoefficient_pos hR hH)
    (mul_pos (by norm_num) unitSphereArea_pos)
  have ha0 : 0 < a := by linarith only [hR, ha]
  have ht0 : 0 ≤ t := by linarith only [ha0, hat]
  have hr0 : 0 ≤ t - a := by linarith only [ha0, hat]
  have hf : ContDiff ℝ 1 f := ((contDiff_two_abs_rpow hp).comp hu).of_le (by norm_num)
  have hJ : Continuous J := by
    apply continuous_const.fun_mul
    apply continuous_intervalIntegral_moving_endpoints
      (f := fun s ρ ↦ ρ * waveSphericalMean f 0 s ρ) (continuous_radiusMean_uncurry hf)
    · fun_prop
    · fun_prop
  have hJn (s : ℝ) (hs : s ∈ Icc 0 t) : 0 ≤ J s :=
    mul_nonneg (by norm_num) (characteristic_source_integral_nonneg
        (fun z ↦ Real.rpow_nonneg (abs_nonneg _) _) hr0 hs)
  have hinner (s : ℝ) (hs : s ∈ Icc a (2 * a)) :
      (1 / 2 : ℝ) * c * (2 * a) ^ (1 - p) ≤ J s := by
    have hsR : 2 * R ≤ s := by linarith only [ha, hs.1, hR]
    have hs0 : 0 < s := ha0.trans_le hs.1
    have hlow := semilinear_shell_radius_integral_lower_bound
      hu hh hhs hhn hR hp hH hwave hzero hinitial hsR
    have hm : (∫ ρ in (s - 2 * R)..(s + 2 * R), ρ * waveSphericalMean f 0 s ρ) ≤
        ∫ ρ in |t - a - (t - s)|..(t - a + (t - s)),
          ρ * waveSphericalMean f 0 s ρ := by
      apply intervalIntegral.integral_mono_interval
        (abs_le.mpr ⟨by linarith only [ha, hs.1, hR],
          by linarith only [ha, hR]⟩)
        (by linarith only [hR]) (by linarith only [hat, ha, hs.2, hR])
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
        exact mul_nonneg ((abs_nonneg _).trans hρ.1.le)
          (unitSphereAverage_nonneg (fun x ↦ Real.rpow_nonneg (abs_nonneg _) _) ρ)
      · simpa only [id_eq, waveSphericalMean, Function.comp_def] using
          ((continuous_id.fun_mul (continuous_sphericalMean_radius
            (hf.comp (contDiff_timeSpaceCons_spatial 3 s)))).intervalIntegrable
              |t - a - (t - s)| (t - a + (t - s)))
    have hpw := Real.rpow_le_rpow_of_nonpos hs0 hs.2 (by linarith only [hp] : 1 - p ≤ 0)
    change c * s ^ (1 - p) ≤ _ at hlow
    have hb := (mul_le_mul_of_nonneg_left hpw hc.le).trans (hlow.trans hm)
    dsimp [J]
    nlinarith only [hb]
  have htime : (1 / 2 : ℝ) * c * (2 * a) ^ (1 - p) * a ≤ ∫ s in (0 : ℝ)..t, J s := by
    have hsub := intervalIntegral.integral_mono_on (μ := volume)
      (by linarith only [ha0] : a ≤ 2 * a)
      (continuous_const.intervalIntegrable a (2 * a)) (hJ.intervalIntegrable a (2 * a)) hinner
    have hwide := intervalIntegral.integral_mono_interval (μ := volume)
      ha0.le (by linarith only [ha0] : a ≤ 2 * a) (by linarith only [hat, ha0] : 2 * a ≤ t)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hJn s ⟨hs.1.le, hs.2⟩) (hJ.intervalIntegrable 0 t)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hsub
    nlinarith only [hsub, hwide]
  have he := radiusMean_eq_characteristic_integrals hu hf (hh.of_le (by norm_num))
    hwave hzero hinitial ht0 (t - a)
  have hfree : 0 ≤ ∫ ρ in |t - a - t|..(t - a + t),
      ρ * unitSphereAverage 3 h 0 ρ := by
    apply intervalIntegral.integral_nonneg
      (abs_le.mpr ⟨by linarith only [hr0, ht0], by linarith only [hr0, ht0]⟩)
    intro ρ hρ
    exact mul_nonneg ((abs_nonneg _).trans hρ.1) (unitSphereAverage_nonneg hhn ρ)
  have hcoef : (1 / 2 : ℝ) * c * (2 * a) ^ (1 - p) * a =
      interiorSourceCoefficient R (∫ y : ℝ^3, h y) p * a ^ (2 - p) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha0.le]
    have hpw : a ^ (1 - p) * a = a ^ (2 - p) := by
      cas using ha0
    dsimp [c, interiorSourceCoefficient]
    calc
      _ = shellSourceCoefficient R (∫ y : ℝ^3, h y) p / (4 * unitSphereArea 3) *
          (2 : ℝ) ^ (1 - p) * (a ^ (1 - p) * a) := by ring
      _ = _ := by rw [hpw]
  rw [hcoef] at htime
  simp only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one] at he
  change _ = _ + ∫ s in (0 : ℝ)..t, J s at he
  linarith only [he, htime, hfree]

end WaveEquation.SmallData
