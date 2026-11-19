/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.PolarMeans
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.SourceGrowth
import CAS.ExactTactic

/-!
# Transferring the outgoing shell into the characteristic source

Polar integration converts the free wave's spatial power integral into a lower
bound for the radius-weighted spherical source. The shell is widened to avoid
any convention about its boundary.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

/-- A continuous spherical mean is continuous as a function of its radius. -/
theorem continuous_sphericalMean_radius {f : ℝ^3 → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (unitSphereAverage 3 f 0) :=
  ((contDiff_unitSphereAverage hf).comp (contDiff_const.prodMk contDiff_id)).continuous

/-- A nonnegative function supported in an annulus is controlled by the
radius-weighted spherical mean of any larger continuous function. -/
theorem integral_le_radius_sphericalMean_integral {f g : ℝ^3 → ℝ} {a b : ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hfi : Integrable f) (hfn : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (ha : 0 ≤ a) (hab : a ≤ b) (hs : ∀ x, ‖x‖ ≤ a ∨ b < ‖x‖ → f x = 0) :
    (∫ x : ℝ^3, f x) ≤ unitSphereArea 3 * b * ∫ r in a..b, r * unitSphereAverage 3 g 0 r := by
  have he := integral_eq_sphericalMean_annulus hfi ha hab ?_
  · rw [he, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ unitSphereArea_pos.le
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      (((continuous_pow 2).fun_mul (continuous_sphericalMean_radius hf)).intervalIntegrable a b)
      ((continuous_const.fun_mul
        (continuous_id.fun_mul (continuous_sphericalMean_radius hg))).intervalIntegrable a b)
    intro r hr
    have hr0 : 0 ≤ r := ha.trans hr.1
    have hn := unitSphereAverage_nonneg hfn r
    have hm := unitSphereAverage_mono hf.continuous hg.continuous hfg r
    have hprod := mul_le_mul_of_nonneg_left hm (sq_nonneg r)
    have hpos := mul_nonneg hr0 (hn.trans hm)
    dsimp only [id_eq]
    nlinarith only [hprod, mul_nonneg (sub_nonneg.mpr hr.2) hpos]
  · intro r hr hbound
    unfold unitSphereAverage
    have hz : (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
        f (0 + r • (ω : ℝ^3))) = fun _ ↦ 0 := by
      funext ω
      apply hs
      have hω : ‖(ω : ℝ^3)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
      simpa only [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω, mul_one] using hbound
    rw [hz, integral_zero, zero_div]

/-- The free-wave shell supplies a lower bound for the inner
characteristic integral of the nonlinear source. -/
theorem semilinear_shell_radius_integral_lower_bound {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p s : ℝ}
    (hu : ContDiff ℝ 2 u) (hh : ContDiff ℝ 2 h) (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0)
    (hhn : ∀ y, 0 ≤ h y) (hR : 0 < R) (hp : 2 < p) (hH : 0 < ∫ y : ℝ^3, h y)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hs : 2 * R ≤ s) :
    shellSourceCoefficient R (∫ y : ℝ^3, h y) p / (2 * unitSphereArea 3) * s ^ (1 - p) ≤ ∫ r in (s -
      2 * R)..(s + 2 * R), r * unitSphereAverage 3 (fun x ↦ |u (timeSpaceCons s x)| ^ p) 0 r := by
  let w := kirchhoffPotential h
  let f := fun x : ℝ^3 ↦ |w (timeSpaceCons s x)| ^ p
  let g := fun x : ℝ^3 ↦ |u (timeSpaceCons s x)| ^ p
  have hspos : 0 < s := by linarith
  have hf : ContDiff ℝ 2 f := (contDiff_two_abs_rpow hp.le).comp
      ((contDiff_kirchhoffPotential hh).comp (contDiff_timeSpaceCons_spatial 3 s))
  have hg : ContDiff ℝ 2 g :=
    (contDiff_two_abs_rpow hp.le).comp (hu.comp (contDiff_timeSpaceCons_spatial 3 s))
  have hcompact : HasCompactSupport f :=
    ((kirchhoffPotential_hasForwardSupport hhs).hasCompactSupport_slice hspos.le).comp_left
      (g := fun z : ℝ ↦ |z| ^ p) (by simp [Real.zero_rpow (by linarith : p ≠ 0)])
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcompact
  have hfg (x : ℝ^3) : f x ≤ g x := by
    have hn := kirchhoffPotential_nonneg hhn hspos.le x
    have hm := kirchhoffPotential_le_semilinear hu hh hp hwave hzero hinitial hspos.le x
    dsimp [f, g, w]
    rw [abs_of_nonneg hn, abs_of_nonneg (hn.trans hm)]
    exact Real.rpow_le_rpow hn hm (by linarith)
  have hbound := integral_le_radius_sphericalMean_integral
    (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hfi
    (fun x ↦ Real.rpow_nonneg (abs_nonneg _) _) hfg
    (by linarith : 0 ≤ s - 2 * R) (by linarith : s - 2 * R ≤ s + 2 * R) ?_
  · have hlow := kirchhoff_power_integral_lower_bound (p := p) hh hhs hR
      (by linarith) hH (by linarith : R ≤ s)
    let I := ∫ r in (s - 2 * R)..(s + 2 * R), r * unitSphereAverage 3 g 0 r
    have hI : 0 ≤ I := by
      refine intervalIntegral.integral_nonneg (by linarith) fun r hr ↦ ?_
      exact mul_nonneg (by linarith [hr.1])
        (unitSphereAverage_nonneg (fun x ↦ Real.rpow_nonneg (abs_nonneg _) _) r)
    have hA : 0 < unitSphereArea 3 := unitSphereArea_pos
    have hlarge : shellSourceCoefficient R (∫ y : ℝ^3, h y) p * s ^ (2 - p) ≤
        2 * unitSphereArea 3 * s * I := by
      change (∫ x : ℝ^3, f x) ≤ unitSphereArea 3 * (s + 2 * R) * I at hbound
      change _ ≤ ∫ x : ℝ^3, f x at hlow
      nlinarith only [hbound, hlow,
        mul_nonneg (by linarith only [hs] : 0 ≤ s - 2 * R) (mul_nonneg hA.le hI)]
    have he : s ^ (2 - p) = s * s ^ (1 - p) := by
      cas using hspos
    rw [he] at hlarge
    change _ ≤ I
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * unitSphereArea 3)).mpr
    nlinarith only [hlarge, hspos]
  · intro x hx
    have hz := kirchhoffPotential_eq_zero_of_shell hhs hspos.le x
      (hx.imp (fun h ↦ by linarith) (fun h ↦ by linarith))
    simp only [f, w, hz, abs_zero, Real.zero_rpow (by linarith : p ≠ 0)]

end WaveEquation.SmallData
