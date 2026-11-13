/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Rectangle.Tonelli
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarRectangleIntegrals
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Kernels against singular weights near the origin and in the far field

Chen and Hou II, Sections 4.4.1 and 4.4.2, bound the integrals of a kernel `k` against the
reciprocal of a weight `φ` on the corner square `[0, r]²` and beyond `max(y₁, y₂) ≥ R` through a
lower bound `φ(y) ≥ q |y|^a (y₁/|y|)^b` and polar coordinates `y = ρ (cos β, sin β)` on the open
quadrant. The kernels are `k₁ = y₁ y₂ / |y|⁴`, the kernel of `u_x(0)` up to the factor `1/π`,
and `k₀₀ = y₁ y₂ (y₁² - y₂²) / |y|⁸`.

## Main results

* `lintegral_le_polar`: `∫⁻ G ≤ ∫⁻_{ρ > 0} ∫⁻_{0 < β < π/2} ρ G(ρ cos β, ρ sin β)` for `G`
  vanishing off the open quadrant.
* `lintegral_cos_rpow_le`: `∫₀^{π/2} cos^c β dβ ≤ (π/2)^{1-c}` for `0 ≤ c ≤ 1`, by Hölder's
  inequality.
* `lintegral_square_strainKernel_div_le`: for `a < 0`, `b ≤ 1`,
  `∫⁻_{(0,r]²} |y₁ y₂|/|y|⁴ / φ ≤ (√2 r)^{-a} / (q (-a)(2 - b))`, Sec. 4.4.1.
* `lintegral_square_quarticKernel_div_le`: for `a < -2`, `b ≤ 0`,
  `∫⁻_{(0,r]²} |y₁ y₂ (y₁² - y₂²)|/|y|⁸ / φ ≤ (√2 r)^{-a-2} / (4 q (-2 - a))`, Sec. 4.4.1.
* `lintegral_far_div_le`: if `|k(y)| ≤ |y|^{-p}` on the quadrant, `-1 ≤ b ≤ 0` and `p + a > 2`,
  then `∫⁻_{max(y₁,y₂) ≥ R} |k| / φ ≤ R^{2-p-a} (π/2)^{1+b} / (q (p + a - 2))`, Sec. 4.4.2.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Sections 4.4.1 and
  4.4.2.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE.Analysis
open scoped ENNReal

namespace PotentialTheory.Planar

/-! ### Polar coordinates on the quadrant -/

/-- For `ρ ≥ 0` the point `(ρ cos θ, ρ sin θ)` has norm `ρ`. -/
private theorem norm_polar {ρ θ : ℝ} (hρ : 0 ≤ ρ) :
    ‖(!₂[ρ * Real.cos θ, ρ * Real.sin θ] : ℝ^2)‖ = ρ := by
  have h := norm_sq_vec (ρ * Real.cos θ) (ρ * Real.sin θ)
  have h2 : (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h2] at h
  exact (sq_eq_sq₀ (norm_nonneg _) hρ).1 h

/-- **Polar coordinates on the open quadrant**, as an upper bound for every `G ≥ 0` vanishing off
the quadrant: `∫⁻ G ≤ ∫⁻_{ρ > 0} ∫⁻_{0 < β < π/2} ρ G(ρ cos β, ρ sin β)`. -/
theorem lintegral_le_polar {G : ℝ^2 → ℝ≥0∞} (h0 : ∀ y : ℝ^2, ¬ (0 < y 0 ∧ 0 < y 1) → G y = 0) :
    ∫⁻ y, G y ≤ ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo 0 (Real.pi / 2),
      ENNReal.ofReal ρ * G !₂[ρ * Real.cos θ, ρ * Real.sin θ] := by
  have h1 : ∫⁻ y, G y = ∫⁻ p : ℝ × ℝ, G (planeEquiv.symm p) := by
    have := measurePreserving_planeEquiv.lintegral_comp_emb planeEquiv.measurableEmbedding
      (fun p ↦ G (planeEquiv.symm p))
    simpa only [MeasurableEquiv.symm_apply_apply] using this
  rw [h1, ← lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans (le_of_eq (setLIntegral_congr_fun measurableSet_Ioi
    fun ρ hρ ↦ ?_))
  simp only [polarCoord_symm_apply, planeEquiv_symm_apply, smul_eq_mul]
  have hρ : 0 < ρ := hρ
  -- the angles outside `(0, π/2)` give points off the quadrant
  have hzero : ∀ θ ∈ Ioo (-Real.pi) Real.pi, θ ∉ Ioo 0 (Real.pi / 2) →
      ENNReal.ofReal ρ * G !₂[ρ * Real.cos θ, ρ * Real.sin θ] = 0 := by
    intro θ hθ hθ'
    rw [h0 _ ?_, mul_zero]
    rintro ⟨hc, hs⟩
    have hc' : 0 < Real.cos θ := by simpa [mul_pos_iff_of_pos_left hρ] using hc
    have hs' : 0 < Real.sin θ := by simpa [mul_pos_iff_of_pos_left hρ] using hs
    exact hθ' ⟨lt_of_not_ge fun h ↦ hs'.not_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le h hθ.1.le),
      lt_of_not_ge fun h ↦ hc'.not_ge
        (Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [hθ.2]))⟩
  have hsub : Ioo 0 (Real.pi / 2) ⊆ Ioo (-Real.pi) Real.pi :=
    Ioo_subset_Ioo (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [show Ioo 0 (Real.pi / 2) = Ioo 0 (Real.pi / 2) ∩ Ioo (-Real.pi) Real.pi from
    (inter_eq_left.2 hsub).symm, ← setLIntegral_indicator (measurableSet_Ioo (a := (0 : ℝ)))]
  refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  by_cases h : θ ∈ Ioo 0 (Real.pi / 2)
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, hzero θ hθ h]

/-! ### One-dimensional integrals -/

/-- `∫⁻_{(0, R]} ρ^s dρ = R^{s+1}/(s+1)` for `s > -1`. -/
theorem lintegral_Ioc_rpow {s R : ℝ} (hs : -1 < s) (hR : 0 ≤ R) :
    ∫⁻ ρ in Ioc 0 R, ENNReal.ofReal (ρ ^ s) = ENNReal.ofReal (R ^ (s + 1) / (s + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hR, integral_rpow (Or.inl hs),
      Real.zero_rpow (by linarith), sub_zero]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1
      (intervalIntegral.intervalIntegrable_rpow' hs)
  · exact (ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun ρ hρ ↦ Real.rpow_nonneg hρ.1.le _)

/-- `∫⁻_{(R, ∞)} ρ^s dρ = -R^{s+1}/(s+1)` for `s < -1` and `R > 0`. -/
theorem lintegral_Ioi_rpow {s R : ℝ} (hs : s < -1) (hR : 0 < R) :
    ∫⁻ ρ in Ioi R, ENNReal.ofReal (ρ ^ s) = ENNReal.ofReal (-R ^ (s + 1) / (s + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hs hR),
    integral_Ioi_rpow_of_lt hs hR]
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun ρ hρ ↦ Real.rpow_nonneg (hR.trans hρ).le _)

/-- For `c ≥ 0` the function `θ ↦ cos^c θ` is continuous on `[0, π/2]`. -/
private theorem continuousOn_cos_rpow {c : ℝ} (hc : 0 ≤ c) :
    ContinuousOn (fun θ ↦ Real.cos θ ^ c) (Icc 0 (Real.pi / 2)) :=
  fun _ _ ↦ (Real.continuousAt_rpow_const _ _ (Or.inr hc)).comp
    Real.continuous_cos.continuousAt |>.continuousWithinAt

/-- `∫₀^{π/2} sin β cos^{1-b} β dβ = 1/(2 - b)` for `b ≤ 1`. -/
theorem lintegral_sin_mul_cos_rpow {b : ℝ} (hb : b ≤ 1) :
    ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal (Real.sin θ * Real.cos θ ^ (1 - b)) =
      ENNReal.ofReal (1 / (2 - b)) := by
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have h2b : 0 < 2 - b := by linarith
  have hcont : ContinuousOn (fun θ ↦ Real.sin θ * Real.cos θ ^ (1 - b)) (Icc 0 (Real.pi / 2)) :=
    Real.continuous_sin.continuousOn.mul (continuousOn_cos_rpow (by linarith))
  have hint : IntegrableOn (fun θ ↦ Real.sin θ * Real.cos θ ^ (1 - b)) (Ioo 0 (Real.pi / 2)) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi]
    have hd : ∀ θ ∈ Ioo 0 (Real.pi / 2), HasDerivAt (fun θ ↦ -(Real.cos θ ^ (2 - b) / (2 - b)))
        (Real.sin θ * Real.cos θ ^ (1 - b)) θ := by
      intro θ hθ
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have h := ((Real.hasDerivAt_cos θ).rpow_const (p := 2 - b) (Or.inl hc.ne')).div_const
        (2 - b) |>.neg
      refine h.congr_deriv ?_
      rw [show 2 - b - 1 = 1 - b by ring]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpi
      ((continuousOn_cos_rpow h2b.le).div_const _ |>.neg) hd
      (hcont.intervalIntegrable_of_Icc hpi)]
    simp [Real.cos_pi_div_two, Real.zero_rpow h2b.ne']
  · exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun θ hθ ↦
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos]))
        (Real.rpow_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
          hθ.2.le⟩) _))

/-- `|cos β sin β (cos² β - sin² β)| = |sin 4β| / 4`. -/
private theorem abs_quartic_trig (θ : ℝ) :
    |Real.cos θ * Real.sin θ * (Real.cos θ ^ 2 - Real.sin θ ^ 2)| = |Real.sin (4 * θ)| / 4 := by
  have h : Real.sin (4 * θ) =
      4 * (Real.cos θ * Real.sin θ * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul,
      Real.cos_sq']
    ring
  rw [h, abs_mul (4 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  ring

/-- `∫₀^{π/2} |sin 4β| dβ = 1`. -/
private theorem lintegral_abs_sin_four :
    ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal |Real.sin (4 * θ)| = 1 := by
  have hpi := Real.pi_pos
  have hcont : Continuous fun θ : ℝ ↦ |Real.sin (4 * θ)| := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (Eventually.of_forall fun _ ↦ abs_nonneg _), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi / 4)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hd : ∀ θ, HasDerivAt (fun θ ↦ -Real.cos (4 * θ) / 4) (Real.sin (4 * θ)) θ := fun θ ↦
    (((hasDerivAt_id' θ).const_mul 4).cos.neg.div_const 4).congr_deriv (by ring)
  have h1 : ∫ θ in (0 : ℝ)..Real.pi / 4, |Real.sin (4 * θ)| = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun θ ↦ Real.sin (4 * θ)) fun θ hθ ↦ ?_]
    · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hd θ)
        ((by fun_prop : Continuous fun θ : ℝ ↦ Real.sin (4 * θ)).intervalIntegrable _ _)]
      rw [show 4 * (Real.pi / 4) = Real.pi by ring]; simp; norm_num
    · rw [uIcc_of_le (by positivity)] at hθ
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2]))
  have h2 : ∫ θ in Real.pi / 4..Real.pi / 2, |Real.sin (4 * θ)| = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun θ ↦ -Real.sin (4 * θ)) fun θ hθ ↦ ?_]
    · rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ ↦ hd θ)
        ((by fun_prop : Continuous fun θ : ℝ ↦ Real.sin (4 * θ)).intervalIntegrable _ _)]
      rw [show 4 * (Real.pi / 2) = 2 * Real.pi by ring, show 4 * (Real.pi / 4) = Real.pi by ring]
      simp; norm_num
    · rw [uIcc_of_le (by linarith)] at hθ
      refine abs_of_nonpos ?_
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := 4 * θ - 2 * Real.pi) (by linarith [hθ.2])
        (by linarith [hθ.1])
      rwa [Real.sin_sub_two_pi] at this
  rw [h1, h2]; norm_num

/-- **Hölder for the angular factor**: `∫₀^{π/2} cos^c β dβ ≤ (π/2)^{1-c}` for `0 ≤ c ≤ 1`. -/
theorem lintegral_cos_rpow_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal (Real.cos θ ^ c) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ (1 - c)) := by
  have hpi := Real.pi_pos
  have hs : 0 < 2 / Real.pi := by positivity
  -- weighted AM-GM: `cos^c = (2/π)^c ((π/2) cos)^c ≤ (2/π)^c (c (π/2) cos + 1 - c)`
  have hpt : ∀ θ ∈ Ioo 0 (Real.pi / 2), ENNReal.ofReal (Real.cos θ ^ c) ≤
      ENNReal.ofReal ((2 / Real.pi) ^ c * (c * (Real.pi / 2) * Real.cos θ + (1 - c))) := by
    intro θ hθ
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], hθ.2.le⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have h := Real.geom_mean_le_arith_mean2_weighted hc0 (by linarith : 0 ≤ 1 - c)
      (by positivity : 0 ≤ Real.pi / 2 * Real.cos θ) zero_le_one (by ring)
    rw [Real.one_rpow, mul_one] at h
    have e : Real.cos θ ^ c = (2 / Real.pi) ^ c * (Real.pi / 2 * Real.cos θ) ^ c := by
      rw [← Real.mul_rpow hs.le (by positivity), ← mul_assoc,
        div_mul_div_cancel₀ (by positivity : (Real.pi : ℝ) ≠ 0), div_self two_ne_zero, one_mul]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs.le _)
    linarith
  have hcont : Continuous fun θ : ℝ ↦
      (2 / Real.pi) ^ c * (c * (Real.pi / 2) * Real.cos θ + (1 - c)) := by fun_prop
  calc ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal (Real.cos θ ^ c)
      ≤ ∫⁻ θ in Ioo 0 (Real.pi / 2),
          ENNReal.ofReal ((2 / Real.pi) ^ c * (c * (Real.pi / 2) * Real.cos θ + (1 - c))) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal ((Real.pi / 2) ^ (1 - c)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set
            Ioo_subset_Icc_self) ((ae_restrict_iff' measurableSet_Ioo).2
            (Eventually.of_forall fun θ hθ ↦ by
              have : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2.le⟩
              have : 0 ≤ 1 - c := by linarith
              positivity)),
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (f := fun x ↦ c * (Real.pi / 2) * Real.cos x)
            (g := fun _ ↦ 1 - c)
            ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
            intervalIntegrable_const,
          intervalIntegral.integral_const_mul, integral_cos, intervalIntegral.integral_const]
        congr 1
        simp only [Real.sin_pi_div_two, Real.sin_zero, sub_zero, smul_eq_mul, mul_one]
        rw [show (1 : ℝ) - c = 1 + -c by ring, Real.rpow_add (by positivity), Real.rpow_one,
          Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
        ring

/-! ### The corner square -/

/-- For `ρ > 0` and `0 < θ < π/2`, `cos θ`, `sin θ` and both coordinates of `(ρ cos θ, ρ sin θ)` are
positive. -/
private theorem polar_coords {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    0 < Real.cos θ ∧ 0 < Real.sin θ ∧ 0 < ρ * Real.cos θ ∧ 0 < ρ * Real.sin θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  exact ⟨hc, hs, mul_pos hρ hc, mul_pos hρ hs⟩

/-- The square `(0, r]²` of the open quadrant is measurable. -/
private theorem measurableSet_quadrantSquare (r : ℝ) :
    MeasurableSet {y : ℝ^2 | 0 < y 0 ∧ y 0 ≤ r ∧ 0 < y 1 ∧ y 1 ≤ r} := by
  have h0 : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable
  have h1 : Measurable fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.measurable
  exact (measurableSet_lt measurable_const h0).inter ((measurableSet_le h0 measurable_const).inter
    ((measurableSet_lt measurable_const h1).inter (measurableSet_le h1 measurable_const)))

/-- Every point of the square `(0, r]²` has norm at most `√2 r`. -/
private theorem norm_le_of_mem_square {r : ℝ} {y : ℝ^2}
    (hy : 0 < y 0 ∧ y 0 ≤ r ∧ 0 < y 1 ∧ y 1 ≤ r) : ‖y‖ ≤ √2 * r := by
  have hr : 0 ≤ r := hy.1.le.trans hy.2.1
  rw [← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_sq hr, ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [EuclideanSpace.norm_sq_fin_two]
  nlinarith [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

/-- The polar slice at radius `ρ > 0` of the majorant `1_{y ∈ quadrant, ‖y‖ ∈ I} g` is a radial
indicator times an angular integral, once `ρ g(ρ cos θ, ρ sin θ) = h ρ · k θ` for `ρ ∈ I`. -/
private theorem lintegral_polar_indicator {I : Set ℝ} {g : ℝ^2 → ℝ} {h k : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hk : Measurable fun θ ↦ ENNReal.ofReal (k θ)) (hh : 0 ≤ h ρ)
    (heq : ρ ∈ I → ∀ θ ∈ Ioo 0 (Real.pi / 2),
      ρ * g !₂[ρ * Real.cos θ, ρ * Real.sin θ] = h ρ * k θ) :
    ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal ρ *
        {y : ℝ^2 | (0 < y 0 ∧ 0 < y 1) ∧ ‖y‖ ∈ I}.indicator (fun y ↦ ENNReal.ofReal (g y))
          !₂[ρ * Real.cos θ, ρ * Real.sin θ] =
      I.indicator (fun ρ ↦ ENNReal.ofReal (h ρ)) ρ *
        ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal (k θ) := by
  rw [← lintegral_const_mul _ hk]
  refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  obtain ⟨-, -, hx, hy⟩ := polar_coords hρ hθ
  have hn := norm_polar (θ := θ) hρ.le
  by_cases hρI : ρ ∈ I
  · rw [Set.indicator_of_mem (show _ ∈ {y : ℝ^2 | (0 < y 0 ∧ 0 < y 1) ∧ ‖y‖ ∈ I} from
        ⟨⟨hx, hy⟩, by rwa [hn]⟩), Set.indicator_of_mem hρI, ← ENNReal.ofReal_mul hρ.le,
      ← ENNReal.ofReal_mul hh, heq hρI θ hθ]
  · rw [Set.indicator_of_notMem (show _ ∉ {y : ℝ^2 | (0 < y 0 ∧ 0 < y 1) ∧ ‖y‖ ∈ I} from
        fun h ↦ hρI (by simpa only [hn] using h.2)), Set.indicator_of_notMem hρI, mul_zero,
      zero_mul]

/-- **The kernel of `u_x(0)` on the corner square**, Chen and Hou II, Sec. 4.4.1: if
`φ(y) ≥ q |y|^a (y₁/|y|)^b > 0` on the open quadrant with `q > 0`, `a < 0` and `b ≤ 1`, then
`∫⁻_{(0,r]²} |y₁ y₂|/|y|⁴ / φ ≤ (√2 r)^{-a} / (q (-a)(2 - b))`. -/
theorem lintegral_square_strainKernel_div_le {φ : ℝ^2 → ℝ} {q a b r : ℝ} (hq : 0 < q)
    (ha : a < 0) (hb : b ≤ 1) (hr : 0 ≤ r)
    (hφ : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b ≤ φ y) :
    ∫⁻ y in {y : ℝ^2 | 0 < y 0 ∧ y 0 ≤ r ∧ 0 < y 1 ∧ y 1 ≤ r},
        ENNReal.ofReal (|y 0 * y 1| / ‖y‖ ^ 4 / φ y) ≤
      ENNReal.ofReal ((√2 * r) ^ (-a) / (q * (-a) * (2 - b))) := by
  set S := {y : ℝ^2 | 0 < y 0 ∧ y 0 ≤ r ∧ 0 < y 1 ∧ y 1 ≤ r} with hS
  set D := {y : ℝ^2 | (0 < y 0 ∧ 0 < y 1) ∧ ‖y‖ ∈ Ioc 0 (√2 * r)} with hD
  set G : ℝ^2 → ℝ≥0∞ := D.indicator fun y ↦
    ENNReal.ofReal (q⁻¹ * ‖y‖ ^ (-a) * (y 0 * y 1 / ‖y‖ ^ 4) * (y 0 / ‖y‖) ^ (-b)) with hG
  -- the integrand is below `G`
  have hpt (y : ℝ^2) :
      S.indicator (fun y ↦ ENNReal.ofReal (|y 0 * y 1| / ‖y‖ ^ 4 / φ y)) y ≤ G y := by
    refine Set.indicator_apply_le' (fun hy ↦ ?_) fun _ ↦ bot_le
    have hn : 0 < ‖y‖ := norm_pos_iff.2 fun h ↦ by have := hy.1; simp [h] at this
    rw [hG, Set.indicator_of_mem (show y ∈ D from ⟨⟨hy.1, hy.2.2.1⟩, hn, norm_le_of_mem_square hy⟩)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 < q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b := by have := hy.1; positivity
    rw [abs_of_pos (mul_pos hy.1 hy.2.2.1)]
    calc y 0 * y 1 / ‖y‖ ^ 4 / φ y ≤ y 0 * y 1 / ‖y‖ ^ 4 / (q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b) :=
          div_le_div_of_nonneg_left (by have := hy.1; have := hy.2.2.1; positivity) hw
            (hφ y hy.1 hy.2.2.1)
      _ = _ := by
          rw [Real.rpow_neg hn.le, Real.rpow_neg (by have := hy.1; positivity)]
          field_simp
  have hG0 : ∀ y : ℝ^2, ¬ (0 < y 0 ∧ 0 < y 1) → G y = 0 := fun y hy ↦
    Set.indicator_of_notMem (fun h ↦ hy h.1) _
  -- in polar coordinates
  have hpolar (ρ : ℝ) (hρ : ρ ∈ Ioi (0 : ℝ)) := lintegral_polar_indicator (I := Ioc 0 (√2 * r))
    (g := fun y ↦ q⁻¹ * ‖y‖ ^ (-a) * (y 0 * y 1 / ‖y‖ ^ 4) * (y 0 / ‖y‖) ^ (-b))
    (h := fun ρ ↦ q⁻¹ * ρ ^ (-a - 1)) (k := fun θ ↦ Real.sin θ * Real.cos θ ^ (1 - b)) hρ
    (ENNReal.measurable_ofReal.comp (Real.measurable_sin.mul (Real.measurable_cos.pow_const _)))
    (by have : (0 : ℝ) < ρ := hρ; positivity) fun _ θ hθ ↦ by
      obtain ⟨hc, -, -, -⟩ := polar_coords hρ hθ
      have e0 : (!₂[ρ * Real.cos θ, ρ * Real.sin θ] : ℝ^2) 0 = ρ * Real.cos θ := rfl
      have e1 : (!₂[ρ * Real.cos θ, ρ * Real.sin θ] : ℝ^2) 1 = ρ * Real.sin θ := rfl
      rw [e0, e1, norm_polar (le_of_lt hρ), mul_div_cancel_left₀ _ (ne_of_gt hρ),
        Real.rpow_sub hρ, Real.rpow_one, Real.rpow_sub hc, Real.rpow_one, Real.rpow_neg hc.le]
      field_simp
  have hsr : 0 ≤ √2 * r := by positivity
  calc ∫⁻ y in S, ENNReal.ofReal (|y 0 * y 1| / ‖y‖ ^ 4 / φ y)
      = ∫⁻ y, S.indicator (fun y ↦ ENNReal.ofReal (|y 0 * y 1| / ‖y‖ ^ 4 / φ y)) y :=
        (lintegral_indicator (measurableSet_quadrantSquare r) _).symm
    _ ≤ ∫⁻ y, G y := lintegral_mono hpt
    _ ≤ _ := lintegral_le_polar hG0
    _ = ∫⁻ ρ in Ioi (0 : ℝ), (Ioc 0 (√2 * r)).indicator
          (fun ρ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 1))) ρ * ENNReal.ofReal (1 / (2 - b)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ ?_
        rw [hpolar ρ hρ, lintegral_sin_mul_cos_rpow hb]
    _ = (∫⁻ ρ in Ioc 0 (√2 * r), ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 1))) *
          ENNReal.ofReal (1 / (2 - b)) := by
        have hmA : Measurable ((Ioc 0 (√2 * r)).indicator
            (fun ρ : ℝ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 1)))) :=
          (ENNReal.measurable_ofReal.comp (measurable_const.mul
            (measurable_id.pow_const _))).indicator measurableSet_Ioc
        rw [lintegral_mul_const _ hmA, setLIntegral_indicator measurableSet_Ioc,
          inter_eq_left.2 Ioc_subset_Ioi_self]
    _ = ENNReal.ofReal ((√2 * r) ^ (-a) / (q * (-a) * (2 - b))) := by
        have h1 : ∫⁻ ρ in Ioc 0 (√2 * r), ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 1)) =
            ENNReal.ofReal q⁻¹ * ENNReal.ofReal ((√2 * r) ^ (-a - 1 + 1) / (-a - 1 + 1)) := by
          have hmR : Measurable fun ρ : ℝ ↦ ENNReal.ofReal (ρ ^ (-a - 1)) :=
            ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
          rw [← lintegral_Ioc_rpow (by linarith) hsr, ← lintegral_const_mul _ hmR]
          refine setLIntegral_congr_fun measurableSet_Ioc fun ρ hρ ↦ ?_
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hq.le)]
        rw [h1, ← ENNReal.ofReal_mul (inv_nonneg.2 hq.le),
          ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hq.le)
            (div_nonneg (Real.rpow_nonneg hsr _) (by linarith)))]
        congr 1
        rw [show -a - 1 + 1 = -a by ring]
        have h2b : 2 - b ≠ 0 := by linarith
        have ha' : -a ≠ 0 := by linarith
        field_simp

/-- **The kernel of `K₀₀` on the corner square**, Chen and Hou II, Sec. 4.4.1: if
`φ(y) ≥ q |y|^a (y₁/|y|)^b > 0` on the open quadrant with `q > 0`, `a < -2` and `b ≤ 0`, then
`∫⁻_{(0,r]²} |y₁ y₂ (y₁² - y₂²)|/|y|⁸ / φ ≤ (√2 r)^{-a-2} / (4 q (-2 - a))`. -/
theorem lintegral_square_quarticKernel_div_le {φ : ℝ^2 → ℝ} {q a b r : ℝ} (hq : 0 < q)
    (ha : a < -2) (hb : b ≤ 0) (hr : 0 ≤ r)
    (hφ : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b ≤ φ y) :
    ∫⁻ y in {y : ℝ^2 | 0 < y 0 ∧ y 0 ≤ r ∧ 0 < y 1 ∧ y 1 ≤ r},
        ENNReal.ofReal (|y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / φ y) ≤
      ENNReal.ofReal ((√2 * r) ^ (-a - 2) / (4 * q * (-2 - a))) := by
  set S := {y : ℝ^2 | 0 < y 0 ∧ y 0 ≤ r ∧ 0 < y 1 ∧ y 1 ≤ r} with hS
  set D := {y : ℝ^2 | (0 < y 0 ∧ 0 < y 1) ∧ ‖y‖ ∈ Ioc 0 (√2 * r)} with hD
  set G : ℝ^2 → ℝ≥0∞ := D.indicator fun y ↦
    ENNReal.ofReal (q⁻¹ * ‖y‖ ^ (-a) * (|y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8)) with hG
  have hpt (y : ℝ^2) : S.indicator
      (fun y ↦ ENNReal.ofReal (|y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / φ y)) y ≤ G y := by
    refine Set.indicator_apply_le' (fun hy ↦ ?_) fun _ ↦ bot_le
    have hy0 := hy.1
    have hn : 0 < ‖y‖ := norm_pos_iff.2 fun h ↦ by simp [h] at hy0
    rw [hG, Set.indicator_of_mem (show y ∈ D from ⟨⟨hy0, hy.2.2.1⟩, hn, norm_le_of_mem_square hy⟩)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hy1 := hy.2.2.1
    have hk : 0 ≤ |y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 := by positivity
    have hpow : (y 0 / ‖y‖) ^ b ≥ 1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
      ((div_le_one hn).2 ((le_abs_self _).trans (by simpa using PiLp.norm_apply_le y 0))) hb
    calc |y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / φ y
        ≤ |y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / (q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b) :=
          div_le_div_of_nonneg_left hk (by positivity) (hφ y hy0 hy1)
      _ ≤ |y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / (q * ‖y‖ ^ a) :=
          div_le_div_of_nonneg_left hk (by positivity)
            (le_mul_of_one_le_right (by positivity) hpow)
      _ = _ := by rw [Real.rpow_neg hn.le]; field_simp
  have hG0 : ∀ y : ℝ^2, ¬ (0 < y 0 ∧ 0 < y 1) → G y = 0 := fun y hy ↦
    Set.indicator_of_notMem (fun h ↦ hy h.1) _
  have hpolar (ρ : ℝ) (hρ : ρ ∈ Ioi (0 : ℝ)) := lintegral_polar_indicator (I := Ioc 0 (√2 * r))
    (g := fun y ↦ q⁻¹ * ‖y‖ ^ (-a) * (|y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8))
    (h := fun ρ ↦ q⁻¹ * ρ ^ (-a - 3)) (k := fun θ ↦ |Real.sin (4 * θ)| / 4) hρ
    (ENNReal.measurable_ofReal.comp
      ((by fun_prop : Continuous fun θ : ℝ ↦ |Real.sin (4 * θ)| / 4).measurable))
    (by have : (0 : ℝ) < ρ := hρ; positivity) fun _ θ hθ ↦ by
      have hρ : (0 : ℝ) < ρ := hρ
      have e0 : (!₂[ρ * Real.cos θ, ρ * Real.sin θ] : ℝ^2) 0 = ρ * Real.cos θ := rfl
      have e1 : (!₂[ρ * Real.cos θ, ρ * Real.sin θ] : ℝ^2) 1 = ρ * Real.sin θ := rfl
      have hq4 : (ρ * Real.cos θ) * (ρ * Real.sin θ) * ((ρ * Real.cos θ) ^ 2 - (ρ * Real.sin θ) ^ 2)
          = ρ ^ 4 * (Real.cos θ * Real.sin θ * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) := by ring
      rw [e0, e1, norm_polar hρ.le, hq4, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ρ ^ 4),
        abs_quartic_trig, show -a - 3 = -a - 4 + 1 by ring, Real.rpow_add hρ, Real.rpow_one,
        Real.rpow_sub hρ, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
  have hθ : ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal (|Real.sin (4 * θ)| / 4) =
      ENNReal.ofReal (1 / 4) := by
    have e : ∀ θ : ℝ, ENNReal.ofReal (|Real.sin (4 * θ)| / 4) =
        ENNReal.ofReal |Real.sin (4 * θ)| * ENNReal.ofReal (1 / 4) := fun θ ↦ by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]; ring_nf
    simp_rw [e]
    have hmS : Measurable fun θ : ℝ ↦ ENNReal.ofReal |Real.sin (4 * θ)| :=
      ENNReal.measurable_ofReal.comp
        ((by fun_prop : Continuous fun θ : ℝ ↦ |Real.sin (4 * θ)|).measurable)
    rw [lintegral_mul_const _ hmS, lintegral_abs_sin_four, one_mul]
  have hsr : 0 ≤ √2 * r := by positivity
  calc ∫⁻ y in S, ENNReal.ofReal (|y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / φ y)
      = ∫⁻ y, S.indicator
          (fun y ↦ ENNReal.ofReal (|y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2)| / ‖y‖ ^ 8 / φ y)) y :=
        (lintegral_indicator (measurableSet_quadrantSquare r) _).symm
    _ ≤ ∫⁻ y, G y := lintegral_mono hpt
    _ ≤ _ := lintegral_le_polar hG0
    _ = ∫⁻ ρ in Ioi (0 : ℝ), (Ioc 0 (√2 * r)).indicator
          (fun ρ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 3))) ρ * ENNReal.ofReal (1 / 4) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ ?_
        rw [hpolar ρ hρ, hθ]
    _ = (∫⁻ ρ in Ioc 0 (√2 * r), ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 3))) * ENNReal.ofReal (1 / 4) := by
        have hmA : Measurable ((Ioc 0 (√2 * r)).indicator
            (fun ρ : ℝ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 3)))) :=
          (ENNReal.measurable_ofReal.comp (measurable_const.mul
            (measurable_id.pow_const _))).indicator measurableSet_Ioc
        rw [lintegral_mul_const _ hmA, setLIntegral_indicator measurableSet_Ioc,
          inter_eq_left.2 Ioc_subset_Ioi_self]
    _ = ENNReal.ofReal ((√2 * r) ^ (-a - 2) / (4 * q * (-2 - a))) := by
        have hmR : Measurable fun ρ : ℝ ↦ ENNReal.ofReal (ρ ^ (-a - 3)) :=
          ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
        have h1 : ∫⁻ ρ in Ioc 0 (√2 * r), ENNReal.ofReal (q⁻¹ * ρ ^ (-a - 3)) =
            ENNReal.ofReal q⁻¹ * ENNReal.ofReal ((√2 * r) ^ (-a - 3 + 1) / (-a - 3 + 1)) := by
          rw [← lintegral_Ioc_rpow (by linarith) hsr, ← lintegral_const_mul _ hmR]
          refine setLIntegral_congr_fun measurableSet_Ioc fun ρ hρ ↦ ?_
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hq.le)]
        rw [h1, ← ENNReal.ofReal_mul (inv_nonneg.2 hq.le),
          ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hq.le)
            (div_nonneg (Real.rpow_nonneg hsr _) (by linarith)))]
        congr 1
        rw [show -a - 3 + 1 = -a - 2 by ring]
        have ha' : -2 - a ≠ 0 := by linarith
        have ha'' : -a - 2 ≠ 0 := by linarith
        field_simp
        ring

/-! ### The far field -/

/-- The far part `{y₁, y₂ > 0, max(y₁, y₂) ≥ R}` of the open quadrant is measurable. -/
private theorem measurableSet_quadrantFar (R : ℝ) :
    MeasurableSet {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1 ∧ R ≤ max (y 0) (y 1)} := by
  have h0 : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable
  have h1 : Measurable fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.measurable
  exact (measurableSet_lt measurable_const h0).inter ((measurableSet_lt measurable_const h1).inter
    (measurableSet_le measurable_const (h0.max h1)))

/-- **The far field**, Chen and Hou II, Sec. 4.4.2: if `|k(y)| ≤ |y|^{-p}` and
`φ(y) ≥ q |y|^a (y₁/|y|)^b > 0` on the open quadrant, with `q, R > 0`, `-1 ≤ b ≤ 0` and
`p + a > 2`, then `∫⁻_{max(y₁, y₂) ≥ R} |k| / φ ≤ R^{2-p-a} (π/2)^{1+b} / (q (p + a - 2))`. -/
theorem lintegral_far_div_le {k φ : ℝ^2 → ℝ} {q a b p R : ℝ} (hq : 0 < q) (hb0 : b ≤ 0)
    (hb1 : -1 ≤ b) (hpa : 2 < p + a) (hR : 0 < R)
    (hk : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → |k y| ≤ ‖y‖ ^ (-p))
    (hφ : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b ≤ φ y) :
    ∫⁻ y in {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1 ∧ R ≤ max (y 0) (y 1)},
        ENNReal.ofReal (|k y| / φ y) ≤
      ENNReal.ofReal (R ^ (2 - p - a) * (Real.pi / 2) ^ (1 + b) / (q * (p + a - 2))) := by
  set T := {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1 ∧ R ≤ max (y 0) (y 1)} with hT
  set D := {y : ℝ^2 | (0 < y 0 ∧ 0 < y 1) ∧ ‖y‖ ∈ Ici R} with hD
  set G : ℝ^2 → ℝ≥0∞ := D.indicator fun y ↦
    ENNReal.ofReal (q⁻¹ * ‖y‖ ^ (-p - a) * (y 0 / ‖y‖) ^ (-b)) with hG
  have hpt (y : ℝ^2) : T.indicator (fun y ↦ ENNReal.ofReal (|k y| / φ y)) y ≤ G y := by
    refine Set.indicator_apply_le' (fun hy ↦ ?_) fun _ ↦ bot_le
    obtain ⟨hy0, hy1, hyR⟩ := hy
    have hRn : R ≤ ‖y‖ := hyR.trans (max_le
      ((le_abs_self _).trans (by simpa using PiLp.norm_apply_le y 0))
      ((le_abs_self _).trans (by simpa using PiLp.norm_apply_le y 1)))
    rw [hG, Set.indicator_of_mem (show y ∈ D from ⟨⟨hy0, hy1⟩, hRn⟩)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn : 0 < ‖y‖ := hR.trans_le hRn
    have hw : 0 < q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b := by positivity
    calc |k y| / φ y ≤ |k y| / (q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hw (hφ y hy0 hy1)
      _ ≤ ‖y‖ ^ (-p) / (q * ‖y‖ ^ a * (y 0 / ‖y‖) ^ b) :=
          div_le_div_of_nonneg_right (hk y hy0 hy1) hw.le
      _ = _ := by
          rw [Real.rpow_sub hn, Real.rpow_neg hn.le, Real.rpow_neg (by positivity)]
          field_simp
  have hG0 : ∀ y : ℝ^2, ¬ (0 < y 0 ∧ 0 < y 1) → G y = 0 := fun y hy ↦
    Set.indicator_of_notMem (fun h ↦ hy h.1) _
  have hpolar (ρ : ℝ) (hρ : ρ ∈ Ioi (0 : ℝ)) := lintegral_polar_indicator (I := Ici R)
    (g := fun y ↦ q⁻¹ * ‖y‖ ^ (-p - a) * (y 0 / ‖y‖) ^ (-b))
    (h := fun ρ ↦ q⁻¹ * ρ ^ (1 - p - a)) (k := fun θ ↦ Real.cos θ ^ (-b)) hρ
    (ENNReal.measurable_ofReal.comp (Real.measurable_cos.pow_const _))
    (by have : (0 : ℝ) < ρ := hρ; positivity) fun _ θ hθ ↦ by
      have hρ : (0 : ℝ) < ρ := hρ
      have e0 : (!₂[ρ * Real.cos θ, ρ * Real.sin θ] : ℝ^2) 0 = ρ * Real.cos θ := rfl
      rw [e0, norm_polar hρ.le, mul_div_cancel_left₀ _ hρ.ne', show 1 - p - a = -p - a + 1 by ring,
        Real.rpow_add hρ, Real.rpow_one]
      ring
  have hθ := lintegral_cos_rpow_le (c := -b) (by linarith) (by linarith)
  rw [show 1 - -b = 1 + b by ring] at hθ
  have hmA : Measurable ((Ici R).indicator
      (fun ρ : ℝ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (1 - p - a)))) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_id.pow_const _))).indicator measurableSet_Ici
  have hmR : Measurable fun ρ : ℝ ↦ ENNReal.ofReal (ρ ^ (1 - p - a)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hrad : ∫⁻ ρ in Ioi (0 : ℝ), (Ici R).indicator
      (fun ρ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (1 - p - a))) ρ =
      ENNReal.ofReal (q⁻¹ * (R ^ (2 - p - a) / (p + a - 2))) := by
    rw [setLIntegral_indicator measurableSet_Ici, inter_eq_left.2 (Ici_subset_Ioi.2 hR),
      ← setLIntegral_congr Ioi_ae_eq_Ici]
    have h1 : ∫⁻ ρ in Ioi R, ENNReal.ofReal (q⁻¹ * ρ ^ (1 - p - a)) =
        ENNReal.ofReal q⁻¹ * ENNReal.ofReal (-R ^ (1 - p - a + 1) / (1 - p - a + 1)) := by
      rw [← lintegral_Ioi_rpow (by linarith) hR, ← lintegral_const_mul _ hmR]
      refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ ?_
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hq.le)]
    rw [h1, ← ENNReal.ofReal_mul (inv_nonneg.2 hq.le)]
    congr 2
    rw [show 1 - p - a + 1 = 2 - p - a by ring, show 2 - p - a = -(p + a - 2) by ring, div_neg,
      neg_div, neg_neg, show -(p + a - 2) = 2 - p - a by ring]
  have hrad0 : 0 ≤ q⁻¹ * (R ^ (2 - p - a) / (p + a - 2)) :=
    mul_nonneg (inv_nonneg.2 hq.le) (div_nonneg (Real.rpow_nonneg hR.le _) (by linarith))
  calc ∫⁻ y in T, ENNReal.ofReal (|k y| / φ y)
      = ∫⁻ y, T.indicator (fun y ↦ ENNReal.ofReal (|k y| / φ y)) y :=
        (lintegral_indicator (measurableSet_quadrantFar R) _).symm
    _ ≤ ∫⁻ y, G y := lintegral_mono hpt
    _ ≤ _ := lintegral_le_polar hG0
    _ = (∫⁻ ρ in Ioi (0 : ℝ), (Ici R).indicator
          (fun ρ ↦ ENNReal.ofReal (q⁻¹ * ρ ^ (1 - p - a))) ρ) *
          ∫⁻ θ in Ioo 0 (Real.pi / 2), ENNReal.ofReal (Real.cos θ ^ (-b)) := by
        rw [← lintegral_mul_const _ hmA]
        exact setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ hpolar ρ hρ
    _ ≤ ENNReal.ofReal (q⁻¹ * (R ^ (2 - p - a) / (p + a - 2))) *
          ENNReal.ofReal ((Real.pi / 2) ^ (1 + b)) := by
        rw [hrad]; exact mul_le_mul' le_rfl hθ
    _ = _ := by
        rw [← ENNReal.ofReal_mul hrad0]
        congr 1
        have : p + a - 2 ≠ 0 := by linarith
        field_simp

end PotentialTheory.Planar
