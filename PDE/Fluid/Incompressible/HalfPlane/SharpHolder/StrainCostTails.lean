/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainCostCells

/-!
# Tail bounds for the transport cost of the strain estimate

The cell bounds for `strainCost` need cells with `x₀ > 1/2` inside a bounded rectangle. Three
pieces of the quadrant `s₁ > 1/2`, `s₂ > 0` that are unbounded or touch the corner are bounded
here by explicit primitives. All three rest on the kernel bound `|Δ(s₁, s₂)| ≤ D^{-3/2}`,
`D = (s₁ - 1/2)² + s₂²`, for `s₁ ≥ 1/2` and `s₂ > 0`, which is the mean value theorem for
`t ↦ K₁(t, s₂)` on `[s₁ - 1/2, s₁ + 1/2]` (`abs_strainDifference_le`).

## Main results

* `abs_strainDifference_le`: for `s₁ ≥ 1/2` and `s₂ > 0`, `|Δ(s₁, s₂)| ≤ D^{-3/2}`.
* `lintegral_strainCostIntegrand_corner_le`: the corner strip `(1/2, 1/2 + x_c] × (0, z₁]` costs
  at most `√(2 x_c)`; there `-Δ ≤ K₁(s₁ - 1/2, s₂)`, `s₁ - T ≤ 2 s₁ - 1` and
  `∫_0^∞ K₁(a, s₂) ds₂ = 1/(2a)`.
* `lintegral_strainCostIntegrand_far_right_le`: the far right `(R₁, ∞) × (0, R]` with `R₁ ≥ 1`
  costs at most `8/√R₁`; there `s₁ - T ≤ s₁` and `∫_0^∞ D^{-3/2} ds₂ = (s₁ - 1/2)^{-2}`.
* `strainCost_le_of_one_le`: for `s₂ ≥ 1`, `M(s₂) ≤ (5/4) s₂^{-3/2}`, by the tangent bound
  `√s₁ ≤ (s₁ + s₂)/(2√s₂)`.
* `lintegral_strainCost_far_top_le`: the far top `s₂ > R ≥ 1` costs at most
  `(5/2)/√R ≤ 4/√R`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-! ### Primitives on half-lines and intervals -/

/-- The lower integral of a nonnegative derivative over `(a, ∞)` is the increment of the
primitive. -/
theorem lintegral_Ioi_ofReal_deriv {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g a) := by
  rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hg)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hpos x hx

/-- The lower integral of a nonnegative derivative over `(a, b]` is the increment of the
primitive. -/
theorem lintegral_Ioc_ofReal_deriv {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hpos : ∀ x ∈ Ioc a b, 0 ≤ g' x) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (g' x) = ENNReal.ofReal (g b - g a) := by
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv
    fun x hx ↦ hpos x (Ioo_subset_Ioc_self hx)
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hint),
    intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hpos x hx

/-- `x / √(x² + q) → 1` as `x → ∞`, for `q ≥ 0`. -/
theorem tendsto_div_sqrt_sq_add {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun x : ℝ ↦ x / Real.sqrt (x ^ 2 + q)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ ↦ q / (x ^ 2 + q)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ q (tendsto_pow_atTop two_ne_zero))
  have h : Tendsto (fun x : ℝ ↦ Real.sqrt (1 - q / (x ^ 2 + q))) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).sqrt
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hpos : 0 < x ^ 2 + q := add_pos_of_pos_of_nonneg (pow_pos hx 2) hq
  rw [show 1 - q / (x ^ 2 + q) = x ^ 2 / (x ^ 2 + q) by field_simp; ring,
    Real.sqrt_div' _ hpos.le, Real.sqrt_sq hx.le]

/-- `∫_R^∞ c / (s √s) ds = 2c/√R` for `R > 0`, `c ≥ 0`. -/
theorem lintegral_Ioi_div_mul_sqrt {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) :
    ∫⁻ s in Ioi R, ENNReal.ofReal (c / (s * Real.sqrt s)) =
      ENNReal.ofReal (2 * c / Real.sqrt R) := by
  have h := lintegral_Ioi_ofReal_deriv (a := R) (l := 0) (g := fun s ↦ -(2 * c) / Real.sqrt s)
    (g' := fun s ↦ c / (s * Real.sqrt s)) (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    (tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop)
  · rw [h]
    congr 1
    ring
  · have hs0 : 0 < s := hR.trans_le hs
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    refine ((hasDerivAt_const s (-(2 * c))).div (Real.hasDerivAt_sqrt hs0.ne')
      hsq.ne').congr_deriv ?_
    have := Real.sq_sqrt hs0.le
    field_simp
    nlinarith
  · have hs0 : 0 < s := hR.trans hs
    exact div_nonneg hc (mul_nonneg hs0.le (Real.sqrt_nonneg _))

/-! ### The pointwise bound of the difference kernel -/

/-- `∂ₐ K₁(a, b) = b (b² - 3a²)/(a² + b²)³` for `b ≠ 0`. -/
theorem hasDerivAt_strainDensity_left {b : ℝ} (hb : b ≠ 0) (a : ℝ) :
    HasDerivAt (fun t ↦ strainDensity t b) (b * (b ^ 2 - 3 * a ^ 2) / (a ^ 2 + b ^ 2) ^ 3) a := by
  have hpos : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hg : HasDerivAt (fun t ↦ (t ^ 2 + b ^ 2) ^ 2) (2 * (a ^ 2 + b ^ 2) * (2 * a)) a := by
    have := ((hasDerivAt_pow 2 a).add_const (b ^ 2)).fun_pow 2
    simpa using this
  have h := ((hasDerivAt_id' a).mul_const b).div hg (pow_ne_zero 2 hpos)
  simp only [strainDensity_eq]
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `|∂ₐ K₁(t, b)| ≤ (u² + b²)^{-3/2}` for `0 ≤ u ≤ t` and `b > 0`. -/
private theorem abs_deriv_strainDensity_le {t u b : ℝ} (hu : 0 ≤ u) (ht : u ≤ t) (hb : 0 < b) :
    |b * (b ^ 2 - 3 * t ^ 2) / (t ^ 2 + b ^ 2) ^ 3| ≤
      1 / ((u ^ 2 + b ^ 2) * Real.sqrt (u ^ 2 + b ^ 2)) := by
  have hD : 0 < u ^ 2 + b ^ 2 := by positivity
  have hDE : u ^ 2 + b ^ 2 ≤ t ^ 2 + b ^ 2 := by nlinarith
  have hE : 0 < t ^ 2 + b ^ 2 := hD.trans_le hDE
  have hsE := Real.sq_sqrt hE.le
  have hsDE : Real.sqrt (u ^ 2 + b ^ 2) ≤ Real.sqrt (t ^ 2 + b ^ 2) := Real.sqrt_le_sqrt hDE
  have hsD := Real.sqrt_nonneg (u ^ 2 + b ^ 2)
  have hnum : |b * (b ^ 2 - 3 * t ^ 2)| ≤ (t ^ 2 + b ^ 2) * Real.sqrt (t ^ 2 + b ^ 2) := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have e : ((t ^ 2 + b ^ 2) * Real.sqrt (t ^ 2 + b ^ 2)) ^ 2 = (t ^ 2 + b ^ 2) ^ 3 := by
      rw [mul_pow, hsE]
      ring
    rw [e]
    nlinarith [sq_nonneg (t * (t ^ 2 - 3 * b ^ 2))]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (t ^ 2 + b ^ 2) ^ 3),
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc |b * (b ^ 2 - 3 * t ^ 2)| * ((u ^ 2 + b ^ 2) * Real.sqrt (u ^ 2 + b ^ 2))
      ≤ ((t ^ 2 + b ^ 2) * Real.sqrt (t ^ 2 + b ^ 2)) *
          ((t ^ 2 + b ^ 2) * Real.sqrt (t ^ 2 + b ^ 2)) :=
        mul_le_mul hnum (mul_le_mul hDE hsDE hsD hE.le) (by positivity) (by positivity)
    _ = (t ^ 2 + b ^ 2) ^ 3 := by
        rw [show (t ^ 2 + b ^ 2) * Real.sqrt (t ^ 2 + b ^ 2) *
            ((t ^ 2 + b ^ 2) * Real.sqrt (t ^ 2 + b ^ 2)) =
            (t ^ 2 + b ^ 2) ^ 2 * Real.sqrt (t ^ 2 + b ^ 2) ^ 2 by ring, hsE]
        ring

/-- **The kernel bound.** For `s₁ ≥ 1/2` and `s₂ > 0`, `|Δ(s₁, s₂)| ≤ D^{-3/2}` with
`D = (s₁ - 1/2)² + s₂²`. -/
theorem abs_strainDifference_le {s₁ s₂ : ℝ} (hs₁ : 1 / 2 ≤ s₁) (hs₂ : 0 < s₂) :
    |strainDifference s₁ s₂| ≤
      1 / (((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) * Real.sqrt ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2)) := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t ↦ strainDensity t s₂)
    (a := s₁ - 1 / 2) (b := s₁ + 1 / 2)
    (C := 1 / (((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) * Real.sqrt ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2)))
    (fun t _ ↦ (hasDerivAt_strainDensity_left hs₂.ne' t).hasDerivWithinAt)
    (fun t ht ↦ by
      rw [Real.norm_eq_abs]
      exact abs_deriv_strainDensity_le (by linarith) ht.1 hs₂)
    (s₁ + 1 / 2) ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs, show s₁ + 1 / 2 - (s₁ - 1 / 2) = 1 by ring, mul_one] at key
  exact key

/-! ### The corner strip -/

/-- `∫_0^∞ K₁(a, b) c db = c/(2a)` for `a > 0` and `c ≥ 0`. -/
theorem lintegral_Ioi_strainDensity_mul {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ∫⁻ b in Ioi 0, ENNReal.ofReal (a * b / (a ^ 2 + b ^ 2) ^ 2 * c) =
      ENNReal.ofReal (c / (2 * a)) := by
  have hlim : Tendsto (fun b : ℝ ↦ 2 * (a ^ 2 + b ^ 2)) atTop atTop :=
    Tendsto.const_mul_atTop two_pos
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  have h := lintegral_Ioi_ofReal_deriv (a := 0) (l := 0)
    (g := fun b ↦ -(a * c) / (2 * (a ^ 2 + b ^ 2)))
    (g' := fun b ↦ a * b / (a ^ 2 + b ^ 2) ^ 2 * c) (fun b _ ↦ ?_) (fun b hb ↦ ?_)
    (tendsto_const_nhds.div_atTop hlim)
  · rw [h]
    congr 1
    field_simp
    ring
  · have hpos : 0 < a ^ 2 + b ^ 2 := by positivity
    have hd : HasDerivAt (fun b ↦ 2 * (a ^ 2 + b ^ 2)) (2 * (2 * b)) b := by
      simpa using ((hasDerivAt_pow 2 b).const_add (a ^ 2)).const_mul 2
    refine ((hasDerivAt_const b (-(a * c))).div hd (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hb0 : 0 < b := hb
    positivity

/-- Near the corner, the integrand is at most `K₁(s₁ - 1/2, s₂) √(2 (s₁ - 1/2))`: there
`-Δ ≤ K₁(s₁ - 1/2, s₂)` and `s₁ - T ≤ 2 s₁ - 1`. -/
theorem strainCostIntegrand_le_corner {s₁ s₂ : ℝ} (hs₁ : 1 / 2 < s₁) (hs₂ : 0 < s₂) :
    strainCostIntegrand s₂ s₁ ≤ ENNReal.ofReal ((s₁ - 1 / 2) * s₂ /
      ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * Real.sqrt (2 * (s₁ - 1 / 2))) := by
  unfold strainCostIntegrand
  by_cases hs : s₁ ∈ Ioi (strainThreshold s₂)
  · rw [indicator_of_mem hs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hΔ := strainDifference_nonpos hs₂ (le_of_lt hs)
    have hT := strainMap_le_self hs₂ (le_of_lt hs)
    have hT' := one_sub_le_strainMap (s₂ := s₂) (by linarith : 0 < s₁)
    have hK : 0 ≤ strainDensity (s₁ + 1 / 2) s₂ := by
      rw [strainDensity_eq]
      have : 0 < s₁ + 1 / 2 := by linarith
      positivity
    generalize strainMap s₁ s₂ = T at hT hT' ⊢
    rw [abs_of_nonpos hΔ, abs_of_nonpos (by linarith), ← Real.sqrt_eq_rpow]
    refine mul_le_mul ?_ (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
      (div_nonneg (mul_nonneg (by linarith) hs₂.le) (by positivity))
    rw [← strainDensity_eq]
    unfold strainDifference
    linarith
  · rw [indicator_of_notMem hs]
    exact zero_le

/-- **The corner strip.** For `x_c > 0` and any `z₁`, the integral of the integrand over
`(0, z₁] × (1/2, 1/2 + x_c]` is at most `√(2 x_c)`. -/
theorem lintegral_strainCostIntegrand_corner_le {xc z₁ : ℝ} (hxc : 0 < xc) :
    ∫⁻ s₂ in Ioc 0 z₁, ∫⁻ s₁ in Ioc (1 / 2) (1 / 2 + xc), strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (Real.sqrt (2 * xc)) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun s₂ s₁ ↦ ENNReal.ofReal ((s₁ - 1 / 2) * s₂ /
    ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * Real.sqrt (2 * (s₁ - 1 / 2)))
  have hF : Measurable fun p : ℝ × ℝ ↦ F p.1 p.2 := by
    simp only [F]
    fun_prop
  calc ∫⁻ s₂ in Ioc 0 z₁, ∫⁻ s₁ in Ioc (1 / 2) (1 / 2 + xc), strainCostIntegrand s₂ s₁
      ≤ ∫⁻ s₂ in Ioc 0 z₁, ∫⁻ s₁ in Ioc (1 / 2) (1 / 2 + xc), F s₂ s₁ :=
        setLIntegral_mono' measurableSet_Ioc fun s₂ hs₂ ↦
          setLIntegral_mono' measurableSet_Ioc fun s₁ hs₁ ↦
            strainCostIntegrand_le_corner hs₁.1 hs₂.1
    _ ≤ ∫⁻ s₂ in Ioi 0, ∫⁻ s₁ in Ioc (1 / 2) (1 / 2 + xc), F s₂ s₁ :=
        lintegral_mono_set Ioc_subset_Ioi_self
    _ = ∫⁻ s₁ in Ioc (1 / 2) (1 / 2 + xc), ∫⁻ s₂ in Ioi 0, F s₂ s₁ :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ s₁ in Ioc (1 / 2) (1 / 2 + xc),
          ENNReal.ofReal (1 / Real.sqrt (2 * (s₁ - 1 / 2))) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun s₁ hs₁ ↦ ?_
        have ha : 0 < s₁ - 1 / 2 := by linarith [hs₁.1]
        rw [lintegral_Ioi_strainDensity_mul ha (Real.sqrt_nonneg _)]
        congr 1
        have h2 : 0 < 2 * (s₁ - 1 / 2) := by linarith
        have hsq := Real.sq_sqrt h2.le
        have hne := (Real.sqrt_pos.2 h2).ne'
        rw [div_eq_div_iff (by linarith) hne, one_mul, ← sq, hsq]
    _ = ENNReal.ofReal (Real.sqrt (2 * xc)) := by
        rw [lintegral_Ioc_ofReal_deriv (g := fun s₁ ↦ Real.sqrt (2 * (s₁ - 1 / 2)))
          (by linarith) (by fun_prop) (fun s₁ hs₁ ↦ ?_) (fun s₁ _ ↦ by positivity)]
        · rw [show 1 / 2 + xc - 1 / 2 = xc by ring, sub_self, mul_zero, Real.sqrt_zero,
            sub_zero]
        · have h2 : 0 < 2 * (s₁ - 1 / 2) := by linarith [hs₁.1]
          have hne := (Real.sqrt_pos.2 h2).ne'
          refine ((((hasDerivAt_id' s₁).sub_const (1 / 2)).const_mul 2).sqrt
            h2.ne').congr_deriv ?_
          field_simp

/-! ### The far right -/

/-- `∫_0^∞ k (a² + b²)^{-3/2} db = k/a²` for `a > 0` and `k ≥ 0`. -/
theorem lintegral_Ioi_three_halves {a k : ℝ} (ha : 0 < a) (hk : 0 ≤ k) :
    ∫⁻ b in Ioi 0, ENNReal.ofReal (k * (1 / ((a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2)))) =
      ENNReal.ofReal (k / a ^ 2) := by
  have hlim : Tendsto (fun b : ℝ ↦ k / a ^ 2 * (b / Real.sqrt (a ^ 2 + b ^ 2))) atTop
      (𝓝 (k / a ^ 2)) := by
    have h := ((tendsto_div_sqrt_sq_add (sq_nonneg a)).const_mul (k / a ^ 2))
    rw [mul_one] at h
    exact h.congr fun b ↦ by rw [add_comm (b ^ 2)]
  have h := lintegral_Ioi_ofReal_deriv (a := 0)
    (g := fun b ↦ k / a ^ 2 * (b / Real.sqrt (a ^ 2 + b ^ 2)))
    (g' := fun b ↦ k * (1 / ((a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2)))) (fun b _ ↦ ?_)
    (fun b _ ↦ ?_) hlim
  · rw [h]
    simp
  · have hE : 0 < a ^ 2 + b ^ 2 := by positivity
    have hd : HasDerivAt (fun b ↦ a ^ 2 + b ^ 2) (2 * b) b := by
      simpa using (hasDerivAt_pow 2 b).const_add (a ^ 2)
    have hσ := hd.sqrt hE.ne'
    have hσ0 := Real.sqrt_pos.2 hE
    refine (((hasDerivAt_id' b).div hσ hσ0.ne').const_mul (k / a ^ 2)).congr_deriv ?_
    have hσ2 := Real.sq_sqrt hE.le
    generalize Real.sqrt (a ^ 2 + b ^ 2) = σ at hσ0 hσ2 ⊢
    rw [← hσ2]
    field_simp
    linear_combination k * hσ2
  · have hE : 0 < a ^ 2 + b ^ 2 := by positivity
    positivity

/-- For `s₁ ≥ 1/2` and `s₂ > 0`, the integrand is at most `√s₁ D^{-3/2}`,
`D = (s₁ - 1/2)² + s₂²`: there `0 < T ≤ s₁`. -/
theorem strainCostIntegrand_le_sqrt {s₁ s₂ : ℝ} (hs₁ : 1 / 2 ≤ s₁) (hs₂ : 0 < s₂) :
    strainCostIntegrand s₂ s₁ ≤ ENNReal.ofReal (Real.sqrt s₁ *
      (1 / (((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) * Real.sqrt ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2)))) := by
  unfold strainCostIntegrand
  by_cases hs : s₁ ∈ Ioi (strainThreshold s₂)
  · rw [indicator_of_mem hs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hT := strainMap_le_self hs₂ (le_of_lt hs)
    have hT0 := strainMap_pos (by linarith : 0 < s₁) hs₂.ne'
    have hΔ := abs_strainDifference_le hs₁ hs₂
    generalize strainMap s₁ s₂ = T at hT hT0 ⊢
    rw [mul_comm, ← Real.sqrt_eq_rpow]
    refine mul_le_mul (Real.sqrt_le_sqrt ?_) hΔ (abs_nonneg _) (Real.sqrt_nonneg _)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [indicator_of_notMem hs]
    exact zero_le

/-- **The far right.** For `R₁ ≥ 1` and any `R`, the integral of the integrand over
`(0, R] × (R₁, ∞)` is at most `8/√R₁`. -/
theorem lintegral_strainCostIntegrand_far_right_le {R₁ R : ℝ} (hR₁ : 1 ≤ R₁) :
    ∫⁻ s₂ in Ioc 0 R, ∫⁻ s₁ in Ioi R₁, strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (8 / Real.sqrt R₁) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun s₂ s₁ ↦ ENNReal.ofReal (Real.sqrt s₁ *
    (1 / (((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) * Real.sqrt ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2))))
  have hF : Measurable fun p : ℝ × ℝ ↦ F p.1 p.2 := by
    simp only [F]
    fun_prop
  calc ∫⁻ s₂ in Ioc 0 R, ∫⁻ s₁ in Ioi R₁, strainCostIntegrand s₂ s₁
      ≤ ∫⁻ s₂ in Ioc 0 R, ∫⁻ s₁ in Ioi R₁, F s₂ s₁ :=
        setLIntegral_mono' measurableSet_Ioc fun s₂ hs₂ ↦
          setLIntegral_mono' measurableSet_Ioi fun s₁ hs₁ ↦
            strainCostIntegrand_le_sqrt (by linarith [hs₁.out]) hs₂.1
    _ ≤ ∫⁻ s₂ in Ioi 0, ∫⁻ s₁ in Ioi R₁, F s₂ s₁ := lintegral_mono_set Ioc_subset_Ioi_self
    _ = ∫⁻ s₁ in Ioi R₁, ∫⁻ s₂ in Ioi 0, F s₂ s₁ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ s₁ in Ioi R₁, ENNReal.ofReal (Real.sqrt s₁ / (s₁ - 1 / 2) ^ 2) :=
        setLIntegral_congr_fun measurableSet_Ioi fun s₁ hs₁ ↦
          lintegral_Ioi_three_halves (by linarith [hs₁.out]) (Real.sqrt_nonneg _)
    _ ≤ ∫⁻ s₁ in Ioi R₁, ENNReal.ofReal (4 / (s₁ * Real.sqrt s₁)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun s₁ hs₁ ↦ ENNReal.ofReal_le_ofReal ?_
        have h1 : 1 < s₁ := hR₁.trans_lt hs₁
        have hsq := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ s₁)
        have hr := Real.sqrt_pos.2 (by linarith : (0 : ℝ) < s₁)
        rw [div_le_div_iff₀ (by nlinarith) (by positivity),
          show Real.sqrt s₁ * (s₁ * Real.sqrt s₁) = s₁ * (Real.sqrt s₁ * Real.sqrt s₁) by ring,
          hsq]
        nlinarith
    _ = ENNReal.ofReal (8 / Real.sqrt R₁) := by
        rw [lintegral_Ioi_div_mul_sqrt (by linarith) (by norm_num)]
        norm_num

/-! ### The far top -/

/-- For `s₂ > 0`, the integrand is at most `(s₁ + s₂)/(2√s₂) D^{-3/2}` on `s₁ > 1/2` and
vanishes on `s₁ ≤ 1/2`, by the tangent bound `√s₁ ≤ (s₁ + s₂)/(2√s₂)`. -/
theorem strainCostIntegrand_le_indicator {s₁ s₂ : ℝ} (hs₂ : 0 < s₂) :
    strainCostIntegrand s₂ s₁ ≤ (Ioi (1 / 2)).indicator (fun s₁ ↦ ENNReal.ofReal
      ((s₁ + s₂) / (2 * Real.sqrt s₂) *
        (1 / (((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) * Real.sqrt ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2))))) s₁ := by
  by_cases h : s₁ ∈ Ioi (1 / 2)
  · rw [indicator_of_mem h]
    refine (strainCostIntegrand_le_sqrt h.out.le hs₂).trans (ENNReal.ofReal_le_ofReal ?_)
    have hr := Real.sqrt_pos.2 hs₂
    have ht := sqrt_le_tangent (by linarith [h.out] : 0 ≤ s₁) hr
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hs₂.le] at ht
    have hD : 0 < (s₁ - 1 / 2) ^ 2 + s₂ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right ht (by positivity)
  · have h' : s₁ ∉ Ioi (strainThreshold s₂) := fun h' ↦
      h (lt_of_le_of_lt (one_half_le_strainThreshold s₂) h')
    unfold strainCostIntegrand
    rw [indicator_of_notMem h']
    exact zero_le

/-- For `s₂ ≥ 1`, `M(s₂) ≤ (5/4) s₂^{-3/2}`. -/
theorem strainCost_le_of_one_le {s₂ : ℝ} (hs₂ : 1 ≤ s₂) :
    strainCost s₂ ≤ ENNReal.ofReal (5 / 4 / (s₂ * Real.sqrt s₂)) := by
  have hs : 0 < s₂ := by linarith
  have hr := Real.sqrt_pos.2 hs
  have hsub : Tendsto (fun x : ℝ ↦ x - 1 / 2) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-(1 / 2)) tendsto_id).congr fun x ↦ by
      simp [sub_eq_add_neg]
  have hE : Tendsto (fun x : ℝ ↦ (x - 1 / 2) ^ 2 + s₂ ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop two_ne_zero).comp hsub)
  have hlim : Tendsto (fun x : ℝ ↦ 1 / (2 * Real.sqrt s₂) *
      (-1 / Real.sqrt ((x - 1 / 2) ^ 2 + s₂ ^ 2) +
        (1 / 2 + s₂) / s₂ ^ 2 * ((x - 1 / 2) / Real.sqrt ((x - 1 / 2) ^ 2 + s₂ ^ 2)))) atTop
      (𝓝 (1 / (2 * Real.sqrt s₂) * (0 + (1 / 2 + s₂) / s₂ ^ 2 * 1))) :=
    ((tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hE)).add
      (((tendsto_div_sqrt_sq_add (sq_nonneg s₂)).comp hsub).const_mul _)).const_mul _
  have h := lintegral_Ioi_ofReal_deriv (a := 1 / 2)
    (g' := fun x ↦ (x + s₂) / (2 * Real.sqrt s₂) *
      (1 / (((x - 1 / 2) ^ 2 + s₂ ^ 2) * Real.sqrt ((x - 1 / 2) ^ 2 + s₂ ^ 2))))
    (fun x _ ↦ ?_) (fun x hx ↦ ?_) hlim
  · rw [strainCost_eq]
    refine (lintegral_mono fun s₁ ↦ strainCostIntegrand_le_indicator hs).trans ?_
    rw [lintegral_indicator measurableSet_Ioi, h]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      zero_div, mul_zero, add_zero, mul_one]
    rw [Real.sqrt_sq hs.le]
    have e : 1 / (2 * Real.sqrt s₂) * ((1 / 2 + s₂) / s₂ ^ 2) -
        1 / (2 * Real.sqrt s₂) * (-1 / s₂) = (1 + 4 * s₂) / (4 * Real.sqrt s₂ * s₂ ^ 2) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hs.le hr.le) (sub_nonneg.2 hs₂)]
  · have hE0 : 0 < (x - 1 / 2) ^ 2 + s₂ ^ 2 := by positivity
    have hd : HasDerivAt (fun x ↦ (x - 1 / 2) ^ 2 + s₂ ^ 2) (2 * (x - 1 / 2)) x := by
      convert (((hasDerivAt_id' x).sub_const (1 / 2)).fun_pow 2).add_const (s₂ ^ 2) using 1
      norm_num
    have hσ := hd.sqrt hE0.ne'
    have hσ0 := Real.sqrt_pos.2 hE0
    refine ((((hasDerivAt_const x (-1 : ℝ)).div hσ hσ0.ne').add
      ((((hasDerivAt_id' x).sub_const (1 / 2)).div hσ hσ0.ne').const_mul
        ((1 / 2 + s₂) / s₂ ^ 2))).const_mul (1 / (2 * Real.sqrt s₂))).congr_deriv ?_
    have hσ2 := Real.sq_sqrt hE0.le
    generalize Real.sqrt ((x - 1 / 2) ^ 2 + s₂ ^ 2) = σ at hσ0 hσ2 ⊢
    rw [← hσ2]
    field_simp
    linear_combination (4 + 8 * s₂) * hσ2
  · have hx0 : 1 / 2 < x := hx
    have hE0 : 0 < (x - 1 / 2) ^ 2 + s₂ ^ 2 := by positivity
    have : 0 < x + s₂ := by linarith
    positivity

/-- **The far top.** For `R ≥ 1`, `∫_R^∞ M(s₂) ds₂ ≤ (5/2)/√R ≤ 4/√R`. -/
theorem lintegral_strainCost_far_top_le {R : ℝ} (hR : 1 ≤ R) :
    ∫⁻ s₂ in Ioi R, strainCost s₂ ≤ ENNReal.ofReal (4 / Real.sqrt R) := by
  calc ∫⁻ s₂ in Ioi R, strainCost s₂
      ≤ ∫⁻ s₂ in Ioi R, ENNReal.ofReal (5 / 4 / (s₂ * Real.sqrt s₂)) :=
        setLIntegral_mono' measurableSet_Ioi fun s₂ hs₂ ↦
          strainCost_le_of_one_le (hR.trans hs₂.out.le)
    _ = ENNReal.ofReal (2 * (5 / 4) / Real.sqrt R) :=
        lintegral_Ioi_div_mul_sqrt (by linarith) (by norm_num)
    _ ≤ ENNReal.ofReal (4 / Real.sqrt R) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

end IncompressibleFlow.SharpHolder
