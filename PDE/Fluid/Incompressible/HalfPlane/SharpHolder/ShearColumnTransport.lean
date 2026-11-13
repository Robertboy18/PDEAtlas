/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearTransport

/-!
# Vertical transport on whole columns of the vertical Hölder estimate of `u_y` and `v_x`

Chen and Hou, Part I, Appendix B.2, (B.54)-(B.56): after rotating and rescaling, on a column
`p > 1` the kernel `Δ(p, ·)` of the unlocalized `u_y`, `v_x` is even, and on `q ≥ 0` negative
below the sign threshold `s_c(p)` and positive above it, with `∫_0^∞ Δ(p, q) dq = 0` (the columns
`p < -1` follow from `Δ(-p, q) = -Δ(p, q)`). The vertical map `T` of (B.66) (`shearMap`)
transports the positive part onto the negative one, so a `1/2`-Hölder `g` on the line satisfies

`|∫ Δ(p, q) g(q) dq| ≤ 2 C ∫_{s_c(p)}^∞ |Δ(p, q)| |q - T(p, q)|^{1/2} dq`

(`abs_integral_shearDifference_mul_le_column`). The column is the whole line, so the half-line
form of the transport lemma is used.

## Main results

* `abs_shearDensity_le`, `abs_shearDifference_le`: kernel bounds.
* `integrable_shearDifference_right`: `Δ(p, ·)` and `Δ(p, ·) |· - c|^{1/2}` are integrable.
* `integral_Ioi_shearDifference`: `∫_0^∞ Δ(p, q) dq = 0`.
* `shearColumnCost`: the column cost.
* `abs_integral_shearDifference_mul_le_column`: the column estimate.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.6, p. 29, Appendix B.2.2,
  (B.54)-(B.56), p. 139, and (B.66), p. 142.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE.Analysis.Rearrangement
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- `|K₂(a, b)| ≤ 1 / (2 (a² + b²))` (both sides vanish at the origin). -/
theorem abs_shearDensity_le (a b : ℝ) : |shearDensity a b| ≤ 1 / (2 * (a ^ 2 + b ^ 2)) := by
  rw [shearDensity_eq]
  rcases eq_or_ne (a ^ 2 + b ^ 2) 0 with h0 | h0
  · rw [h0]
    simp
  · have hp : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (a ^ 2 + b ^ 2) ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : |a ^ 2 - b ^ 2| ≤ a ^ 2 + b ^ 2 :=
      abs_le.2 ⟨by nlinarith [sq_nonneg a, sq_nonneg b], by nlinarith [sq_nonneg a, sq_nonneg b]⟩
    nlinarith

/-- On a column `|p| > 1`, `|Δ(p, q)| ≤ 1 / ((|p| - 1)² + q²)`. -/
theorem abs_shearDifference_le {p : ℝ} (hp : 1 < |p|) (q : ℝ) :
    |shearDifference p q| ≤ 1 / ((|p| - 1) ^ 2 + q ^ 2) := by
  have ha : 0 < |p| - 1 := by linarith
  have h₁ : (|p| - 1) ^ 2 ≤ (p + 1) ^ 2 := by
    rcases le_or_gt 0 p with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  have h₂ : (|p| - 1) ^ 2 ≤ (p - 1) ^ 2 := by
    rcases le_or_gt 0 p with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]; nlinarith
  have hd : 0 < (|p| - 1) ^ 2 + q ^ 2 := by positivity
  have e₁ : 1 / (2 * ((p + 1) ^ 2 + q ^ 2)) ≤ 1 / (2 * ((|p| - 1) ^ 2 + q ^ 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e₂ : 1 / (2 * ((p - 1) ^ 2 + q ^ 2)) ≤ 1 / (2 * ((|p| - 1) ^ 2 + q ^ 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc |shearDifference p q| ≤ |shearDensity (p + 1) q| + |shearDensity (p - 1) q| :=
        abs_sub _ _
    _ ≤ 1 / (2 * ((p + 1) ^ 2 + q ^ 2)) + 1 / (2 * ((p - 1) ^ 2 + q ^ 2)) :=
        add_le_add (abs_shearDensity_le _ _) (abs_shearDensity_le _ _)
    _ ≤ _ := by
        have : 1 / (2 * ((|p| - 1) ^ 2 + q ^ 2)) + 1 / (2 * ((|p| - 1) ^ 2 + q ^ 2)) =
            1 / ((|p| - 1) ^ 2 + q ^ 2) := by field_simp; ring
        linarith

/-- `Δ(p, ·)` is continuous off the poles, `p ≠ ± 1`. -/
theorem continuous_shearDifference_right {p : ℝ} (hp₁ : p + 1 ≠ 0) (hp₂ : p - 1 ≠ 0) :
    Continuous (shearDifference p) :=
  (continuous_shearDensity_right hp₁).sub (continuous_shearDensity_right hp₂)

/-- On a column `|p| > 1`, `|Δ(p, q)| (1 + |q - c|^{1/2}) ≤ K (1 + q²)^{-3/4}` for a constant
`K` depending on `p` and `c`. -/
private theorem abs_shearDifference_mul_le {p : ℝ} (hp : 1 < |p|) (c : ℝ) :
    ∃ K : ℝ, ∀ q, |shearDifference p q| * (1 + |q - c| ^ (1 / 2 : ℝ)) ≤
      K * ((1 : ℝ) + ‖q‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
  set a := |p| - 1 with ha
  have ha0 : 0 < a := by linarith
  refine ⟨(1 / min 1 (a ^ 2)) * (2 + |c| ^ (1 / 2 : ℝ)), fun q ↦ ?_⟩
  have hm : 0 < min 1 (a ^ 2) := lt_min one_pos (by positivity)
  have hq1 : (0 : ℝ) < 1 + q ^ 2 := by positivity
  have hnorm : ‖q‖ ^ 2 = q ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  -- the kernel
  have hk : |shearDifference p q| ≤ 1 / min 1 (a ^ 2) * (1 + q ^ 2)⁻¹ := by
    refine (abs_shearDifference_le hp q).trans ?_
    rw [one_div, one_div, ← mul_inv, ← ha]
    refine inv_anti₀ (by positivity) ?_
    have h1 : min 1 (a ^ 2) ≤ 1 := min_le_left _ _
    have h2 : min 1 (a ^ 2) ≤ a ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg q]
  -- the weight
  have hw : 1 + |q - c| ^ (1 / 2 : ℝ) ≤ (2 + |c| ^ (1 / 2 : ℝ)) * (1 + q ^ 2) ^ (1 / 4 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (1 + q ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
    have h2 : |q - c| ^ (1 / 2 : ℝ) ≤ |q| ^ (1 / 2 : ℝ) + |c| ^ (1 / 2 : ℝ) := by
      calc |q - c| ^ (1 / 2 : ℝ) ≤ (|q| + |c|) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (abs_nonneg _) (abs_sub _ _) (by norm_num)
        _ ≤ |q| ^ (1 / 2 : ℝ) + |c| ^ (1 / 2 : ℝ) :=
            Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) (by norm_num) (by norm_num)
    have h3 : |q| ^ (1 / 2 : ℝ) ≤ (1 + q ^ 2) ^ (1 / 4 : ℝ) := by
      rw [show |q| ^ (1 / 2 : ℝ) = (q ^ 2) ^ (1 / 4 : ℝ) by
        rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; norm_num]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    linarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ |c| ^ (1 / 2 : ℝ))]
  have hpow : (1 + q ^ 2)⁻¹ * (1 + q ^ 2) ^ (1 / 4 : ℝ) = (1 + q ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hq1]
    norm_num
  calc |shearDifference p q| * (1 + |q - c| ^ (1 / 2 : ℝ))
      ≤ (1 / min 1 (a ^ 2) * (1 + q ^ 2)⁻¹) *
          ((2 + |c| ^ (1 / 2 : ℝ)) * (1 + q ^ 2) ^ (1 / 4 : ℝ)) :=
        mul_le_mul hk hw (by positivity) (by positivity)
    _ = _ := by rw [← hpow]; ring

/-- For `|p| > 1`, `p + 1 ≠ 0` and `p - 1 ≠ 0`. -/
private theorem ne_of_one_lt_abs {p : ℝ} (hp : 1 < |p|) : p + 1 ≠ 0 ∧ p - 1 ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show p = -1 by linarith] at hp; norm_num at hp
  · rw [show p = 1 by linarith] at hp; norm_num at hp

/-- On a column `|p| > 1`, `Δ(p, ·)` and `Δ(p, ·) |· - c|^{1/2}` are integrable on the line. -/
theorem integrable_shearDifference_right {p : ℝ} (hp : 1 < |p|) (c : ℝ) :
    Integrable (shearDifference p) ∧
      Integrable fun q ↦ shearDifference p q * |q - c| ^ (1 / 2 : ℝ) := by
  obtain ⟨hp₁, hp₂⟩ := ne_of_one_lt_abs hp
  have hc := continuous_shearDifference_right hp₁ hp₂
  obtain ⟨K, hK⟩ := abs_shearDifference_mul_le hp c
  have hJ : Integrable fun q : ℝ ↦ K * ((1 : ℝ) + ‖q‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) :=
    (integrable_rpow_neg_one_add_norm_sq (by norm_num)).const_mul K
  refine ⟨hJ.mono' hc.aestronglyMeasurable (Eventually.of_forall fun q ↦ ?_),
    hJ.mono' (hc.mul ((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
      fun _ ↦ Or.inr (by norm_num))).aestronglyMeasurable (Eventually.of_forall fun q ↦ ?_)⟩
  · refine le_trans ?_ (hK q)
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (shearDifference p q), Real.rpow_nonneg (abs_nonneg (q - c)) (1 / 2 : ℝ)]
  · refine le_trans ?_ (hK q)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    nlinarith [abs_nonneg (shearDifference p q), Real.rpow_nonneg (abs_nonneg (q - c)) (1 / 2 : ℝ)]

/-- The primitive `Ψ` of `Δ(p, ·)` tends to `0` at infinity. -/
theorem tendsto_shearPotential (p : ℝ) :
    Tendsto (shearPotential p) atTop (𝓝 0) := by
  have h : ∀ a : ℝ, Tendsto (fun t : ℝ ↦ t / (a ^ 2 + t ^ 2)) atTop (𝓝 0) := fun a ↦ by
    have h₁ : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    refine squeeze_zero_norm' ?_ h₁
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht, abs_of_pos (by positivity),
      div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ ht]
    nlinarith [sq_nonneg a]
  have := ((h (p + 1)).sub (h (p - 1))).div_const 2
  rw [sub_zero, zero_div] at this
  exact this

/-- The column `|p| > 1` of `Δ` has zero mass on the half-line: `∫_0^∞ Δ(p, q) dq = 0`
(Chen and Hou, Part I, (B.55)). -/
theorem integral_Ioi_shearDifference {p : ℝ} (hp : 1 < |p|) :
    ∫ q in Ioi 0, shearDifference p q = 0 := by
  obtain ⟨hp₁, hp₂⟩ := ne_of_one_lt_abs hp
  have hd : ∀ t, HasDerivAt (shearPotential p) (shearDifference p t) t := fun t ↦
    hasDerivAt_shearPotential (by positivity) (by positivity)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
    (fun t _ ↦ hd t) (integrable_shearDifference_right hp 0).1.integrableOn
    (tendsto_shearPotential p)]
  simp [shearPotential]

/-- The vertical map is measurable on each column. -/
theorem measurable_shearMap_right (p : ℝ) : Measurable (shearMap p) := by
  have hP : Measurable fun q ↦ shearMapCoeffP p q := by
    unfold shearMapCoeffP
    fun_prop
  have hQ : Measurable fun q ↦ shearMapCoeffQ p q := by
    unfold shearMapCoeffQ
    fun_prop
  exact (PDE.Analysis.Scalar.measurable_cardanoRoot.comp (hP.prodMk hQ)).sub
    (measurable_id.div_const 3)

/-- The vertical transport cost `∫_{s_c(p)}^∞ |Δ(p, q)| |q - T(p, q)|^{1/2} dq` of the column
`p > 1`, with the map `T` of (B.66) (Chen and Hou, Part I, (B.56)). -/
def shearColumnCost (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ q in Ioi (shearThreshold p),
    ‖shearDifference p q‖ₑ * ENNReal.ofReal (|q - shearMap p q| ^ (1 / 2 : ℝ))

/-- The even fold `g(q) + g(-q)` of a `1/2`-Hölder function on the line is `1/2`-Hölder on
`[0, ∞)` with twice the constant. -/
theorem holderOnWith_add_neg {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderOnWith C (1 / 2) g univ) :
    HolderOnWith (2 * C) (1 / 2) (fun q ↦ g q + g (-q)) (Ici 0) := by
  intro t _ t' _
  calc edist (g t + g (-t)) (g t' + g (-t'))
      ≤ edist (g t) (g t') + edist (g (-t)) (g (-t')) := edist_add_add_le _ _ _ _
    _ ≤ C * edist t t' ^ ((1 / 2 : ℝ≥0) : ℝ) + C * edist (-t) (-t') ^ ((1 / 2 : ℝ≥0) : ℝ) :=
        add_le_add (hg t trivial t' trivial) (hg (-t) trivial (-t') trivial)
    _ = (2 * C : ℝ≥0) * edist t t' ^ ((1 / 2 : ℝ≥0) : ℝ) := by
        rw [edist_neg_neg, ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring

/-- **The column estimate** of Chen and Hou, Part I, Appendix B.2, (B.55) and (B.56). For a column
`p > 1` and `g` `1/2`-Hölder with constant `C` on the line,

`|∫ Δ(p, q) g(q) dq| ≤ 2 C ∫_{s_c(p)}^∞ |Δ(p, q)| |q - T(p, q)|^{1/2} dq`.

The column is even in `q`, so the integral is `∫_0^∞ Δ(p, q) (g(q) + g(-q)) dq`; the half-line
kernel is balanced at `s_c(p)` and `T` matches its outer masses. -/
theorem abs_integral_shearDifference_mul_le_column {p : ℝ} (hp : 1 < p) {g : ℝ → ℝ} {C : ℝ≥0}
    (hg : HolderOnWith C (1 / 2) g univ) :
    ENNReal.ofReal |∫ q, shearDifference p q * g q| ≤ 2 * C * shearColumnCost p := by
  have hp' : 1 < |p| := by rwa [abs_of_pos (by linarith)]
  obtain ⟨hp₁, hp₂⟩ := ne_of_one_lt_abs hp'
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 ≠ 1 := by nlinarith
  set c := shearThreshold p with hc
  have hc0 : 0 < c := shearThreshold_pos hp2
  set κ : ℝ → ℝ := (Ici 0).indicator (shearDifference p) with hκ
  set G : ℝ → ℝ := fun q ↦ g q + g (-q) with hG
  have hGh : HolderOnWith (2 * C) (1 / 2) G (Ici 0) := holderOnWith_add_neg hg
  obtain ⟨hΔi, hΔc⟩ := integrable_shearDifference_right hp' c
  have hκi : Integrable κ := hΔi.indicator measurableSet_Ici
  have hzero : ∫ q, κ q = 0 := by
    rw [hκ, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_Ioi_shearDifference hp']
  have hne : ∀ q, (p - 1) ^ 2 + q ^ 2 ≠ 0 := fun q ↦ by positivity
  have hκneg : ∀ᵐ q, q < c → κ q ≤ 0 := Eventually.of_forall fun q hq ↦ by
    by_cases h : q ∈ Ici 0
    · rw [hκ, indicator_of_mem h]
      refine ((shearDifference_neg_iff hp0 (hne q)).2 ?_).le
      rwa [abs_of_nonneg h]
    · rw [hκ, indicator_of_notMem h]
  have hκpos : ∀ᵐ q, c < q → 0 ≤ κ q := Eventually.of_forall fun q hq ↦ by
    have h : q ∈ Ici 0 := (hc0.trans hq).le
    rw [hκ, indicator_of_mem h]
    refine ((shearDifference_pos_iff hp0 (hne q)).2 ?_).le
    rwa [abs_of_nonneg h]
  have hint : Integrable fun q ↦ κ q * |q - c| ^ ((1 / 2 : ℝ≥0) : ℝ) := by
    refine (hΔc.indicator (measurableSet_Ici (a := 0))).congr (.of_forall fun q ↦ ?_)
    by_cases hq : q ∈ Ici (0 : ℝ)
    · simp [hκ, indicator_of_mem hq]
    · simp [hκ, indicator_of_notMem hq]
  have hTm : Measurable (shearMap p) := measurable_shearMap_right p
  have hTlt : ∀ᵐ q ∂volume.restrict (Ioi c), κ q ≠ 0 → shearMap p q < c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q (hq : c < q) _
    exact shearMap_lt_shearThreshold hp0 hp2 hq
  have hTeq : ∀ᵐ q ∂volume.restrict (Ioi c), κ q ≠ 0 → ∫ x in shearMap p q..q, κ x = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q (hq : c < q) _
    have hq0 : 0 < q := hc0.trans hq
    have hT0 : 0 < shearMap p q := shearMap_pos hq0 hp2
    have hTq : shearMap p q ≤ q := ((shearMap_lt_shearThreshold hp0 hp2 hq).trans hq).le
    rw [intervalIntegral.integral_congr (g := shearDifference p) fun x hx ↦ by
        rw [uIcc_of_le hTq] at hx
        rw [hκ, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hT0.le.trans hx.1)],
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ ↦ hasDerivAt_shearPotential (by positivity) (hne x))
        ((continuous_shearDifference_right hp₁ hp₂).intervalIntegrable _ _),
      shearPotential_shearMap hq0 hp2, sub_self]
  have hmain := abs_integral_mul_le_of_integral_eq_zero hκi hκneg hκpos hzero hint
    hTm.aemeasurable hTlt hTeq (by norm_num) measurableSet_Ici
    (.of_forall fun q hq ↦ by_contra fun h ↦ hq (indicator_of_notMem h _)) hc0.le hGh
  -- the fold
  have hfold : ∫ q, shearDifference p q * g q = ∫ q, κ q * G q := by
    have hgi : Integrable fun q ↦ shearDifference p q * g q := by
      have h1 := integrable_mul_sub_of_holderOnWith (k := shearDifference p) (c := c)
        (by simpa using hΔc) (by norm_num) MeasurableSet.univ
        (Eventually.of_forall fun _ _ ↦ trivial) trivial hg
      refine (h1.add (hΔi.mul_const (g c))).congr (.of_forall fun q ↦ ?_)
      simp only [Pi.add_apply]; ring
    have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hgi
    rw [compl_Ioi] at hsplit
    have hneg : ∫ q in Iic 0, shearDifference p q * g q =
        ∫ q in Ioi 0, shearDifference p q * g (-q) := by
      simpa only [neg_zero, shearDifference_neg_right] using
        (integral_comp_neg_Ioi (0 : ℝ) fun q ↦ shearDifference p q * g q).symm
    have hgi' : IntegrableOn (fun q ↦ shearDifference p q * g (-q)) (Ioi 0) :=
      hgi.comp_neg.integrableOn.congr_fun (fun q _ ↦ by simp only [shearDifference_neg_right])
        measurableSet_Ioi
    rw [← hsplit, hneg, ← integral_add hgi.integrableOn hgi',
      ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume 0] with q hq0
    by_cases hq : 0 < q
    · simp [hκ, hG, indicator_of_mem (show q ∈ Ici (0 : ℝ) from hq.le),
        indicator_of_mem (show q ∈ Ioi (0 : ℝ) from hq), mul_add]
    · have : q < 0 := lt_of_le_of_ne (not_lt.1 hq) hq0
      simp [hκ, indicator_of_notMem (show q ∉ Ici (0 : ℝ) from not_le.2 this),
        indicator_of_notMem (show q ∉ Ioi (0 : ℝ) from not_lt.2 this.le)]
  have hrhs : ∫ y in Ioi c, |κ y| * |y - shearMap p y| ^ ((1 / 2 : ℝ≥0) : ℝ) =
      ∫ y in Ioi c, |shearDifference p y| * |y - shearMap p y| ^ (1 / 2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    rw [hκ, indicator_of_mem (show y ∈ Ici (0 : ℝ) from (hc0.trans hy).le)]
    norm_num
  rw [hrhs, ← hfold] at hmain
  have hnn : 0 ≤ ∫ y in Ioi c, |shearDifference p y| * |y - shearMap p y| ^ (1 / 2 : ℝ) :=
    setIntegral_nonneg measurableSet_Ioi fun y _ ↦ by positivity
  calc ENNReal.ofReal |∫ q, shearDifference p q * g q|
      ≤ ENNReal.ofReal ((2 * C : ℝ≥0) *
          ∫ y in Ioi c, |shearDifference p y| * |y - shearMap p y| ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = (2 * C : ℝ≥0) * ENNReal.ofReal
          (∫ y in Ioi c, |shearDifference p y| * |y - shearMap p y| ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    _ ≤ (2 * C : ℝ≥0) * shearColumnCost p := by
        gcongr
        rw [← abs_of_nonneg hnn, ← Real.enorm_eq_ofReal_abs]
        refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        refine setLIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
        rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ |y - shearMap p y| ^ (1 / 2 : ℝ)),
          Real.enorm_eq_ofReal_abs]
    _ = 2 * C * shearColumnCost p := by rw [ENNReal.coe_mul, ENNReal.coe_ofNat]

end IncompressibleFlow.SharpHolder
