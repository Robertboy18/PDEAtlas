/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainMoments
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainMapBounds
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainTransport
public import PDE.Analysis.Integration.CellSums

/-!
# Cell bounds for the transport cost of the strain estimate

`strainCost s₂ = ∫ s₁, strainCostIntegrand s₂ s₁` with the integrand
`1{s₁ > f(s₂)} |Δ(s₁, s₂)| |T(s₁, s₂) - s₁|^{1/2}`. On a cell `[x₀, x₁] × [z₀, z₁]` lying to the
right of the threshold, `-Δ ≥ 0` and `0 ≤ s₁ - T`, and for an affine majorant `L` of `s₁ - T` and
any `r > 0`, `√(s₁ - T) ≤ (L + r²)/(2r)`. The resulting bound is a corner sum of explicit
primitives (`lintegral_strainCostIntegrand_cell_le`), evaluated through a cross ratio and the unit
shifts of the arctangent primitives (`cornerSum_strainCell_eq`).

## Main definitions

* `strainCostIntegrand`: the integrand of `strainCost`, extended by zero below the threshold.
* `strainCellWeight`: the affine weight `(c₀ - c₁ (x₁ - s₁) - c₂ (s₂ - z₀) + r²)/(2r)`.
* `strainCross`: the cross ratio `((u₀² + z₁²)(u₁² + z₀²)) / ((u₁² + z₁²)(u₀² + z₀²))`.
* `strainShift₁`, `strainShift₂`: the unit shifts of the first- and second-moment primitives.
* `strainStripBound`: the bound of `-Δ` on the strip `[f⁻, f⁺]` along the threshold.

## Main results

* `strainCost_eq`: `M(s₂)` is the lower integral of `strainCostIntegrand s₂` over the line.
* `strainCostIntegrand_le`: for `s₂ > 0`, `s₁ ≥ f(s₂)`, `s₁ - T ≤ L` and `r > 0`, the integrand
  is at most `-Δ(s₁, s₂) (L + r²)/(2r)`.
* `lintegral_strainCostIntegrand_cell_le`: the second-order cell bound, a corner sum of
  `strainCorner` with the weight `strainCellWeight`.
* `cornerSum_strainCell_eq`: the cell corner sum in terms of the cross ratios and the unit shifts.
* `lintegral_strainCostIntegrand_cell_le_const`: the first-order cell bound
  `(φ₀ + r²)/(2r)` times the mass of `-Δ`, allowing the bottom slab `z₀ = 0`.
* `lintegral_strainCostIntegrand_strip_le`: the integral over a strip cell along the threshold is
  at most `(z₁ - z₀)(f⁺ - f⁻) strainStripBound (φ₁ + r²)/(2r)`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-- The integrand of `strainCost`, extended by zero below the threshold. -/
def strainCostIntegrand (s₂ s₁ : ℝ) : ℝ≥0∞ :=
  (Ioi (strainThreshold s₂)).indicator (fun s₁ ↦
    ENNReal.ofReal (|strainDifference s₁ s₂| * |strainMap s₁ s₂ - s₁| ^ (1 / 2 : ℝ))) s₁

/-- The transport cost `M(s₂)` is the lower integral of `strainCostIntegrand s₂` over the line. -/
theorem strainCost_eq (s₂ : ℝ) : strainCost s₂ = ∫⁻ s₁, strainCostIntegrand s₂ s₁ := by
  rw [strainCost, ← lintegral_indicator measurableSet_Ioi]
  rfl

/-- To the right of the threshold, `Δ ≤ 0`. -/
theorem strainDifference_nonpos {s₁ s₂ : ℝ} (hs₂ : 0 < s₂) (h : strainThreshold s₂ ≤ s₁) :
    strainDifference s₁ s₂ ≤ 0 := by
  have hf := strainThreshold_pos s₂
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq, strainDifference_eq hs₂.ne', strainQuartic_strainThreshold, mul_zero, zero_div]
  · exact ((strainDifference_neg_iff (hf.trans hlt).le hs₂).2 hlt).le

/-- To the right of the threshold, `T ≤ s₁`. -/
theorem strainMap_le_self {s₁ s₂ : ℝ} (hs₂ : 0 < s₂) (h : strainThreshold s₂ ≤ s₁) :
    strainMap s₁ s₂ ≤ s₁ := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq, strainMap_strainThreshold hs₂.ne']
  · exact ((strainMap_lt_strainThreshold hs₂ hlt).trans hlt).le

/-- `√φ ≤ (φ + r²)/(2r)` for `φ ≥ 0`, `r > 0`. -/
theorem sqrt_le_tangent {φ r : ℝ} (hφ : 0 ≤ φ) (hr : 0 < r) :
    φ ^ (1 / 2 : ℝ) ≤ (φ + r ^ 2) / (2 * r) := by
  rw [← Real.sqrt_eq_rpow, le_div_iff₀ (by positivity)]
  have h := Real.sq_sqrt hφ
  nlinarith [sq_nonneg (Real.sqrt φ - r)]

/-- **The pointwise bound.** For `s₂ > 0`, `s₁ ≥ f(s₂)`, `s₁ - T ≤ L` and `r > 0`:
`strainCostIntegrand s₂ s₁ ≤ -Δ(s₁, s₂) (L + r²)/(2r)`. -/
theorem strainCostIntegrand_le {s₁ s₂ L r : ℝ} (hs₂ : 0 < s₂) (h : strainThreshold s₂ ≤ s₁)
    (hL : s₁ - strainMap s₁ s₂ ≤ L) (hr : 0 < r) :
    strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (-strainDifference s₁ s₂ * ((L + r ^ 2) / (2 * r))) := by
  unfold strainCostIntegrand
  by_cases hs : s₁ ∈ Ioi (strainThreshold s₂)
  · rw [indicator_of_mem hs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hΔ := strainDifference_nonpos hs₂ h
    have hT := strainMap_le_self hs₂ h
    rw [abs_of_nonpos hΔ, abs_of_nonpos (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc (-(strainMap s₁ s₂ - s₁)) ^ (1 / 2 : ℝ) ≤ (-(strainMap s₁ s₂ - s₁) + r ^ 2) / (2 * r) :=
          sqrt_le_tangent (by linarith) hr
      _ ≤ (L + r ^ 2) / (2 * r) := by gcongr; linarith
  · rw [indicator_of_notMem hs]
    exact zero_le

/-- The affine weight `(c₀ - c₁ (x₁ - s₁) - c₂ (s₂ - z₀) + r²)/(2r)` as `p₀ + p₁ s₁ + p₂ s₂`. -/
def strainCellWeight (x₁ z₀ c₀ c₁ c₂ r : ℝ) : ℝ × ℝ × ℝ :=
  ((c₀ + r ^ 2 - c₁ * x₁ + c₂ * z₀) / (2 * r), c₁ / (2 * r), -c₂ / (2 * r))

/-- **The second-order cell bound.** If the cell `[x₀, x₁] × [z₀, z₁]`, `z₀ > 0`, lies
to the right of the threshold and `s₁ - T ≤ c₀ - c₁ (x₁ - s₁) - c₂ (s₂ - z₀)` on it, then for
`r > 0` the cell integral is at most the corner sum of the primitives with the weight
`strainCellWeight`. -/
theorem lintegral_strainCostIntegrand_cell_le {x₀ x₁ z₀ z₁ c₀ c₁ c₂ r : ℝ}
    (hx : x₀ ≤ x₁) (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) (hfull : strainThreshold z₁ ≤ x₀)
    (hL : ∀ s₁ ∈ Icc x₀ x₁, ∀ s₂ ∈ Icc z₀ z₁,
      s₁ - strainMap s₁ s₂ ≤ c₀ - c₁ * (x₁ - s₁) - c₂ * (s₂ - z₀))
    (hr : 0 < r) :
    ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (cornerSum (fun s₁ z ↦
        strainCorner ((strainCellWeight x₁ z₀ c₀ c₁ c₂ r).1 +
            (strainCellWeight x₁ z₀ c₀ c₁ c₂ r).2.1 / 2)
          (strainCellWeight x₁ z₀ c₀ c₁ c₂ r).2.1 (strainCellWeight x₁ z₀ c₀ c₁ c₂ r).2.2
          (s₁ - 1 / 2) z -
        strainCorner ((strainCellWeight x₁ z₀ c₀ c₁ c₂ r).1 -
            (strainCellWeight x₁ z₀ c₀ c₁ c₂ r).2.1 / 2)
          (strainCellWeight x₁ z₀ c₀ c₁ c₂ r).2.1 (strainCellWeight x₁ z₀ c₀ c₁ c₂ r).2.2
          (s₁ + 1 / 2) z) x₀ x₁ z₀ z₁) := by
  set p := strainCellWeight x₁ z₀ c₀ c₁ c₂ r
  have hP : ∀ s₁ s₂ : ℝ, p.1 + p.2.1 * s₁ + p.2.2 * s₂ =
      (c₀ - c₁ * (x₁ - s₁) - c₂ * (s₂ - z₀) + r ^ 2) / (2 * r) := by
    intro s₁ s₂
    simp only [p, strainCellWeight]
    field_simp
    ring
  have hthr : ∀ s₂ ∈ Icc z₀ z₁, ∀ s₁ ∈ Icc x₀ x₁, strainThreshold s₂ ≤ s₁ := fun s₂ hs₂ s₁ hs₁ ↦
    (monotoneOn_strainThreshold (show s₂ ∈ Ici 0 from (hz₀.trans_le hs₂.1).le)
      (show z₁ ∈ Ici 0 from (hz₀.trans_le hz).le) hs₂.2).trans (hfull.trans hs₁.1)
  calc ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, strainCostIntegrand s₂ s₁
      ≤ ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁,
          ENNReal.ofReal (-strainDifference s₁ s₂ * (p.1 + p.2.1 * s₁ + p.2.2 * s₂)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s₂ hs₂ ↦ ?_
        refine setLIntegral_mono' measurableSet_Ioc fun s₁ hs₁ ↦ ?_
        have hs₂' := Ioc_subset_Icc_self hs₂
        have hs₁' := Ioc_subset_Icc_self hs₁
        rw [hP]
        exact strainCostIntegrand_le (hz₀.trans hs₂.1) (hthr s₂ hs₂' s₁ hs₁')
          (hL s₁ hs₁' s₂ hs₂') hr
    _ = ENNReal.ofReal (∫ s₂ in z₀..z₁, ∫ s₁ in x₀..x₁,
          -strainDifference s₁ s₂ * (p.1 + p.2.1 * s₁ + p.2.2 * s₂)) := by
        refine lintegral_lintegral_ofReal_eq hx hz ?_ fun s₁ hs₁ s₂ hs₂ ↦ ?_
        · refine ContinuousOn.mul ?_ (by fun_prop)
          simp only [strainDifference, strainDensity_eq]
          refine ContinuousOn.neg (ContinuousOn.sub ?_ ?_)
          · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
              have : 0 < q.2 := hz₀.trans_le hq.2.1
              positivity
          · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
              have : 0 < q.2 := hz₀.trans_le hq.2.1
              positivity
        · have hs₂0 : 0 < s₂ := hz₀.trans_le hs₂.1
          have hΔ := strainDifference_nonpos hs₂0 (hthr s₂ hs₂ s₁ hs₁)
          have hT := strainMap_le_self hs₂0 (hthr s₂ hs₂ s₁ hs₁)
          rw [hP]
          refine mul_nonneg (by linarith) (div_nonneg ?_ (by positivity))
          have := hL s₁ hs₁ s₂ hs₂
          nlinarith [sq_nonneg r]
    _ = _ := by
        rw [integral_integral_neg_strainDifference_affine p.1 p.2.1 p.2.2 hz₀ hz]

/-! ### Evaluation of the corner sum -/

/-- The cross ratio `((u₀² + z₁²)(u₁² + z₀²)) / ((u₁² + z₁²)(u₀² + z₀²))` of a rectangle. -/
def strainCross (u₀ u₁ z₀ z₁ : ℝ) : ℝ :=
  (u₀ ^ 2 + z₁ ^ 2) * (u₁ ^ 2 + z₀ ^ 2) / ((u₁ ^ 2 + z₁ ^ 2) * (u₀ ^ 2 + z₀ ^ 2))

/-- The unit shift `(z/2) arctan (z / (z² + u (u + 1)))` of the first-moment primitive. -/
def strainShift₁ (u z : ℝ) : ℝ := z / 2 * Real.arctan (z / (z ^ 2 + u * (u + 1)))

/-- The unit shift `((u + 1)/2) arctan (z/(u + 1)) - (u/2) arctan (z/u)` of the second-moment
primitive. -/
def strainShift₂ (u z : ℝ) : ℝ :=
  (u + 1) / 2 * Real.arctan (z / (u + 1)) - u / 2 * Real.arctan (z / u)

/-- **The cell corner sum** in terms of the cross ratios and the unit shifts. -/
theorem cornerSum_strainCell_eq (p₀ p₁ p₂ : ℝ) {x₀ x₁ z₀ z₁ : ℝ} (hx₀ : 1 / 2 < x₀)
    (hx : x₀ ≤ x₁) (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) :
    cornerSum (fun s₁ z ↦ strainCorner (p₀ + p₁ / 2) p₁ p₂ (s₁ - 1 / 2) z -
        strainCorner (p₀ - p₁ / 2) p₁ p₂ (s₁ + 1 / 2) z) x₀ x₁ z₀ z₁ =
      (p₀ + p₁ / 2) * (Real.log (strainCross (x₀ - 1 / 2) (x₁ - 1 / 2) z₀ z₁ /
          strainCross (x₀ + 1 / 2) (x₁ + 1 / 2) z₀ z₁) / 4) +
        p₁ * (Real.log (strainCross (x₀ + 1 / 2) (x₁ + 1 / 2) z₀ z₁) / 4 -
          cornerSum (fun s₁ z ↦ strainShift₁ (s₁ - 1 / 2) z) x₀ x₁ z₀ z₁) -
        p₂ * cornerSum (fun s₁ z ↦ strainShift₂ (s₁ - 1 / 2) z) x₀ x₁ z₀ z₁ := by
  have ha : 0 < x₀ - 1 / 2 := by linarith
  have hb : 0 < x₀ + 1 / 2 := by linarith
  have hA := cornerSum_strainLog_eq (z₀ := z₀) (z₁ := z₁) ha (by linarith : x₀ - 1 / 2 ≤ x₁ - 1 / 2)
  have hB := cornerSum_strainLog_eq (z₀ := z₀) (z₁ := z₁) hb (by linarith : x₀ + 1 / 2 ≤ x₁ + 1 / 2)
  have hcr₀ : 0 < strainCross (x₀ - 1 / 2) (x₁ - 1 / 2) z₀ z₁ := by
    unfold strainCross
    have : 0 < x₁ - 1 / 2 := by linarith
    positivity
  have hcr₁ : 0 < strainCross (x₀ + 1 / 2) (x₁ + 1 / 2) z₀ z₁ := by
    unfold strainCross
    have : 0 < x₁ + 1 / 2 := by linarith
    positivity
  have hsh : ∀ s₁ ∈ ({x₀, x₁} : Set ℝ), ∀ z ∈ ({z₀, z₁} : Set ℝ),
      z / 2 * Real.arctan ((s₁ - 1 / 2) / z) - z / 2 * Real.arctan ((s₁ + 1 / 2) / z) =
        -(z / 2 * Real.arctan (z / (z ^ 2 + (s₁ - 1 / 2) * (s₁ + 1 / 2)))) := by
    intro s₁ hs₁ z hz'
    have hs : 0 ≤ s₁ - 1 / 2 := by
      rcases hs₁ with h | h <;> (rw [h]; linarith)
    have hz0 : 0 < z := by
      rcases hz' with h | h <;> (rw [h]; linarith)
    have := strainShift₁_eq hs hz0
    rw [show s₁ - 1 / 2 + 1 = s₁ + 1 / 2 by ring] at this
    linarith
  rw [Real.log_div hcr₀.ne' hcr₁.ne']
  unfold strainCross at hA hB ⊢
  simp only [cornerSum, strainCorner, strainShift₂] at hA hB ⊢
  have e₁ := hsh x₁ (by simp) z₁ (by simp)
  have e₂ := hsh x₀ (by simp) z₁ (by simp)
  have e₃ := hsh x₁ (by simp) z₀ (by simp)
  have e₄ := hsh x₀ (by simp) z₀ (by simp)
  simp only [strainShift₁]
  rw [show x₁ - 1 / 2 + 1 = x₁ + 1 / 2 by ring, show x₀ - 1 / 2 + 1 = x₀ + 1 / 2 by ring]
  linear_combination (p₀ + p₁ / 2) * hA - (p₀ - p₁ / 2) * hB + p₁ * e₁ - p₁ * e₂ - p₁ * e₃ + p₁ * e₄

/-! ### First-order cells on the bottom slab and the strip along the threshold -/

/-- The mass of the difference kernel over a cell, for `x₀ > 1/2` and any `z₀ ≤ z₁`. -/
theorem integral_integral_neg_strainDifference {x₀ x₁ z₀ z₁ : ℝ} (hx₀ : 1 / 2 < x₀)
    (hx : x₀ ≤ x₁) :
    ∫ z in z₀..z₁, ∫ s₁ in x₀..x₁, -strainDifference s₁ z =
      Real.log (strainCross (x₀ - 1 / 2) (x₁ - 1 / 2) z₀ z₁ /
        strainCross (x₀ + 1 / 2) (x₁ + 1 / 2) z₀ z₁) / 4 := by
  have ha : 0 < x₀ - 1 / 2 := by linarith
  have hb : 0 < x₀ + 1 / 2 := by linarith
  have hu : ∀ s₁ ∈ uIcc x₀ x₁, 0 < s₁ - 1 / 2 := fun s₁ hs ↦ by
    rw [uIcc_of_le hx] at hs; linarith [hs.1]
  have hFTC : ∫ z in z₀..z₁, ∫ s₁ in x₀..x₁, -strainDifference s₁ z =
      cornerSum (fun s₁ z ↦ -Real.log ((s₁ - 1 / 2) ^ 2 + z ^ 2) / 4 +
        Real.log ((s₁ + 1 / 2) ^ 2 + z ^ 2) / 4) x₀ x₁ z₀ z₁ := by
    refine integral_integral_eq_cornerSum_swap
      (k₁ := fun s₁ z ↦ -z / (2 * ((s₁ - 1 / 2) ^ 2 + z ^ 2)) +
        z / (2 * ((s₁ + 1 / 2) ^ 2 + z ^ 2)))
      (fun z _ s₁ hs₁ ↦ ?_) (fun z _ ↦ ?_) (fun z _ ↦ ?_) (fun z _ ↦ ?_) ?_ ?_
    · have h₁ := hu s₁ hs₁
      have p₁ : 0 < (s₁ - 1 / 2) ^ 2 + z ^ 2 := by positivity
      have p₂ : 0 < (s₁ + 1 / 2) ^ 2 + z ^ 2 := by nlinarith
      have d₁ : HasDerivAt (fun s ↦ 2 * ((s - 1 / 2) ^ 2 + z ^ 2))
          (2 * (2 * (s₁ - 1 / 2))) s₁ := by
        have := ((((hasDerivAt_id' s₁).sub_const (1 / 2)).pow 2).add_const (z ^ 2)).const_mul 2
        simpa using this
      have d₂ : HasDerivAt (fun s ↦ 2 * ((s + 1 / 2) ^ 2 + z ^ 2))
          (2 * (2 * (s₁ + 1 / 2))) s₁ := by
        have := ((((hasDerivAt_id' s₁).add_const (1 / 2)).pow 2).add_const (z ^ 2)).const_mul 2
        simpa using this
      refine (((hasDerivAt_const s₁ (-z)).div d₁ (by positivity)).add
        ((hasDerivAt_const s₁ z).div d₂ (by positivity))).congr_deriv ?_
      simp only [strainDifference, strainDensity_eq]
      field_simp
      ring
    · refine ContinuousOn.intervalIntegrable ?_
      simp only [strainDifference, strainDensity_eq]
      refine ContinuousOn.neg (ContinuousOn.sub ?_ ?_)
      · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun s₁ hs₁ ↦ by
          have : 0 < s₁ + 1 / 2 := by linarith [hu s₁ hs₁]
          exact pow_ne_zero 2 (add_pos_of_pos_of_nonneg (pow_pos this 2) (sq_nonneg _)).ne'
      · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun s₁ hs₁ ↦ by
          have := hu s₁ hs₁
          exact pow_ne_zero 2 (add_pos_of_pos_of_nonneg (pow_pos this 2) (sq_nonneg _)).ne'
    · have p₁ : 0 < (x₀ - 1 / 2) ^ 2 + z ^ 2 := by positivity
      have p₂ : 0 < (x₀ + 1 / 2) ^ 2 + z ^ 2 := by positivity
      have e₁ : HasDerivAt (fun z ↦ (x₀ - 1 / 2) ^ 2 + z ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z).const_add ((x₀ - 1 / 2) ^ 2)
      have e₂ : HasDerivAt (fun z ↦ (x₀ + 1 / 2) ^ 2 + z ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z).const_add ((x₀ + 1 / 2) ^ 2)
      refine (((e₁.log p₁.ne').neg.div_const 4).add ((e₂.log p₂.ne').div_const 4)).congr_deriv ?_
      field_simp
      ring
    · have hb₁ : 0 < x₁ - 1 / 2 := by linarith
      have p₁ : 0 < (x₁ - 1 / 2) ^ 2 + z ^ 2 := by positivity
      have p₂ : 0 < (x₁ + 1 / 2) ^ 2 + z ^ 2 := by nlinarith
      have e₁ : HasDerivAt (fun z ↦ (x₁ - 1 / 2) ^ 2 + z ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z).const_add ((x₁ - 1 / 2) ^ 2)
      have e₂ : HasDerivAt (fun z ↦ (x₁ + 1 / 2) ^ 2 + z ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z).const_add ((x₁ + 1 / 2) ^ 2)
      refine (((e₁.log p₁.ne').neg.div_const 4).add ((e₂.log p₂.ne').div_const 4)).congr_deriv ?_
      field_simp
      ring
    · exact (Continuous.add (Continuous.div (by fun_prop) (by fun_prop) fun z ↦ by
        have : 0 < (x₀ - 1 / 2) ^ 2 + z ^ 2 := by positivity
        positivity) (Continuous.div (by fun_prop) (by fun_prop) fun z ↦ by
        have : 0 < (x₀ + 1 / 2) ^ 2 + z ^ 2 := by positivity
        positivity)).intervalIntegrable _ _
    · have hb₁ : 0 < x₁ - 1 / 2 := by linarith
      exact (Continuous.add (Continuous.div (by fun_prop) (by fun_prop) fun z ↦ by
        have : 0 < (x₁ - 1 / 2) ^ 2 + z ^ 2 := by positivity
        positivity) (Continuous.div (by fun_prop) (by fun_prop) fun z ↦ by
        have : 0 < (x₁ + 1 / 2) ^ 2 + z ^ 2 := by nlinarith
        positivity)).intervalIntegrable _ _
  rw [hFTC]
  have hcr₀ : 0 < strainCross (x₀ - 1 / 2) (x₁ - 1 / 2) z₀ z₁ := by
    unfold strainCross; have : 0 < x₁ - 1 / 2 := by linarith
    positivity
  have hcr₁ : 0 < strainCross (x₀ + 1 / 2) (x₁ + 1 / 2) z₀ z₁ := by
    unfold strainCross; have : 0 < x₁ + 1 / 2 := by linarith
    positivity
  have hA := cornerSum_strainLog_eq (z₀ := z₀) (z₁ := z₁) ha (by linarith :
    x₀ - 1 / 2 ≤ x₁ - 1 / 2)
  have hB := cornerSum_strainLog_eq (z₀ := z₀) (z₁ := z₁) hb (by linarith :
    x₀ + 1 / 2 ≤ x₁ + 1 / 2)
  rw [Real.log_div hcr₀.ne' hcr₁.ne']
  unfold strainCross
  simp only [cornerSum] at hA hB ⊢
  linear_combination hA - hB

/-- **The first-order cell bound**, allowing the bottom slab `z₀ = 0`: if `s₁ - T ≤ φ₀` on the cell
(for `s₂ > 0`) and the cell lies to the right of the threshold, then for `r > 0` the cell
integral is at most `(φ₀ + r²)/(2r)` times the mass `(1/4) log (cr₀ / cr₁)`. -/
theorem lintegral_strainCostIntegrand_cell_le_const {x₀ x₁ z₀ z₁ φ₀ r : ℝ} (hx₀ : 1 / 2 < x₀)
    (hx : x₀ ≤ x₁) (hz₀ : 0 ≤ z₀) (hz : z₀ ≤ z₁) (hfull : strainThreshold z₁ ≤ x₀)
    (hφ : ∀ s₁ ∈ Icc x₀ x₁, ∀ s₂ ∈ Ioc z₀ z₁, s₁ - strainMap s₁ s₂ ≤ φ₀) (hφ₀ : 0 ≤ φ₀)
    (hr : 0 < r) :
    ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal ((φ₀ + r ^ 2) / (2 * r) *
        (Real.log (strainCross (x₀ - 1 / 2) (x₁ - 1 / 2) z₀ z₁ /
          strainCross (x₀ + 1 / 2) (x₁ + 1 / 2) z₀ z₁) / 4)) := by
  have hthr : ∀ s₂ ∈ Icc z₀ z₁, ∀ s₁ ∈ Icc x₀ x₁, strainThreshold s₂ ≤ s₁ := fun s₂ hs₂ s₁ hs₁ ↦
    (monotoneOn_strainThreshold (show s₂ ∈ Ici 0 from hz₀.trans hs₂.1)
      (show z₁ ∈ Ici 0 from hz₀.trans hz) hs₂.2).trans (hfull.trans hs₁.1)
  have hφ0 : 0 ≤ φ₀ + r ^ 2 := by positivity
  set c := (φ₀ + r ^ 2) / (2 * r)
  have hc : 0 ≤ c := div_nonneg hφ0 (by positivity)
  have hΔ0 : ∀ s₁ ∈ Icc x₀ x₁, ∀ s₂ ∈ Icc z₀ z₁, 0 ≤ -strainDifference s₁ s₂ := by
    intro s₁ hs₁ s₂ hs₂
    rcases eq_or_lt_of_le (hz₀.trans hs₂.1) with h | h
    · rw [← h]
      simp [strainDifference, strainDensity_eq]
    · linarith [strainDifference_nonpos h (hthr s₂ hs₂ s₁ hs₁)]
  calc ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, strainCostIntegrand s₂ s₁
      ≤ ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, ENNReal.ofReal (-strainDifference s₁ s₂ * c) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s₂ hs₂ ↦ ?_
        refine setLIntegral_mono' measurableSet_Ioc fun s₁ hs₁ ↦ ?_
        have hs₁' := Ioc_subset_Icc_self hs₁
        exact strainCostIntegrand_le (hz₀.trans_lt hs₂.1) (hthr s₂ (Ioc_subset_Icc_self hs₂) s₁
          hs₁') (hφ s₁ hs₁' s₂ hs₂) hr
    _ = ENNReal.ofReal (∫ s₂ in z₀..z₁, ∫ s₁ in x₀..x₁, -strainDifference s₁ s₂ * c) := by
        refine lintegral_lintegral_ofReal_eq hx hz ?_ fun s₁ hs₁ s₂ hs₂ ↦
          mul_nonneg (hΔ0 s₁ hs₁ s₂ hs₂) hc
        refine ContinuousOn.mul ?_ continuousOn_const
        simp only [strainDifference, strainDensity_eq]
        refine ContinuousOn.neg (ContinuousOn.sub ?_ ?_)
        · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
            have : 0 < q.1 + 1 / 2 := by linarith [hq.1.1]
            exact pow_ne_zero 2 (add_pos_of_pos_of_nonneg (pow_pos this 2) (sq_nonneg _)).ne'
        · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
            have : 0 < q.1 - 1 / 2 := by linarith [hq.1.1]
            exact pow_ne_zero 2 (add_pos_of_pos_of_nonneg (pow_pos this 2) (sq_nonneg _)).ne'
    _ = _ := by
        rw [show (∫ s₂ in z₀..z₁, ∫ s₁ in x₀..x₁, -strainDifference s₁ s₂ * c) =
            (∫ s₂ in z₀..z₁, ∫ s₁ in x₀..x₁, -strainDifference s₁ s₂) * c by
          simp only [intervalIntegral.integral_mul_const],
          integral_integral_neg_strainDifference hx₀ hx, mul_comm]

/-- On the strip `[f⁻, f⁺]` along the threshold, `-Δ ≤ z₁ · 3 (f⁺² - f⁻²)(f⁺² + z₁² + 1/12) /
(((f⁻ + 1/2)² + z₀²)² ((f⁻ - 1/2)² + z₀²)²)` where `s₁ ≥ f(s₂)`. -/
theorem neg_strainDifference_le_strip {fl fu z₀ z₁ s₁ s₂ : ℝ} (hfl : 1 / 2 ≤ fl)
    (hz₀ : 0 < z₀) (hs₁ : s₁ ∈ Icc fl fu) (hs₂ : s₂ ∈ Icc z₀ z₁) (hfl₀ : fl ≤ strainThreshold s₂)
    (h : strainThreshold s₂ ≤ s₁) :
    -strainDifference s₁ s₂ ≤
      z₁ * (3 * (fu ^ 2 - fl ^ 2) * (fu ^ 2 + z₁ ^ 2 + 1 / 12)) /
        (((fl + 1 / 2) ^ 2 + z₀ ^ 2) ^ 2 * ((fl - 1 / 2) ^ 2 + z₀ ^ 2) ^ 2) := by
  have hs₂0 : 0 < s₂ := hz₀.trans_le hs₂.1
  have hf := strainThreshold_nonneg s₂
  have hsq : Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1) ≤ 4 * s₂ ^ 2 + 1 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg s₂]⟩
  have hsq0 := Real.sqrt_nonneg (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1)
  rw [strainDifference_eq hs₂0.ne', strainQuartic_eq]
  generalize Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1) = q at hsq hsq0 ⊢
  set f := strainThreshold s₂
  have hs₁0 : 0 ≤ s₁ := by linarith [hs₁.1]
  have hA : 0 ≤ s₁ ^ 2 - f ^ 2 := by nlinarith
  have hA' : s₁ ^ 2 - f ^ 2 ≤ fu ^ 2 - fl ^ 2 := by nlinarith [hs₁.2]
  have hB : 0 ≤ s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - q) / 6 := by nlinarith [sq_nonneg s₁]
  have hB' : s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - q) / 6 ≤ fu ^ 2 + z₁ ^ 2 + 1 / 12 := by
    nlinarith [hs₁.2, hs₂.2]
  have hDp : ((fl + 1 / 2) ^ 2 + z₀ ^ 2) ^ 2 * ((fl - 1 / 2) ^ 2 + z₀ ^ 2) ^ 2 ≤
      ((s₁ + 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 := by
    have hz2 : z₀ ^ 2 ≤ s₂ ^ 2 := pow_le_pow_left₀ hz₀.le hs₂.1 2
    have h₁ : (fl + 1 / 2) ^ 2 + z₀ ^ 2 ≤ (s₁ + 1 / 2) ^ 2 + s₂ ^ 2 :=
      add_le_add (pow_le_pow_left₀ (by linarith) (by linarith [hs₁.1]) 2) hz2
    have h₂ : (fl - 1 / 2) ^ 2 + z₀ ^ 2 ≤ (s₁ - 1 / 2) ^ 2 + s₂ ^ 2 :=
      add_le_add (pow_le_pow_left₀ (by linarith) (by linarith [hs₁.1]) 2) hz2
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h₁ 2) (pow_le_pow_left₀ (by positivity) h₂ 2)
      (by positivity) (by positivity)
  have e : -(s₂ * (-3 * (s₁ ^ 2 - f ^ 2) * (s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - q) / 6)) /
      (((s₁ + 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2)) =
      s₂ * (3 * (s₁ ^ 2 - f ^ 2) * (s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - q) / 6)) /
        (((s₁ + 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2) := by ring
  rw [e]
  have hz₁ : 0 ≤ z₁ := by linarith [hs₂.1, hs₂.2]
  have hff : 0 ≤ fu ^ 2 - fl ^ 2 := by nlinarith [hs₁.1, hs₁.2]
  refine div_le_div₀ (by positivity) ?_ (by positivity) hDp
  refine mul_le_mul hs₂.2 ?_ (by positivity) hz₁
  exact mul_le_mul (by linarith) hB' hB (by nlinarith)

/-- The bound of `-Δ` on the strip,
`z₁ · 3 (f⁺² - f⁻²)(f⁺² + z₁² + 1/12) / (((f⁻ + 1/2)² + z₀²)² ((f⁻ - 1/2)² + z₀²)²)`. -/
def strainStripBound (fl fu z₀ z₁ : ℝ) : ℝ :=
  z₁ * (3 * (fu ^ 2 - fl ^ 2) * (fu ^ 2 + z₁ ^ 2 + 1 / 12)) /
    (((fl + 1 / 2) ^ 2 + z₀ ^ 2) ^ 2 * ((fl - 1 / 2) ^ 2 + z₀ ^ 2) ^ 2)

/-- `s₁ - T(s₁, s₂) ≤ f⁺ - T(f⁺, z₀)` for `0 < s₁ ≤ f⁺` and `s₂ ≥ z₀ > 0`. -/
theorem sub_strainMap_le_corner {s₁ s₂ fu z₀ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ fu) (hz₀ : 0 < z₀)
    (hs₂ : z₀ ≤ s₂) : s₁ - strainMap s₁ s₂ ≤ fu - strainMap fu z₀ := by
  have hs₂0 : 0 < s₂ := hz₀.trans_le hs₂
  have h₁ : strainMap fu s₂ ≤ strainMap s₁ s₂ :=
    (strictAntiOn_strainMap hs₂0).antitoneOn hs₁ (hs₁.trans_le hs) hs
  have h₂ : strainMap fu z₀ ≤ strainMap fu s₂ :=
    monotoneOn_strainMap_right (hs₁.trans_le hs) hz₀ hs₂0 hs₂
  linarith

/-- **The strip cell.** For `1/2 ≤ f⁻ ≤ f(z₀)`, `z₀ > 0`, `s₁ - T ≤ φ₁` on `[f⁻, f⁺] × [z₀, z₁]`
and `r > 0`, the integral over the strip is at most
`(z₁ - z₀)(f⁺ - f⁻) strainStripBound (φ₁ + r²)/(2r)`. -/
theorem lintegral_strainCostIntegrand_strip_le {fl fu z₀ z₁ φ₁ r : ℝ} (hfl : 1 / 2 ≤ fl)
    (hf : fl ≤ fu) (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) (hfl₀ : fl ≤ strainThreshold z₀)
    (hφ : ∀ s₁ ∈ Icc fl fu, ∀ s₂ ∈ Icc z₀ z₁, s₁ - strainMap s₁ s₂ ≤ φ₁) (hφ₁ : 0 ≤ φ₁)
    (hr : 0 < r) :
    ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc fl fu, strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal ((z₁ - z₀) * ((fu - fl) *
        (strainStripBound fl fu z₀ z₁ * ((φ₁ + r ^ 2) / (2 * r))))) := by
  set c := strainStripBound fl fu z₀ z₁ * ((φ₁ + r ^ 2) / (2 * r))
  have hpt : ∀ s₂ ∈ Ioc z₀ z₁, ∀ s₁ ∈ Ioc fl fu, strainCostIntegrand s₂ s₁ ≤ ENNReal.ofReal c := by
    intro s₂ hs₂ s₁ hs₁
    have hs₂' := Ioc_subset_Icc_self hs₂
    have hs₁' := Ioc_subset_Icc_self hs₁
    have hs₂0 : 0 < s₂ := hz₀.trans hs₂.1
    have hf₀ : fl ≤ strainThreshold s₂ := hfl₀.trans (monotoneOn_strainThreshold
      (show z₀ ∈ Ici 0 from hz₀.le) (show s₂ ∈ Ici 0 from hs₂0.le) hs₂.1.le)
    by_cases hs : strainThreshold s₂ ≤ s₁
    · refine (strainCostIntegrand_le hs₂0 hs (hφ s₁ hs₁' s₂ hs₂') hr).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hφ0 : 0 ≤ φ₁ + r ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (neg_strainDifference_le_strip hfl hz₀ hs₁' hs₂' hf₀ hs)
        (div_nonneg hφ0 (by positivity))
    · unfold strainCostIntegrand
      rw [indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact (not_le.1 hs).le)]
      exact zero_le
  calc ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc fl fu, strainCostIntegrand s₂ s₁
      ≤ ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc fl fu, ENNReal.ofReal c :=
        setLIntegral_mono' measurableSet_Ioc fun s₂ hs₂ ↦
          setLIntegral_mono' measurableSet_Ioc fun s₁ hs₁ ↦ hpt s₂ hs₂ s₁ hs₁
    _ = ENNReal.ofReal (z₁ - z₀) * (ENNReal.ofReal (fu - fl) * ENNReal.ofReal c) := by
        simp only [setLIntegral_const, Real.volume_Ioc]
        ring
    _ = ENNReal.ofReal ((z₁ - z₀) * ((fu - fl) * c)) := by
        have hc : 0 ≤ c := by
          have : 0 ≤ strainStripBound fl fu z₀ z₁ := by
            unfold strainStripBound
            have : 0 ≤ fu ^ 2 - fl ^ 2 := by nlinarith
            have : 0 ≤ z₁ := by linarith
            positivity
          exact mul_nonneg this (div_nonneg (by positivity) (by positivity))
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith)]

end IncompressibleFlow.SharpHolder
