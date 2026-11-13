/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMapBounds
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMoments
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearVertical
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainCostCells

/-!
# Cell bounds of the vertical transport cost of the shear estimates

The column cost `∫_{s_c(p)}^∞ |Δ(p, t)| |t - T(p, t)|^{1/2} dt` of `shearColumnCost` is the
lintegral of `shearColumnDensity p`, the density extended by zero below the threshold. On a
rectangle where the sign quartic is `≤ 0`, `Δ ≥ 0` and `T ≤ t`, so the tangent bound
`√(t - T) ≤ (t - T + r²)/(2r)` and an affine majorant `α + β p + γ t` of the right side turn the
cell into the corner sum of `integral_integral_shearDifference_affine`. A rectangle crossing the
threshold is bounded by its area times a bound of the density, and where the quartic is `≥ 0`
the density vanishes.

## Main definitions

* `shearColumnDensity`: the transport density `|Δ(p, t)| |t - T(p, t)|^{1/2}` of the column `p`,
  extended by zero for `t ≤ s_c(p)`.

## Main results

* `shearColumnCost_eq`: the column cost is the lintegral of the column density over `t > 0`.
* `shearColumnDensity_eq_zero`: where the sign quartic is `≥ 0`, the density vanishes.
* `shearColumnDensity_le`: where `Q(p, t) ≤ 0` and `(t - T + r²)/(2r) ≤ α + β p + γ t`, the
  density is at most `Δ (α + β p + γ t)`.
* `lintegral_shearColumnDensity_cell_le`: on a cell `[p₀, p₁] × [t₀, t₁]` where the sign quartic
  is `≤ 0`, the cell integral is at most the corner sum of
  `integral_integral_shearDifference_affine`.
* `lintegral_shearColumnDensity_strip_le`: if `|Δ| ≤ D` and `|t - T| ≤ φ` above the threshold,
  the cell integral is at most `(p₁ - p₀)(t₁ - t₀) D √φ`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-- The transport density `|Δ(p, t)| |t - T(p, t)|^{1/2}` of the column `p`, extended by zero for
`t ≤ s_c(p)`. -/
def shearColumnDensity (p t : ℝ) : ℝ≥0∞ :=
  (Ioi (shearThreshold p)).indicator (fun t ↦ ‖shearDifference p t‖ₑ *
    ENNReal.ofReal (|t - shearMap p t| ^ (1 / 2 : ℝ))) t

/-- The column cost is the lower integral of the column density over `t > 0`. -/
theorem shearColumnCost_eq (p : ℝ) :
    shearColumnCost p = ∫⁻ t in Ioi 0, shearColumnDensity p t := by
  have hs : 0 ≤ shearThreshold p := Real.sqrt_nonneg _
  unfold shearColumnDensity
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.2 (Ioi_subset_Ioi hs)]
  rfl

/-- The column density is jointly measurable in `(p, t)`. -/
theorem measurable_shearColumnDensity :
    Measurable fun x : ℝ × ℝ ↦ shearColumnDensity x.1 x.2 := by
  have hs : Measurable fun p : ℝ ↦ shearThreshold p := by
    unfold shearThreshold
    fun_prop
  have hF : Measurable fun x : ℝ × ℝ ↦ ‖shearDifference x.1 x.2‖ₑ *
      ENNReal.ofReal (|x.2 - shearMap x.1 x.2| ^ (1 / 2 : ℝ)) :=
    measurable_shearDifference.enorm.mul
      ((continuous_abs.measurable.comp (measurable_snd.sub measurable_shearMap)).pow_const
        _).ennreal_ofReal
  have e : (fun x : ℝ × ℝ ↦ shearColumnDensity x.1 x.2) =
      {x : ℝ × ℝ | shearThreshold x.1 < x.2}.indicator fun x ↦ ‖shearDifference x.1 x.2‖ₑ *
        ENNReal.ofReal (|x.2 - shearMap x.1 x.2| ^ (1 / 2 : ℝ)) := by
    ext x
    simp only [shearColumnDensity, indicator, mem_Ioi, mem_ofPred_eq]
  rw [e]
  exact hF.indicator (measurableSet_lt (hs.comp measurable_fst) measurable_snd)

/-- Where the sign quartic is `≥ 0`, the density vanishes. -/
theorem shearColumnDensity_eq_zero {p t : ℝ} (ht : 0 ≤ t) (h : 0 ≤ shearQuartic p t) :
    shearColumnDensity p t = 0 :=
  indicator_of_notMem (fun hs ↦ absurd (le_shearThreshold_of_shearQuartic_nonneg ht h)
    (not_le.2 (mem_Ioi.1 hs))) _

/-- `Δ(0, t) = 0`. -/
theorem shearDifference_zero_left (t : ℝ) : shearDifference 0 t = 0 := by
  have := shearDifference_neg_left 0 t
  rw [neg_zero] at this
  linarith

/-- `Δ ≥ 0` where the sign quartic is `≤ 0`, for `p ≥ 0`. -/
theorem shearDifference_nonneg_of_nonneg {p t : ℝ} (hp : 0 ≤ p) (ht : 0 < t)
    (h : shearQuartic p t ≤ 0) : 0 ≤ shearDifference p t := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · rw [← hp0, shearDifference_zero_left]
  · exact shearDifference_nonneg_of_shearQuartic_nonpos hp0 ht h

/-- **The pointwise bound.** For `p ≥ 0`, `t > 0` with `Q(p, t) ≤ 0`, `r > 0` and
`(t - T + r²)/(2r) ≤ α + β p + γ t`, the density is at most `Δ (α + β p + γ t)`. -/
theorem shearColumnDensity_le {p t α β γ r : ℝ} (hp : 0 ≤ p) (ht : 0 < t)
    (hQ : shearQuartic p t ≤ 0) (hr : 0 < r)
    (hW : (t - shearMap p t + r ^ 2) / (2 * r) ≤ α + β * p + γ * t) :
    shearColumnDensity p t ≤ ENNReal.ofReal (shearDifference p t * (α + β * p + γ * t)) := by
  have hΔ := shearDifference_nonneg_of_nonneg hp ht hQ
  have hT := shearMap_le_self_of_shearQuartic_nonpos ht hQ
  unfold shearColumnDensity
  refine (indicator_le_self _ _ _).trans ?_
  dsimp only
  rw [Real.enorm_eq_ofReal hΔ, ← ENNReal.ofReal_mul hΔ]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hΔ)
  rw [abs_of_nonneg (by linarith)]
  exact (sqrt_le_tangent (by linarith) hr).trans hW

/-- **The cell bound.** On `[p₀, p₁] × [t₀, t₁]` with `p₀ ≥ 0`, `t₀ > 0`, where the sign quartic
is `≤ 0` and `(t - T + r²)/(2r) ≤ α + β p + γ t`, the cell integral of the density is at most the
corner sum of `integral_integral_shearDifference_affine`. -/
theorem lintegral_shearColumnDensity_cell_le {p₀ p₁ t₀ t₁ α β γ r : ℝ} (hp₀ : 0 ≤ p₀)
    (hp : p₀ ≤ p₁) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) (hr : 0 < r)
    (hQ : ∀ p ∈ Icc p₀ p₁, ∀ t ∈ Icc t₀ t₁, shearQuartic p t ≤ 0)
    (hW : ∀ p ∈ Icc p₀ p₁, ∀ t ∈ Icc t₀ t₁,
      (t - shearMap p t + r ^ 2) / (2 * r) ≤ α + β * p + γ * t) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (cornerSum (fun p t ↦ shearCorner (α - β) β γ (p + 1) t -
        shearCorner (α + β) β γ (p - 1) t) p₀ p₁ t₀ t₁) := by
  calc ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, shearColumnDensity p t
      ≤ ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁,
          ENNReal.ofReal (shearDifference p t * (α + β * p + γ * t)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht' ↦ ?_
        refine setLIntegral_mono' measurableSet_Ioc fun p hp' ↦ ?_
        have ht'' := Ioc_subset_Icc_self ht'
        have hp'' := Ioc_subset_Icc_self hp'
        exact shearColumnDensity_le (hp₀.trans hp''.1) (ht₀.trans_le ht''.1) (hQ p hp'' t ht'')
          hr (hW p hp'' t ht'')
    _ = ENNReal.ofReal (∫ t in t₀..t₁, ∫ p in p₀..p₁,
          shearDifference p t * (α + β * p + γ * t)) := by
        refine lintegral_lintegral_ofReal_eq hp ht ?_ fun p hp' t ht' ↦ ?_
        · refine ContinuousOn.mul ?_ (by fun_prop)
          simp only [shearDifference, shearDensity_eq]
          refine ContinuousOn.sub ?_ ?_
          · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
              have : 0 < q.2 := ht₀.trans_le hq.2.1
              positivity
          · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
              have : 0 < q.2 := ht₀.trans_le hq.2.1
              positivity
        · have ht0 : 0 < t := ht₀.trans_le ht'.1
          have hΔ := shearDifference_nonneg_of_nonneg (hp₀.trans hp'.1) ht0 (hQ p hp' t ht')
          have hT := shearMap_le_self_of_shearQuartic_nonpos ht0 (hQ p hp' t ht')
          refine mul_nonneg hΔ ((div_nonneg ?_ (by positivity)).trans (hW p hp' t ht'))
          nlinarith [sq_nonneg r]
    _ = _ := by rw [integral_integral_shearDifference_affine α β γ ht₀ ht]

/-- **The strip bound.** If, on `(p₀, p₁] × (t₀, t₁]` above the threshold, `|Δ| ≤ D` and
`|t - T| ≤ φ`, then the cell integral is at most `(p₁ - p₀)(t₁ - t₀) D √φ`. -/
theorem lintegral_shearColumnDensity_strip_le {p₀ p₁ t₀ t₁ D φ : ℝ} (hp : p₀ ≤ p₁)
    (hD : 0 ≤ D)
    (hb : ∀ p ∈ Ioc p₀ p₁, ∀ t ∈ Ioc t₀ t₁, shearThreshold p < t →
      |shearDifference p t| ≤ D ∧ |t - shearMap p t| ≤ φ) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, shearColumnDensity p t ≤
      ENNReal.ofReal ((p₁ - p₀) * (t₁ - t₀) * (D * Real.sqrt φ)) := by
  have hpt : ∀ p ∈ Ioc p₀ p₁, ∀ t ∈ Ioc t₀ t₁,
      shearColumnDensity p t ≤ ENNReal.ofReal (D * Real.sqrt φ) := by
    intro p hp' t ht'
    unfold shearColumnDensity
    by_cases hs : t ∈ Ioi (shearThreshold p)
    · rw [indicator_of_mem hs]
      obtain ⟨h1, h2⟩ := hb p hp' t ht' hs
      rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul h1 ?_ (by positivity) hD)
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt h2
    · rw [indicator_of_notMem hs]
      exact zero_le
  calc ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, shearColumnDensity p t
      ≤ ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, ENNReal.ofReal (D * Real.sqrt φ) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht' ↦ ?_
        exact setLIntegral_mono' measurableSet_Ioc fun p hp' ↦ hpt p hp' t ht'
    _ = ENNReal.ofReal ((p₁ - p₀) * (t₁ - t₀) * (D * Real.sqrt φ)) := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Real.volume_Ioc]
        have h0 : 0 ≤ D * Real.sqrt φ := mul_nonneg hD (Real.sqrt_nonneg _)
        rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (mul_nonneg h0 (sub_nonneg.2 hp))]
        congr 1
        ring

end IncompressibleFlow.SharpHolder
