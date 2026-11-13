/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowBounds
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearCostTails

/-!
# Cell bounds of the transport cost of the inner rows

The inner row cost `2 ∫_0^{h_c^-(q)} |Δ| |p - T_y|^{1/2} dp + ∫_{T_y(0, q)}^1 |Δ| (2p)^{1/2} dp`
of `shearInnerRowCost` is `2 ∫ shearRowDensity · q` plus the remainder
(`shearInnerRowCost_eq`). On the inner region `Δ ≤ 0` and `p < T_y`, so on a rectangle where the
sign quartic is `≥ 0` the tangent bound and an affine majorant `α + β p + γ q ≥ 0` turn the cell
into a corner sum (`lintegral_shearRowDensity_cell_le`); a rectangle crossing `h_c^-` is bounded by
its area (`lintegral_shearRowDensity_strip_le`). The rows `q ≤ a` cost at most `2 √a`
(`lintegral_shearRowDensity_bottom_le`): there `p < 1 - q`, `T_y < 1` and
`|Δ| ≤ 1/2 + 1/(2 (1 - p)²)`.

## Main definitions

* `shearRowDensity`: the transport density `|Δ(p, q)| |p - T_y(p, q)|^{1/2}` of the row `q` on
  the inner region `0 < p < h_c^-(q)`, extended by zero.
* `shearNextRow`: the next node `p + ρ (1 - p)` of a walk in `p` toward `1`.

## Main results

* `shearInnerRowCost_eq`: the inner row cost as the row density and the remainder.
* `shearRowDensity_le`: the pointwise tangent bound of the row density.
* `lintegral_shearRowDensity_cell_le`: the corner-sum bound of a cell where `Q ≥ 0`.
* `lintegral_shearRowDensity_strip_le`: the area bound of a cell crossing `h_c^-`.
* `lintegral_shearRowDensity_bottom_le`: the rows `q ≤ a`, `a ≤ 1/4`, cost at most `2 √a`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter PDE.Analysis
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- The transport density `|Δ(p, q)| |p - T_y(p, q)|^{1/2}` of the row `q` on the inner region
`0 < p < h_c^-(q)`, extended by zero. -/
def shearRowDensity (p q : ℝ) : ℝ≥0∞ :=
  (Ioo 0 (lowerShearThreshold q)).indicator (fun p ↦ ‖shearDifference p q‖ₑ *
    ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ))) p

/-- The lower threshold `h_c^-` is measurable. -/
theorem measurable_lowerShearThreshold : Measurable lowerShearThreshold := by
  unfold lowerShearThreshold
  fun_prop

/-- The row density is jointly measurable in `(p, q)`. -/
theorem measurable_shearRowDensity : Measurable fun x : ℝ × ℝ ↦ shearRowDensity x.1 x.2 := by
  have hF : Measurable fun x : ℝ × ℝ ↦ ‖shearDifference x.1 x.2‖ₑ *
      ENNReal.ofReal (|x.1 - horizontalShearMap x.1 x.2| ^ (1 / 2 : ℝ)) :=
    measurable_shearDifference.enorm.mul
      ((continuous_abs.measurable.comp (measurable_fst.sub measurable_horizontalShearMap)).pow_const
        _).ennreal_ofReal
  have e : (fun x : ℝ × ℝ ↦ shearRowDensity x.1 x.2) =
      {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < lowerShearThreshold x.2}.indicator fun x ↦
        ‖shearDifference x.1 x.2‖ₑ *
          ENNReal.ofReal (|x.1 - horizontalShearMap x.1 x.2| ^ (1 / 2 : ℝ)) := by
    ext x
    simp only [shearRowDensity, indicator, mem_Ioo, mem_ofPred_eq]
  rw [e]
  exact hF.indicator ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst (measurable_lowerShearThreshold.comp measurable_snd)))

/-- The inner row cost as the row density and the remainder. -/
theorem shearInnerRowCost_eq (q : ℝ) :
    shearInnerRowCost q = 2 * (∫⁻ p, shearRowDensity p q) +
      ∫⁻ p in Ioo (horizontalShearMap 0 q) 1,
        ‖shearDifference p q‖ₑ * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ)) := by
  rw [shearInnerRowCost]
  congr 2
  unfold shearRowDensity
  rw [lintegral_indicator measurableSet_Ioo]

/-- The row density vanishes for `p ≥ h_c^-(q)`. -/
theorem shearRowDensity_eq_zero_of_le {p q : ℝ} (h : lowerShearThreshold q ≤ p) :
    shearRowDensity p q = 0 :=
  indicator_of_notMem (fun hp ↦ absurd h (not_le.2 hp.2)) _

/-- On the inner region `p < T_y`, and `3q² < 1`. -/
theorem lt_horizontalShearMap_of_mem {p q : ℝ} (hq : 0 < q) (hp : 0 < p)
    (hlt : p < lowerShearThreshold q) : p < horizontalShearMap p q ∧ 3 * q ^ 2 < 1 := by
  have h3 : 3 * q ^ 2 < 1 := by
    by_contra hc
    push Not at hc
    rw [lowerShearThreshold_eq_zero hq.le hc] at hlt
    linarith
  exact ⟨hlt.trans (lowerShearThreshold_lt_horizontalShearMap hq h3 hp.le hlt), h3⟩

/-- **The pointwise bound.** -/
theorem shearRowDensity_le {p q α β γ r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hΔ : shearDifference p q ≤ 0)
    (hW : 0 < p → p < lowerShearThreshold q →
      (horizontalShearMap p q - p + r ^ 2) / (2 * r) ≤ α + β * p + γ * q) :
    shearRowDensity p q ≤ ENNReal.ofReal (-shearDifference p q * (α + β * p + γ * q)) := by
  unfold shearRowDensity
  by_cases hs : p ∈ Ioo 0 (lowerShearThreshold q)
  · rw [indicator_of_mem hs]
    obtain ⟨hT, -⟩ := lt_horizontalShearMap_of_mem hq hs.1 hs.2
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos hΔ,
      ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by linarith))
    rw [abs_of_neg (by linarith), neg_sub]
    exact (sqrt_le_tangent (by linarith) hr).trans (hW hs.1 hs.2)
  · rw [indicator_of_notMem hs]
    exact zero_le

/-- **The cell bound** of the inner rows. -/
theorem lintegral_shearRowDensity_cell_le {p₀ p₁ q₀ q₁ α β γ r : ℝ} (hp₀ : 0 ≤ p₀)
    (hp : p₀ ≤ p₁) (hq₀ : 0 < q₀) (hq : q₀ ≤ q₁) (hr : 0 < r)
    (hQ : ∀ p ∈ Icc p₀ p₁, ∀ q ∈ Icc q₀ q₁, 0 ≤ shearQuartic p q)
    (hW0 : ∀ p ∈ Icc p₀ p₁, ∀ q ∈ Icc q₀ q₁, 0 ≤ α + β * p + γ * q)
    (hW : ∀ p ∈ Icc p₀ p₁, ∀ q ∈ Icc q₀ q₁, 0 < p → p < lowerShearThreshold q →
      (horizontalShearMap p q - p + r ^ 2) / (2 * r) ≤ α + β * p + γ * q) :
    ∫⁻ q in Ioc q₀ q₁, ∫⁻ p in Ioc p₀ p₁, shearRowDensity p q ≤
      ENNReal.ofReal (cornerSum (fun p t ↦ shearCorner (-α + β) (-β) (-γ) (p + 1) t -
        shearCorner (-α - β) (-β) (-γ) (p - 1) t) p₀ p₁ q₀ q₁) := by
  have hΔ : ∀ p ∈ Icc p₀ p₁, ∀ q ∈ Icc q₀ q₁, shearDifference p q ≤ 0 := fun p hp q hq ↦
    shearDifference_nonpos_of_shearQuartic_nonneg (hp₀.trans hp.1) (hq₀.trans_le hq.1)
      (hQ p hp q hq)
  calc ∫⁻ q in Ioc q₀ q₁, ∫⁻ p in Ioc p₀ p₁, shearRowDensity p q
      ≤ ∫⁻ q in Ioc q₀ q₁, ∫⁻ p in Ioc p₀ p₁,
          ENNReal.ofReal (-shearDifference p q * (α + β * p + γ * q)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun q hq' ↦ ?_
        refine setLIntegral_mono' measurableSet_Ioc fun p hp' ↦ ?_
        have hq'' := Ioc_subset_Icc_self hq'
        have hp'' := Ioc_subset_Icc_self hp'
        exact shearRowDensity_le (hq₀.trans_le hq''.1) hr (hΔ p hp'' q hq'') (hW p hp'' q hq'')
    _ = ENNReal.ofReal (∫ q in q₀..q₁, ∫ p in p₀..p₁,
          -shearDifference p q * (α + β * p + γ * q)) := by
        refine lintegral_lintegral_ofReal_eq hp hq ?_ fun p hp' q hq' ↦
          mul_nonneg (neg_nonneg.2 (hΔ p hp' q hq')) (hW0 p hp' q hq')
        refine ContinuousOn.mul (ContinuousOn.neg ?_) (by fun_prop)
        simp only [shearDifference, shearDensity_eq]
        refine ContinuousOn.sub ?_ ?_ <;>
          exact ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx ↦ by
            have : 0 < x.2 := hq₀.trans_le hx.2.1
            positivity
    _ = _ := by
        congr 1
        have h := integral_integral_shearDifference_affine (-α) (-β) (-γ) hq₀ hq (p₀ := p₀)
          (p₁ := p₁)
        rw [show -α - -β = -α + β by ring, show -α + -β = -α - β by ring] at h
        rw [← h]
        congr 1
        ext q
        congr 1
        ext p
        ring

/-- **The strip bound** of the inner rows. -/
theorem lintegral_shearRowDensity_strip_le {p₀ p₁ q₀ q₁ D φ : ℝ} (hp : p₀ ≤ p₁) (hD : 0 ≤ D)
    (hb : ∀ p ∈ Ioc p₀ p₁, ∀ q ∈ Ioc q₀ q₁, 0 < p → p < lowerShearThreshold q →
      |shearDifference p q| ≤ D ∧ |p - horizontalShearMap p q| ≤ φ) :
    ∫⁻ q in Ioc q₀ q₁, ∫⁻ p in Ioc p₀ p₁, shearRowDensity p q ≤
      ENNReal.ofReal ((p₁ - p₀) * (q₁ - q₀) * (D * Real.sqrt φ)) := by
  have hpt : ∀ q ∈ Ioc q₀ q₁, ∀ p ∈ Ioc p₀ p₁,
      shearRowDensity p q ≤ ENNReal.ofReal (D * Real.sqrt φ) := by
    intro q hq' p hp'
    unfold shearRowDensity
    by_cases hs : p ∈ Ioo 0 (lowerShearThreshold q)
    · rw [indicator_of_mem hs]
      obtain ⟨h1, h2⟩ := hb p hp' q hq' hs.1 hs.2
      rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _),
        ← Real.sqrt_eq_rpow]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul h1 (Real.sqrt_le_sqrt h2) (by positivity) hD)
    · rw [indicator_of_notMem hs]
      exact zero_le
  calc ∫⁻ q in Ioc q₀ q₁, ∫⁻ p in Ioc p₀ p₁, shearRowDensity p q
      ≤ ∫⁻ q in Ioc q₀ q₁, ∫⁻ p in Ioc p₀ p₁, ENNReal.ofReal (D * Real.sqrt φ) :=
        setLIntegral_mono' measurableSet_Ioc fun q hq' ↦
          setLIntegral_mono' measurableSet_Ioc (hpt q hq')
    _ = ENNReal.ofReal ((p₁ - p₀) * (q₁ - q₀) * (D * Real.sqrt φ)) := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Real.volume_Ioc]
        have h0 : 0 ≤ D * Real.sqrt φ := mul_nonneg hD (Real.sqrt_nonneg _)
        rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (mul_nonneg h0 (sub_nonneg.2 hp))]
        congr 1
        ring

/-- **The bottom rows**: the rows `q ≤ a`, `a ≤ 1/4`, cost at most `2 √a`. -/
theorem lintegral_shearRowDensity_bottom_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) :
    ∫⁻ q in Ioc 0 a, ∫⁻ p, shearRowDensity p q ≤ ENNReal.ofReal (2 * Real.sqrt a) := by
  have hpt : ∀ q ∈ Ioc (0 : ℝ) a, ∫⁻ p, shearRowDensity p q ≤
      ENNReal.ofReal (1 / Real.sqrt q) := by
    intro q hq
    have hq0 : 0 < q := hq.1
    have hq1 : q < 1 := by linarith [hq.2]
    -- the density is supported in `(0, 1 - q)` and bounded there
    have hsupp : ∀ p, shearRowDensity p q ≤ (Ioc 0 (1 - q)).indicator (fun p ↦
        ENNReal.ofReal (Real.sqrt (1 - p) / 2 + 1 / (2 * ((1 - p) * Real.sqrt (1 - p))))) p := by
      intro p
      unfold shearRowDensity
      by_cases hs : p ∈ Ioo 0 (lowerShearThreshold q)
      · rw [indicator_of_mem hs]
        have hp1 : p < 1 - q :=
          hs.2.trans_le (lowerShearThreshold_le_one_sub hq0.le hq1.le)
        rw [indicator_of_mem (show p ∈ Ioc 0 (1 - q) from ⟨hs.1, hp1.le⟩)]
        obtain ⟨hT, h3⟩ := lt_horizontalShearMap_of_mem hq0 hs.1 hs.2
        have hT1 := horizontalShearMap_lt_one hq0 h3 hs.1.le hs.2
        have hu : 0 < 1 - p := by linarith
        have hsu := Real.sqrt_pos.2 hu
        rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hΔ : |shearDifference p q| ≤ 1 / 2 + 1 / (2 * (1 - p) ^ 2) := by
          have h₁ := abs_shearDensity_le (p + 1) q
          have h₂ := abs_shearDensity_le (p - 1) q
          have e₁ : 1 / (2 * ((p + 1) ^ 2 + q ^ 2)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [sq_nonneg q, hs.1]
          have e₂ : 1 / (2 * ((p - 1) ^ 2 + q ^ 2)) ≤ 1 / (2 * (1 - p) ^ 2) := by
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith [sq_nonneg q]
          exact (abs_sub _ _).trans (add_le_add (h₁.trans e₁) (h₂.trans e₂))
        have hφ : |p - horizontalShearMap p q| ^ (1 / 2 : ℝ) ≤ Real.sqrt (1 - p) := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_sqrt (by rw [abs_of_neg (by linarith)]; linarith)
        calc |shearDifference p q| * |p - horizontalShearMap p q| ^ (1 / 2 : ℝ)
            ≤ (1 / 2 + 1 / (2 * (1 - p) ^ 2)) * Real.sqrt (1 - p) :=
              mul_le_mul hΔ hφ (by positivity) (by positivity)
          _ = Real.sqrt (1 - p) / 2 + 1 / (2 * ((1 - p) * Real.sqrt (1 - p))) := by
              have hs2 := Real.sq_sqrt hu.le
              generalize Real.sqrt (1 - p) = s at hsu hs2 ⊢
              rw [show (1 : ℝ) - p = s ^ 2 from hs2.symm]
              field_simp
      · rw [indicator_of_notMem hs]
        exact zero_le
    -- the primitive `-(1 - p)^{3/2}/3 + (1 - p)^{-1/2}`
    have hint : ∫⁻ p in Ioc 0 (1 - q),
        ENNReal.ofReal (Real.sqrt (1 - p) / 2 + 1 / (2 * ((1 - p) * Real.sqrt (1 - p)))) =
        ENNReal.ofReal ((-(q * Real.sqrt q) / 3 + 1 / Real.sqrt q) -
          (-(1 * Real.sqrt 1) / 3 + 1 / Real.sqrt 1)) := by
      have h := lintegral_Ioc_ofReal_deriv (a := 0) (b := 1 - q)
        (g := fun p ↦ -((1 - p) * Real.sqrt (1 - p)) / 3 + 1 / Real.sqrt (1 - p))
        (g' := fun p ↦ Real.sqrt (1 - p) / 2 + 1 / (2 * ((1 - p) * Real.sqrt (1 - p))))
        (by linarith) ?_ (fun p hp ↦ ?_) (fun p hp ↦ ?_)
      · rw [h]
        congr 1
        simp only [sub_sub_cancel, sub_zero]
      · have hc : Continuous fun p : ℝ ↦ -((1 - p) * Real.sqrt (1 - p)) / 3 := by fun_prop
        refine hc.continuousOn.add (continuousOn_const.div (by fun_prop) fun p hp ↦ ?_)
        exact (Real.sqrt_pos.2 (by linarith [hp.2])).ne'
      · have hu : 0 < 1 - p := by linarith [hp.2]
        have hsu := Real.sqrt_pos.2 hu
        have hd : HasDerivAt (fun p ↦ 1 - p) (-1) p := by
          simpa using (hasDerivAt_id p).const_sub 1
        have hsq := hd.sqrt hu.ne'
        refine (((hd.mul hsq).neg.div_const 3).add
          ((hasDerivAt_const p (1 : ℝ)).div hsq hsu.ne')).congr_deriv ?_
        have hs2 := Real.sq_sqrt hu.le
        generalize Real.sqrt (1 - p) = s at hsu hs2 ⊢
        rw [show (1 : ℝ) - p = s ^ 2 from hs2.symm]
        field_simp
        ring
      · have hu : 0 < 1 - p := by linarith [hp.2]
        positivity
    calc ∫⁻ p, shearRowDensity p q
        ≤ ∫⁻ p, (Ioc 0 (1 - q)).indicator (fun p ↦ ENNReal.ofReal
            (Real.sqrt (1 - p) / 2 + 1 / (2 * ((1 - p) * Real.sqrt (1 - p))))) p :=
          lintegral_mono hsupp
      _ = ∫⁻ p in Ioc 0 (1 - q), ENNReal.ofReal
            (Real.sqrt (1 - p) / 2 + 1 / (2 * ((1 - p) * Real.sqrt (1 - p)))) :=
          lintegral_indicator measurableSet_Ioc _
      _ = _ := hint
      _ ≤ ENNReal.ofReal (1 / Real.sqrt q) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [Real.sqrt_one, mul_one, div_one]
          have : 0 ≤ q * Real.sqrt q := mul_nonneg hq0.le (Real.sqrt_nonneg _)
          linarith
  calc ∫⁻ q in Ioc 0 a, ∫⁻ p, shearRowDensity p q
      ≤ ∫⁻ q in Ioc 0 a, ENNReal.ofReal (1 / Real.sqrt q) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal (2 * Real.sqrt a) := by
        rw [lintegral_Ioc_ofReal_deriv (g := fun q ↦ 2 * Real.sqrt q) ha.le (by fun_prop)
          (fun q hq ↦ ?_) (fun q hq ↦ by positivity)]
        · simp
        · have hq0 : 0 < q := hq.1
          refine ((Real.hasDerivAt_sqrt hq0.ne').const_mul 2).congr_deriv ?_
          have hs := Real.sqrt_pos.2 hq0
          field_simp

/-- The next node `p + ρ (1 - p)` of a walk in `p` toward `1`, rounded up. -/
def shearNextRow (ρ p : ℚ) : ℚ := roundUpRel (p + ρ * (1 - p))

end IncompressibleFlow.SharpHolder
