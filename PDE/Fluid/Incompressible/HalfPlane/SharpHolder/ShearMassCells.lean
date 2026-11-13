/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearHolderEnvelope
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearUpperCells
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowBounds

/-!
# The mass of the shear kernel over a slab

The outer term of the estimate of `u_y` needs `∫_{t₀}^{t₁} ∫_0^∞ |Δ(p, t)| dp dt` over slabs.
On a rectangle where `Δ` has one sign this is the absolute value of the corner sum of the angular
primitive (`lintegral_enorm_shearDifference_eq_of_nonneg`,
`lintegral_enorm_shearDifference_eq_of_nonpos`); beyond `P > 1`, where `Δ ≤ 0`, the column
integrals are explicit and the slab mass is a difference of arctangents
(`lintegral_enorm_shearDifference_far_eq`); a band around a threshold is bounded by its area
(`lintegral_enorm_shearDifference_le_strip`). `shearSlabMass` assembles the six pieces of a slab
and `lintegral_le_shearSlabMass` is its soundness.

## Main definitions

* `shearFarHigh`: an upper bound of the mass of the far region `p > P` of a slab.
* `shearStripMass`: the mass bound of a band `[p_a, p_b]` from bounds of `|Q|` and of the
  denominator.
* `shearSlabMassPieces`: the six pieces of a slab, from the left zero region to the far region.
* `shearSlabMass`: the mass of a slab `[t₀, t₁]` over all columns `p > 0`, after the checks, as
  a numerator over `2⁶⁴`.

## Main results

* `integral_integral_shearDifference_eq`: `∫∫ Δ` over a rectangle above the axis is the
  difference of the angular corner sums.
* `lintegral_enorm_shearDifference_eq_of_nonneg`, `lintegral_enorm_shearDifference_eq_of_nonpos`:
  the mass of `|Δ|` over a rectangle where `Δ` has one sign.
* `lintegral_enorm_shearDifference_far_eq`: for `P > 1` the slab mass beyond `P` is
  `(arctan (t₁/(P - 1)) - arctan (t₀/(P - 1)) - arctan (t₁/(P + 1)) + arctan (t₀/(P + 1)))/2`.
* `lintegral_enorm_shearDifference_le_strip`: the mass of a band is at most its area times a
  bound of `|Δ|`.
* `lintegral_le_shearSlabMass`: if `shearSlabMass t₀ t₁ = some N`, then
  `∫_{t₀}^{t₁} ∫_0^∞ |Δ(p, t)| dp dt ≤ N / 2⁶⁴`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter PDE.Analysis
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-! ### Real pieces -/

/-- `∫∫ Δ` over a rectangle above the axis is the difference of the angular corner sums. -/
theorem integral_integral_shearDifference_eq {p₀ p₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    ∫ t in t₀..t₁, ∫ p in p₀..p₁, shearDifference p t =
      cornerSum (fun a t ↦ Real.arctan (a / t) / 2) (p₀ + 1) (p₁ + 1) t₀ t₁ -
        cornerSum (fun a t ↦ Real.arctan (a / t) / 2) (p₀ - 1) (p₁ - 1) t₀ t₁ := by
  have h := integral_integral_shearDifference_affine 1 0 0 (p₀ := p₀) (p₁ := p₁) ht₀ ht
  simp only [zero_mul, add_zero, mul_one, sub_zero] at h
  rw [h]
  simp only [cornerSum, shearCorner]
  ring

/-- On a cell on one side of `p = 1` with `t₀ > 0`, `∫∫ Δ ≤ shearMassHigh`. -/
theorem integral_integral_shearDifference_le_shearMassHigh {p₀ p₁ t₀ t₁ : ℚ} (hp₀ : 0 ≤ p₀)
    (hp : p₀ ≤ p₁) (h1 : 0 ≤ (p₀ - 1) * (p₁ - 1)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    ∫ t in (t₀ : ℝ)..t₁, ∫ p in (p₀ : ℝ)..p₁, shearDifference p t ≤ shearMassHigh p₀ p₁ t₀ t₁ := by
  have hplus := (shearAnglePair_spec (a₀ := p₀ + 1) (a₁ := p₁ + 1) ht₀ ht (by linarith)
    (mul_nonneg (by linarith) (by linarith))).2
  have hminus := (shearAnglePair_spec (a₀ := p₀ - 1) (a₁ := p₁ - 1) ht₀ ht (by linarith) h1).1
  push_cast at hplus hminus
  rw [integral_integral_shearDifference_eq (by exact_mod_cast ht₀) (by exact_mod_cast ht)]
  simp only [shearMassHigh]
  push_cast
  linarith

/-- On a cell on one side of `p = 1` with `t₀ > 0`, `shearMassLow ≤ ∫∫ Δ`. -/
theorem shearMassLow_le_integral_integral_shearDifference {p₀ p₁ t₀ t₁ : ℚ} (hp₀ : 0 ≤ p₀)
    (hp : p₀ ≤ p₁) (h1 : 0 ≤ (p₀ - 1) * (p₁ - 1)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    (shearMassLow p₀ p₁ t₀ t₁ : ℝ) ≤
      ∫ t in (t₀ : ℝ)..t₁, ∫ p in (p₀ : ℝ)..p₁, shearDifference p t := by
  have hplus := (shearAnglePair_spec (a₀ := p₀ + 1) (a₁ := p₁ + 1) ht₀ ht (by linarith)
    (mul_nonneg (by linarith) (by linarith))).1
  have hminus := (shearAnglePair_spec (a₀ := p₀ - 1) (a₁ := p₁ - 1) ht₀ ht (by linarith) h1).2
  push_cast at hplus hminus
  rw [integral_integral_shearDifference_eq (by exact_mod_cast ht₀) (by exact_mod_cast ht)]
  simp only [shearMassLow]
  push_cast
  linarith

/-- For `t₀ > 0`, `Δ` is continuous on the rectangle `[p₀, p₁] × [t₀, t₁]`. -/
private theorem continuousOn_shearDifference_rect {p₀ p₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousOn (fun x : ℝ × ℝ ↦ shearDifference x.1 x.2) (Icc p₀ p₁ ×ˢ Icc t₀ t₁) := by
  simp only [shearDifference, shearDensity_eq]
  refine ContinuousOn.sub ?_ ?_
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
      have : 0 < q.2 := ht₀.trans_le hq.2.1
      positivity
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq ↦ by
      have : 0 < q.2 := ht₀.trans_le hq.2.1
      positivity

/-- The mass of `|Δ|` over a rectangle where `Δ ≥ 0`. -/
theorem lintegral_enorm_shearDifference_eq_of_nonneg {p₀ p₁ t₀ t₁ : ℝ} (hp : p₀ ≤ p₁)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁)
    (hΔ : ∀ p ∈ Icc p₀ p₁, ∀ t ∈ Icc t₀ t₁, 0 ≤ shearDifference p t) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, ‖shearDifference p t‖ₑ =
      ENNReal.ofReal (∫ t in t₀..t₁, ∫ p in p₀..p₁, shearDifference p t) := by
  rw [← lintegral_lintegral_ofReal_eq hp ht (continuousOn_shearDifference_rect ht₀) hΔ]
  refine setLIntegral_congr_fun measurableSet_Ioc fun t ht' ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioc fun p hp' ↦ ?_
  rw [← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg (hΔ p (Ioc_subset_Icc_self hp') t (Ioc_subset_Icc_self ht'))]

/-- The mass of `|Δ|` over a rectangle where `Δ ≤ 0`. -/
theorem lintegral_enorm_shearDifference_eq_of_nonpos {p₀ p₁ t₀ t₁ : ℝ} (hp : p₀ ≤ p₁)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁)
    (hΔ : ∀ p ∈ Icc p₀ p₁, ∀ t ∈ Icc t₀ t₁, shearDifference p t ≤ 0) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, ‖shearDifference p t‖ₑ =
      ENNReal.ofReal (-∫ t in t₀..t₁, ∫ p in p₀..p₁, shearDifference p t) := by
  have hc : ContinuousOn (fun x : ℝ × ℝ ↦ -shearDifference x.1 x.2) (Icc p₀ p₁ ×ˢ Icc t₀ t₁) :=
    (continuousOn_shearDifference_rect ht₀).neg
  rw [show -∫ t in t₀..t₁, ∫ p in p₀..p₁, shearDifference p t =
      ∫ t in t₀..t₁, ∫ p in p₀..p₁, -shearDifference p t by
    simp only [intervalIntegral.integral_neg],
    ← lintegral_lintegral_ofReal_eq hp ht hc fun p hp t ht ↦ neg_nonneg.2 (hΔ p hp t ht)]
  refine setLIntegral_congr_fun measurableSet_Ioc fun t ht' ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioc fun p hp' ↦ ?_
  rw [← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonpos (hΔ p (Ioc_subset_Icc_self hp') t (Ioc_subset_Icc_self ht'))]

/-- **The far region**: for `P > 1` and `Δ ≤ 0` beyond `P`, the slab mass beyond `P` is
`(arctan (t₁/(P - 1)) - arctan (t₀/(P - 1)) - arctan (t₁/(P + 1)) + arctan (t₀/(P + 1)))/2`. -/
theorem lintegral_enorm_shearDifference_far_eq {P t₀ t₁ : ℝ} (hP : 1 < P) (ht₀ : 0 < t₀)
    (ht : t₀ ≤ t₁) (hΔ : ∀ p ∈ Ici P, ∀ t ∈ Icc t₀ t₁, shearDifference p t ≤ 0) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioi P, ‖shearDifference p t‖ₑ =
      ENNReal.ofReal ((Real.arctan (t₁ / (P - 1)) - Real.arctan (t₀ / (P - 1)) -
        (Real.arctan (t₁ / (P + 1)) - Real.arctan (t₀ / (P + 1)))) / 2) := by
  have hval : ∀ t, 0 < t → ∫ p in Ioi P, -shearDifference p t =
      (P - 1) / (2 * ((P - 1) ^ 2 + t ^ 2)) - (P + 1) / (2 * ((P + 1) ^ 2 + t ^ 2)) :=
    fun t ht0 ↦ by
      rw [integral_neg, show ∫ p in Ioi P, shearDifference p t =
          (∫ p in Ioi P, shearDensity (p + 1) t) - ∫ p in Ioi P, shearDensity (p + -1) t by
        rw [← integral_sub (integrable_shearDensity_add ht0 1).integrableOn
          (integrable_shearDensity_add ht0 (-1)).integrableOn]
        rfl, integral_Ioi_shearDensity_add ht0 P 1, integral_Ioi_shearDensity_add ht0 P (-1)]
      ring_nf
  have hcol : ∀ t ∈ Ioc t₀ t₁, ∫⁻ p in Ioi P, ‖shearDifference p t‖ₑ =
      ENNReal.ofReal ((P - 1) / (2 * ((P - 1) ^ 2 + t ^ 2)) -
        (P + 1) / (2 * ((P + 1) ^ 2 + t ^ 2))) := by
    intro t ht'
    have ht0 : 0 < t := ht₀.trans ht'.1
    have hneg : ∀ p ∈ Ioi P, shearDifference p t ≤ 0 := fun p hp ↦
      hΔ p (le_of_lt hp) t (Ioc_subset_Icc_self ht')
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun p ↦ ENNReal.ofReal
      (-shearDifference p t)) fun p hp ↦ by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos (hneg p hp)],
      ← ofReal_integral_eq_lintegral_ofReal (f := fun p ↦ -shearDifference p t)
        ((integrable_shearDensity_add ht0 1).sub
          (integrable_shearDensity_add ht0 (-1))).neg.integrableOn
        (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi)
          fun p hp ↦ neg_nonneg.2 (hneg p hp)), hval t ht0]
  rw [setLIntegral_congr_fun measurableSet_Ioc hcol]
  have hP₁ : 0 < P - 1 := by linarith
  have hP₂ : 0 < P + 1 := by linarith
  rw [lintegral_Ioc_ofReal_deriv (g := fun t ↦ (Real.arctan (t / (P - 1)) -
      Real.arctan (t / (P + 1))) / 2) ht (by fun_prop) (fun t _ ↦ ?_) (fun t ht' ↦ ?_)]
  · congr 1
    ring
  · have d₁ := hasDerivAt_arctan_div_const (c := P - 1) t
    have d₂ := hasDerivAt_arctan_div_const (c := P + 1) t
    refine ((d₁.sub d₂).div_const 2).congr_deriv ?_
    field_simp
  · -- the column value is the integral of `-Δ ≥ 0`
    have h := hval t (ht₀.trans ht'.1)
    have hnn : 0 ≤ ∫ p in Ioi P, -shearDifference p t :=
      setIntegral_nonneg measurableSet_Ioi fun p hp ↦ neg_nonneg.2 (hΔ p (le_of_lt hp) t
        (Ioc_subset_Icc_self ht'))
    ring_nf at h hnn ⊢
    linarith

/-- **The strip bound** of the mass. -/
theorem lintegral_enorm_shearDifference_le_strip {p₀ p₁ t₀ t₁ D : ℝ} (hp : p₀ ≤ p₁)
    (hD : 0 ≤ D) (hb : ∀ p ∈ Ioc p₀ p₁, ∀ t ∈ Ioc t₀ t₁, |shearDifference p t| ≤ D) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal ((p₁ - p₀) * (t₁ - t₀) * D) := by
  calc ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, ‖shearDifference p t‖ₑ
      ≤ ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁, ENNReal.ofReal D := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht' ↦ ?_
        refine setLIntegral_mono' measurableSet_Ioc fun p hp' ↦ ?_
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hb p hp' t ht')
    _ = ENNReal.ofReal ((p₁ - p₀) * (t₁ - t₀) * D) := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Real.volume_Ioc]
        rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul (mul_nonneg hD (sub_nonneg.2 hp))]
        congr 1
        ring

/-! ### The rational slab mass -/

/-- An upper bound of the far region of a slab, `(A(P - 1) - A(P + 1))/2` with
`A(c) = arctan (t₁/c) - arctan (t₀/c)`. -/
def shearFarHigh (P t₀ t₁ : ℚ) : ℚ :=
  (atanPair (strainG (P - 1) t₀ t₁)).2 / 2 - (atanPair (strainG (P + 1) t₀ t₁)).1 / 2

/-- For `P > 1` and `0 ≤ t₀ ≤ t₁`, `(A(P - 1) - A(P + 1))/2 ≤ shearFarHigh P t₀ t₁` with
`A(c) = arctan (t₁/c) - arctan (t₀/c)`. -/
theorem le_shearFarHigh {P t₀ t₁ : ℚ} (hP : 1 < P) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) :
    (Real.arctan (t₁ / ((P : ℝ) - 1)) - Real.arctan (t₀ / ((P : ℝ) - 1)) -
        (Real.arctan (t₁ / ((P : ℝ) + 1)) - Real.arctan (t₀ / ((P : ℝ) + 1)))) / 2 ≤
      shearFarHigh P t₀ t₁ := by
  have hP' : (1 : ℝ) < P := by exact_mod_cast hP
  have ht₀' : (0 : ℝ) ≤ t₀ := by exact_mod_cast ht₀
  have ht₁' : (0 : ℝ) ≤ t₁ := by exact_mod_cast (ht₀.trans ht)
  rw [arctan_sub_arctan_div (by linarith) ht₀' ht₁', arctan_sub_arctan_div (by linarith) ht₀' ht₁']
  have h₁ := le_atanPair_snd (strainG (P - 1) t₀ t₁)
  have h₂ := atanPair_fst_le (strainG (P + 1) t₀ t₁)
  simp only [strainG] at h₁ h₂
  push_cast at h₁ h₂
  simp only [shearFarHigh, strainG]
  push_cast
  linarith

/-- The mass bound of a band `[p_a, p_b]` from a bound `Qm` of `|Q|` and the denominator `Dm`. -/
def shearStripMass (t₀ t₁ pa pb Qm Dm : ℚ) : ℚ := (pb - pa) * (t₁ - t₀) * (2 * pb * Qm / Dm)

/-- `|Δ| ≤ 2 p |Q| / ((p + 1)² + t²)² ((p - 1)² + t²)²`, the form used by the strips. -/
theorem abs_shearDifference_eq {p t : ℝ} (hp : 0 ≤ p) (ht : 0 < t) :
    |shearDifference p t| = 2 * p * |shearQuartic p t| /
      (((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2) := by
  have h₁ : (p + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h₂ : (p - 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  rw [shearDifference_eq h₁ h₂, abs_div, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2),
    abs_of_nonneg hp]
  norm_num

/-- The strip bound from a bound of `|Q|` and a lower bound of the denominator. -/
theorem abs_shearDifference_le_strip {p t pb Qm Dm : ℝ} (hp : 0 ≤ p) (hpb : p ≤ pb)
    (ht : 0 < t) (hQ : |shearQuartic p t| ≤ Qm) (hDm : 0 < Dm)
    (hD : Dm ≤ ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2) :
    |shearDifference p t| ≤ 2 * pb * Qm / Dm := by
  rw [abs_shearDifference_eq hp ht]
  have hQm : 0 ≤ Qm := (abs_nonneg _).trans hQ
  calc 2 * p * |shearQuartic p t| / (((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2)
      ≤ 2 * pb * Qm / (((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul (by linarith) hQ (abs_nonneg _) (by linarith))
          (by positivity)
    _ ≤ 2 * pb * Qm / Dm := div_le_div_of_nonneg_left (by nlinarith) hDm hD

/-- The six pieces of the mass of a slab `[t₀, t₁]`: the left zero region `[0, q_a]`, the left
strip `[q_a, q_b]`, the left cells `[q_b, 1]`, the right cells `[1, p_a]`, the right strip
`[p_a, p_b]` and the far region `p > p_b`. -/
def shearSlabMassPieces (t₀ t₁ pa pb qa qb : ℚ) : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ :=
  (-shearMassLow 0 qa t₀ t₁,
    shearStripMass t₀ t₁ qa qb (max (max 0 (shearQuarticRat qa t₀)) (-shearQuarticRat qb t₁))
      (((qa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((1 - qb) ^ 2 + t₀ ^ 2) ^ 2),
    shearMassHigh qb 1 t₀ t₁, shearMassHigh 1 pa t₀ t₁,
    shearStripMass t₀ t₁ pa pb (max (max 0 (-shearQuarticRat pa t₁)) (shearQuarticRat pb t₀))
      (((pa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((pa - 1) ^ 2 + t₀ ^ 2) ^ 2),
    shearFarHigh pb t₀ t₁)

/-- **The mass of a slab** `[t₀, t₁]` over all columns `p > 0`, after the checks. -/
def shearSlabMass (t₀ t₁ : ℚ) : Option ℤ :=
  let pa := roundDownRel (1 + shearUpperGap t₀ * (1 - 1 / 2 ^ 12))
  let pb := roundUpRel (1 + shearUpperGap t₁ * (1 + 1 / 2 ^ 12))
  let qa := max 0 (roundDownRel (1 - shearLowerGap t₁ * (1 + 1 / 2 ^ 12)))
  let qb := max 0 (min 1 (roundUpRel (1 - shearLowerGap t₀ * (1 - 1 / 2 ^ 12))))
  let m := shearSlabMassPieces t₀ t₁ pa pb qa qb
  if decide (0 < t₀) && decide (t₀ ≤ t₁) && decide (1 < pa) && decide (pa ≤ pb) &&
      decide (t₁ ^ 2 + 1 ≤ pa ^ 2) && decide (shearQuarticRat pa t₀ ≤ 0) &&
      decide (0 ≤ shearQuarticRat pb t₁) && decide (qa ≤ qb) &&
      (decide (qa = 0) || decide (0 ≤ shearQuarticRat qa t₁)) &&
      decide (shearQuarticRat qb t₀ ≤ 0) && decide (0 ≤ m.1) && decide (0 ≤ m.2.1) &&
      decide (0 ≤ m.2.2.1) && decide (0 ≤ m.2.2.2.1) && decide (0 ≤ m.2.2.2.2.1) &&
      decide (0 ≤ m.2.2.2.2.2) then
    some (ceilScaled 64 (m.1 + m.2.1 + m.2.2.1 + m.2.2.2.1 + m.2.2.2.2.1 + m.2.2.2.2.2))
  else none

/-- For a set `S`, `t ↦ ∫⁻ p in S, |Δ(p, t)|` is measurable. -/
theorem measurable_lintegral_enorm_shearDifference (S : Set ℝ) :
    Measurable fun t ↦ ∫⁻ p in S, ‖shearDifference p t‖ₑ :=
  (measurable_shearDifference.enorm.comp measurable_swap).lintegral_prod_right'

/-- `Q(1, t) ≤ 0`. -/
theorem shearQuartic_one_nonpos (t : ℝ) : shearQuartic 1 t ≤ 0 := by
  simp only [shearQuartic]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

/-- A strip `(p₀, p₁] × (t₀, t₁]` with `p₀ ≥ 0` and rational data: if `|Q| ≤ Q_m` and
`D_m ≤ ((p + 1)² + t²)² ((p - 1)² + t²)²` there, its mass is at most `shearStripMass`. -/
private theorem lintegral_le_shearStripMass {t₀ t₁ p₀ p₁ Qm Dm : ℚ} (hp : (p₀ : ℝ) ≤ p₁)
    (hp₀ : (0 : ℝ) ≤ p₀) (ht₀ : (0 : ℝ) < t₀) (hQm : (0 : ℝ) ≤ Qm) (hDm : (0 : ℝ) < Dm)
    (hQ : ∀ p ∈ Ioc (p₀ : ℝ) p₁, ∀ t ∈ Ioc (t₀ : ℝ) t₁, |shearQuartic p t| ≤ Qm)
    (hD : ∀ p ∈ Ioc (p₀ : ℝ) p₁, ∀ t ∈ Ioc (t₀ : ℝ) t₁,
      (Dm : ℝ) ≤ ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal (shearStripMass t₀ t₁ p₀ p₁ Qm Dm) := by
  refine (lintegral_enorm_shearDifference_le_strip (D := 2 * p₁ * Qm / Dm) hp
    (div_nonneg (mul_nonneg (by linarith) hQm) hDm.le) fun p hp' t ht ↦
      abs_shearDifference_le_strip (hp₀.trans hp'.1.le) hp'.2 (ht₀.trans ht.1) (hQ p hp' t ht) hDm
        (hD p hp' t ht)).trans_eq ?_
  simp only [shearStripMass]
  push_cast
  ring_nf

/-- **Soundness of the slab mass.** -/
theorem lintegral_le_shearSlabMass {t₀ t₁ : ℚ} {N : ℤ} (h : shearSlabMass t₀ t₁ = some N) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearSlabMass at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht₀, ht⟩, hpa1⟩, hab⟩, hpa2⟩, hQa⟩, hQb⟩, hqab⟩, hqa⟩, hQqb⟩,
    h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := hck
  simp only [Option.some.injEq] at h
  subst h
  set pa := roundDownRel (1 + shearUpperGap t₀ * (1 - 1 / 2 ^ 12))
  set pb := roundUpRel (1 + shearUpperGap t₁ * (1 + 1 / 2 ^ 12))
  set qa := max 0 (roundDownRel (1 - shearLowerGap t₁ * (1 + 1 / 2 ^ 12)))
  set qb := max 0 (min 1 (roundUpRel (1 - shearLowerGap t₀ * (1 - 1 / 2 ^ 12))))
  have hqa0 : 0 ≤ qa := le_max_left _ _
  have hqb1 : qb ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ht' : (t₀ : ℝ) ≤ t₁ := by exact_mod_cast ht
  have ht₁' : (0 : ℝ) < t₁ := ht₀'.trans_le ht'
  have hpa1' : (1 : ℝ) < pa := by exact_mod_cast hpa1
  have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
  have hpa2' : (t₁ : ℝ) ^ 2 + 1 ≤ (pa : ℝ) ^ 2 := by exact_mod_cast hpa2
  have hqa0' : (0 : ℝ) ≤ qa := by exact_mod_cast hqa0
  have hqab' : (qa : ℝ) ≤ qb := by exact_mod_cast hqab
  have hqb1' : (qb : ℝ) ≤ 1 := by exact_mod_cast hqb1
  have cQ : ∀ x y : ℚ, ((shearQuarticRat x y : ℚ) : ℝ) = shearQuartic x y := cast_shearQuarticRat
  have hQa' : shearQuartic pa t₀ ≤ 0 := by rw [← cQ]; exact_mod_cast hQa
  have hQb' : 0 ≤ shearQuartic pb t₁ := by rw [← cQ]; exact_mod_cast hQb
  have hQqb' : shearQuartic qb t₀ ≤ 0 := by rw [← cQ]; exact_mod_cast hQqb
  set m := shearSlabMassPieces t₀ t₁ pa pb qa qb with hm
  -- piece 1: the left zero region
  have b₁ : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (0 : ℝ) qa, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal m.1 := by
    rcases hqa with hz | hz
    · rw [hz]
      simp
    · have hz' : 0 ≤ shearQuartic qa t₁ := by rw [← cQ]; exact_mod_cast hz
      have hΔ : ∀ p ∈ Icc (0 : ℝ) qa, ∀ t ∈ Icc (t₀ : ℝ) t₁, shearDifference p t ≤ 0 :=
        fun p hp t ht'' ↦ shearDifference_nonpos_of_shearQuartic_nonneg hp.1
          (ht₀'.trans_le ht''.1) (hz'.trans (shearQuartic_le_of_left (hqab'.trans hqb1') hp.1
            hp.2 (ht₀'.le.trans ht''.1) ht''.2))
      have hlow := shearMassLow_le_integral_integral_shearDifference (p₀ := 0) (p₁ := qa)
        le_rfl hqa0 (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (by linarith)) ht₀ ht
      rw [lintegral_enorm_shearDifference_eq_of_nonpos hqa0' ht₀' ht' hΔ]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [hm, shearSlabMassPieces]
      push_cast at hlow ⊢
      linarith
  -- piece 2: the left strip
  have b₂ : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (qa : ℝ) qb, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal m.2.1 := by
    set Dm : ℚ := ((qa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((1 - qb) ^ 2 + t₀ ^ 2) ^ 2 with hDm
    set Qm : ℚ := max (max 0 (shearQuarticRat qa t₀)) (-shearQuarticRat qb t₁) with hQm
    refine lintegral_le_shearStripMass hqab' hqa0' ht₀'
      (by exact_mod_cast le_max_of_le_left (le_max_left _ _))
      (by exact_mod_cast (show (0 : ℚ) < Dm by positivity)) (fun p hp t ht'' ↦ ?_)
      fun p hp t ht'' ↦ ?_
    · have hp0 : 0 ≤ p := hqa0'.trans hp.1.le
      have hu : shearQuartic p t ≤ shearQuartic qa t₀ :=
        shearQuartic_le_of_left (hp.2.trans hqb1') hqa0' hp.1.le ht₀'.le ht''.1.le
      have hl : shearQuartic qb t₁ ≤ shearQuartic p t :=
        shearQuartic_le_of_left hqb1' hp0 hp.2 (ht₀'.trans ht''.1).le ht''.2
      push_cast
      rw [cQ, cQ, abs_le]
      exact ⟨by linarith [le_max_right (max 0 (shearQuartic qa t₀)) (-shearQuartic qb t₁)],
        le_max_of_le_left (le_max_of_le_right hu)⟩
    · have e1 : ((qa : ℝ) + 1) ^ 2 + t₀ ^ 2 ≤ (p + 1) ^ 2 + t ^ 2 := by
        nlinarith [ht''.1, hp.1]
      have e2 : (1 - (qb : ℝ)) ^ 2 + t₀ ^ 2 ≤ (p - 1) ^ 2 + t ^ 2 := by
        nlinarith [ht''.1, hp.2]
      push_cast
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) e1 2)
        (pow_le_pow_left₀ (by positivity) e2 2) (by positivity) (by positivity)
  -- piece 3: the left cells region, where `Δ ≥ 0`
  have b₃ : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (qb : ℝ) 1, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal m.2.2.1 := by
    have hΔ : ∀ p ∈ Icc (qb : ℝ) 1, ∀ t ∈ Icc (t₀ : ℝ) t₁, 0 ≤ shearDifference p t :=
      fun p hp t ht'' ↦ shearDifference_nonneg_of_nonneg (hqa0'.trans (hqab'.trans hp.1))
        (ht₀'.trans_le ht''.1) ((shearQuartic_le_max (hqa0'.trans hqab') hp ht₀'.le ht''.1).trans
          (max_le hQqb' (shearQuartic_one_nonpos _)))
    have hhigh := integral_integral_shearDifference_le_shearMassHigh (p₀ := qb) (p₁ := 1)
      (hqa0.trans hqab) hqb1 (by rw [sub_self, mul_zero]) ht₀ ht
    rw [lintegral_enorm_shearDifference_eq_of_nonneg hqb1' ht₀' ht' hΔ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hm, shearSlabMassPieces]
    push_cast at hhigh
    exact hhigh
  -- piece 4: the right cells region, where `Δ ≥ 0`
  have b₄ : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (1 : ℝ) pa, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal m.2.2.2.1 := by
    have hΔ : ∀ p ∈ Icc (1 : ℝ) pa, ∀ t ∈ Icc (t₀ : ℝ) t₁, 0 ≤ shearDifference p t :=
      fun p hp t ht'' ↦ shearDifference_nonneg_of_nonneg (zero_le_one.trans hp.1)
        (ht₀'.trans_le ht''.1) ((shearQuartic_le_max zero_le_one hp ht₀'.le ht''.1).trans
          (max_le (shearQuartic_one_nonpos _) hQa'))
    have hhigh := integral_integral_shearDifference_le_shearMassHigh (p₀ := 1) (p₁ := pa)
      zero_le_one hpa1.le (by rw [sub_self, zero_mul]) ht₀ ht
    rw [lintegral_enorm_shearDifference_eq_of_nonneg hpa1'.le ht₀' ht' hΔ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hm, shearSlabMassPieces]
    push_cast at hhigh
    exact hhigh
  -- piece 5: the right strip
  have b₅ : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (pa : ℝ) pb, ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal m.2.2.2.2.1 := by
    set Dm : ℚ := ((pa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((pa - 1) ^ 2 + t₀ ^ 2) ^ 2 with hDm
    set Qm : ℚ := max (max 0 (-shearQuarticRat pa t₁)) (shearQuarticRat pb t₀) with hQm
    refine lintegral_le_shearStripMass hab' (by linarith) ht₀'
      (by exact_mod_cast le_max_of_le_left (le_max_left _ _))
      (by exact_mod_cast (show (0 : ℚ) < Dm by positivity)) (fun p hp t ht'' ↦ ?_)
      fun p hp t ht'' ↦ ?_
    · have ht0 : 0 < t := ht₀'.trans ht''.1
      have hl : shearQuartic pa t₁ ≤ shearQuartic p t :=
        shearQuartic_le_of_right hpa2' (by linarith [hp.1]) hp.1.le ht0.le ht''.2
      have hsq : t ^ 2 + 1 ≤ p ^ 2 := by
        have h1 : t ^ 2 ≤ (t₁ : ℝ) ^ 2 := pow_le_pow_left₀ ht0.le ht''.2 2
        have h2 : (pa : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by linarith [hp.1]) hp.1.le 2
        linarith
      have hu : shearQuartic p t ≤ shearQuartic pb t₀ :=
        (shearQuartic_le_of_le ht₀'.le ht''.1.le).trans (shearQuartic_le_of_right
          (by nlinarith [ht''.1]) (by linarith [hp.1]) hp.2 ht₀'.le le_rfl)
      push_cast
      rw [cQ, cQ, abs_le]
      exact ⟨by linarith [le_max_left (max 0 (-shearQuartic pa t₁)) (shearQuartic pb t₀),
        le_max_right (0 : ℝ) (-shearQuartic pa t₁)], le_max_of_le_right hu⟩
    · have e1 : ((pa : ℝ) + 1) ^ 2 + t₀ ^ 2 ≤ (p + 1) ^ 2 + t ^ 2 := by
        nlinarith [ht''.1, hp.1]
      have e2 : ((pa : ℝ) - 1) ^ 2 + t₀ ^ 2 ≤ (p - 1) ^ 2 + t ^ 2 := by
        nlinarith [ht''.1, hp.1]
      push_cast
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) e1 2)
        (pow_le_pow_left₀ (by positivity) e2 2) (by positivity) (by positivity)
  -- piece 6: the far region
  have b₆ : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (pb : ℝ), ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal m.2.2.2.2.2 := by
    have hpb2 : (t₁ : ℝ) ^ 2 + 1 ≤ (pb : ℝ) ^ 2 :=
      hpa2'.trans (pow_le_pow_left₀ (by linarith) hab' 2)
    have hΔ : ∀ p ∈ Ici (pb : ℝ), ∀ t ∈ Icc (t₀ : ℝ) t₁, shearDifference p t ≤ 0 :=
      fun p hp t ht'' ↦ shearDifference_nonpos_of_shearQuartic_nonneg (by linarith [hp.out])
        (ht₀'.trans_le ht''.1) (hQb'.trans (shearQuartic_le_of_right hpb2 (by linarith) hp
          (ht₀'.le.trans ht''.1) ht''.2))
    rw [lintegral_enorm_shearDifference_far_eq (by linarith) ht₀' ht' hΔ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hm, shearSlabMassPieces]
    exact le_shearFarHigh (lt_of_lt_of_le hpa1 hab) ht₀.le ht
  -- the six pieces cover `p > 0`
  have hsub : Ioi (0 : ℝ) ⊆ Ioc (0 : ℝ) qa ∪ Ioc (qa : ℝ) qb ∪ Ioc (qb : ℝ) 1 ∪
      Ioc (1 : ℝ) pa ∪ Ioc (pa : ℝ) pb ∪ Ioi (pb : ℝ) := by
    rw [Ioc_union_Ioc_eq_Ioc hqa0' hqab', Ioc_union_Ioc_eq_Ioc (hqa0'.trans hqab') hqb1',
      Ioc_union_Ioc_eq_Ioc zero_le_one hpa1'.le, Ioc_union_Ioc_eq_Ioc (by linarith) hab',
      Ioc_union_Ioi_eq_Ioi (by linarith)]
  have hU : ∀ S S' : Set ℝ, ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in S ∪ S', ‖shearDifference p t‖ₑ ≤
      (∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in S, ‖shearDifference p t‖ₑ) +
        ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in S', ‖shearDifference p t‖ₑ := fun S S' ↦ by
    rw [← lintegral_add_left (measurable_lintegral_enorm_shearDifference S)]
    exact lintegral_mono fun t ↦ lintegral_union_le _ _ _
  have c₁ : (0 : ℝ) ≤ m.1 := by exact_mod_cast h₁
  have c₂ : (0 : ℝ) ≤ m.2.1 := by exact_mod_cast h₂
  have c₃ : (0 : ℝ) ≤ m.2.2.1 := by exact_mod_cast h₃
  have c₄ : (0 : ℝ) ≤ m.2.2.2.1 := by exact_mod_cast h₄
  have c₅ : (0 : ℝ) ≤ m.2.2.2.2.1 := by exact_mod_cast h₅
  calc ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ
      ≤ ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (0 : ℝ) qa ∪ Ioc (qa : ℝ) qb ∪ Ioc (qb : ℝ) 1 ∪
          Ioc (1 : ℝ) pa ∪ Ioc (pa : ℝ) pb ∪ Ioi (pb : ℝ), ‖shearDifference p t‖ₑ :=
        lintegral_mono fun t ↦ lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal m.1 + ENNReal.ofReal m.2.1 + ENNReal.ofReal m.2.2.1 +
          ENNReal.ofReal m.2.2.2.1 + ENNReal.ofReal m.2.2.2.2.1 + ENNReal.ofReal m.2.2.2.2.2 := by
        refine (hU _ _).trans (add_le_add ?_ b₆)
        refine (hU _ _).trans (add_le_add ?_ b₅)
        refine (hU _ _).trans (add_le_add ?_ b₄)
        refine (hU _ _).trans (add_le_add ?_ b₃)
        exact (hU _ _).trans (add_le_add b₁ b₂)
    _ = ENNReal.ofReal ((m.1 + m.2.1 + m.2.2.1 + m.2.2.2.1 + m.2.2.2.2.1 + m.2.2.2.2.2 : ℚ) :
          ℝ) := by
        push_cast
        rw [ENNReal.ofReal_add (by positivity) (by exact_mod_cast h₆),
          ENNReal.ofReal_add (by positivity) c₅, ENNReal.ofReal_add (by positivity) c₄,
          ENNReal.ofReal_add (by positivity) c₃, ENNReal.ofReal_add c₁ c₂]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 _)

end IncompressibleFlow.SharpHolder
