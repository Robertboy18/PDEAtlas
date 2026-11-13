/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowTransport
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMapBounds

/-!
# Bounds of the horizontal transport map of the inner rows

On `p² + 3q² ≤ 1` the row map is `T_y(p, q) = R(p, q)^{1/2}` with
`R(p, q) = (1 + q²)(1 - 3q² - p²)/(1 + q² - p²)` (`horizontalShearMap_sq_eq`). The differences of
`R` in `p` and in `q` factor (`horizontalShearMap_sq_sub_left`, `horizontalShearMap_sq_sub_right`),
which gives the affine majorant `T_y(p, q) - p ≤ (T₁ - p₀) - (1 + λ)(p - p₀) - μ (q - q₀)` on a
rectangle (`horizontalShearMap_sub_le_affine`). The inner region `D₁ = {0 < p < h_c^-(q)}` lies in
`p² + 3q² < 1` (`sq_add_three_mul_sq_lt_one`); a point `p_b ∈ [0, 1]` with `Q(p_b, q) ≤ 0` bounds
`h_c^-(q)` from above (`lowerShearThreshold_le_of_shearQuartic_nonpos`), and `h_c^-(q) ≤ 1 - q`.

## Main results

* `horizontalShearMap_sq_eq`: on `p² + 3q² ≤ 1`, `T_y(p, q)² = R(p, q)`.
* `horizontalShearMap_sq_sub_left`, `horizontalShearMap_sq_sub_right`: the factored differences
  of `R` in `p` and in `q`.
* `horizontalShearMap_sub_le_affine`: the affine majorant of `T_y - p` on a rectangle.
* `sq_add_three_mul_sq_lt_one`: on `D₁`, `p² + 3q² < 1`.
* `lowerShearThreshold_le_of_shearQuartic_nonpos`: a point `p_b ∈ [0, 1]` with `Q(p_b, q) ≤ 0`
  lies at or above `h_c^-(q)`, for `3q² ≤ 1`.
* `lowerShearThreshold_le_one_sub`, `lowerShearThreshold_eq_zero`: `h_c^-(q) ≤ 1 - q` for
  `0 ≤ q ≤ 1`, and `h_c^-(q) = 0` for `3q² ≥ 1`.
* `shearDifference_nonpos_of_shearQuartic_nonneg`: where `Q ≥ 0` and `p ≥ 0`, `Δ ≤ 0`.
-/

@[expose] public section

noncomputable section

open Set

namespace IncompressibleFlow.SharpHolder

/-- The row map as the square root of `R(p, q) = (1 + q²)(1 - 3q² - p²)/(1 + q² - p²)`. -/
theorem horizontalShearMap_eq_sqrt (p q : ℝ) :
    horizontalShearMap p q =
      Real.sqrt ((1 + q ^ 2) * (1 - 3 * q ^ 2 - p ^ 2) / (1 + q ^ 2 - p ^ 2)) := by
  rw [horizontalShearMap, horizontalShearMap_radicand]
  congr 1
  rw [← neg_div_neg_eq]
  ring_nf

/-- On `p² + 3q² ≤ 1`, `T_y(p, q)² = R(p, q)`. -/
theorem horizontalShearMap_sq_eq {p q : ℝ} (h : p ^ 2 + 3 * q ^ 2 ≤ 1) :
    horizontalShearMap p q ^ 2 = (1 + q ^ 2) * (1 - 3 * q ^ 2 - p ^ 2) / (1 + q ^ 2 - p ^ 2) := by
  rw [horizontalShearMap_eq_sqrt]
  refine Real.sq_sqrt (div_nonneg (mul_nonneg (by positivity) (by linarith)) ?_)
  nlinarith [sq_nonneg q]

/-- The difference of `R` in `p`. -/
theorem horizontalShearMap_sq_sub_left {p P q : ℝ} (hq : 0 < q) (h : p ^ 2 + 3 * q ^ 2 ≤ 1)
    (hP : P ^ 2 + 3 * q ^ 2 ≤ 1) :
    horizontalShearMap p q ^ 2 - horizontalShearMap P q ^ 2 =
      4 * q ^ 2 * (1 + q ^ 2) * (P ^ 2 - p ^ 2) /
        ((1 + q ^ 2 - p ^ 2) * (1 + q ^ 2 - P ^ 2)) := by
  rw [horizontalShearMap_sq_eq h, horizontalShearMap_sq_eq hP]
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have h1 : 1 + q ^ 2 - p ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 + q ^ 2 - P ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- The difference of `R` in `q`. -/
theorem horizontalShearMap_sq_sub_right {p q Q : ℝ} (hq : 0 < q) (hQ0 : 0 < Q)
    (h : p ^ 2 + 3 * q ^ 2 ≤ 1) (hQ : p ^ 2 + 3 * Q ^ 2 ≤ 1) :
    horizontalShearMap p q ^ 2 - horizontalShearMap p Q ^ 2 =
      (Q ^ 2 - q ^ 2) * (3 + 4 * p ^ 2 * (1 - p ^ 2) /
        ((1 + q ^ 2 - p ^ 2) * (1 + Q ^ 2 - p ^ 2))) := by
  rw [horizontalShearMap_sq_eq h, horizontalShearMap_sq_eq hQ]
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have hQ2 : 0 < Q ^ 2 := pow_pos hQ0 2
  have h1 : 1 + q ^ 2 - p ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 + Q ^ 2 - p ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- If `(A - B)(A + B) = X ≥ 0` with `A, B ≥ 0`, `A + B ≤ 2T`, `T > 0` and `κ (2T) ≤ X`, then
`κ ≤ A - B`. -/
private theorem le_sub_of_sq_sub {A B T X κ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A + B ≤ 2 * T)
    (hT : 0 < T) (hX : (A - B) * (A + B) = X) (hX0 : 0 ≤ X) (hκ : κ * (2 * T) ≤ X) :
    κ ≤ A - B := by
  have hge : 0 ≤ A - B := by
    rcases eq_or_lt_of_le (add_nonneg hA hB) with h0 | h0
    · nlinarith
    · by_contra hc
      push Not at hc
      nlinarith
  have : X ≤ (A - B) * (2 * T) := by
    rw [← hX]
    exact mul_le_mul_of_nonneg_left hAB hge
  have h2T : 0 < 2 * T := by linarith
  exact le_of_mul_le_mul_right (hκ.trans this) h2T

/-- If `(B - C)(B + C) = X ≥ 0` with `B ≥ 0`, then `C ≤ B`. -/
private theorem le_of_sq_sub {B C X : ℝ} (hB : 0 ≤ B) (h : (B - C) * (B + C) = X)
    (hX : 0 ≤ X) : C ≤ B := by
  by_contra hlt
  push Not at hlt
  have : (B - C) * (B + C) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  linarith

/-- **The affine majorant of the row map.** On `[p₀, p₁] × [q₀, q₁]` with `0 ≤ p₀`, `p₁ ≤ 1`,
`q₀ > 0`, `T(p₀, q₀) ≤ T₁`, `T₁ > 0`, and slopes `λ, μ` with
`λ (1 + q₀² - p₀²)² 2T₁ ≤ 8 p₀ q₀² (1 + q₀²)` and
`μ 2T₁ ≤ 2 q₀ (3 + 4 p₀² (1 - p₁²)/(1 + q₁² - p₀²)²)`, every point with `p² + 3q² ≤ 1` has
`T(p, q) - p ≤ (T₁ - p₀) - (1 + λ)(p - p₀) - μ (q - q₀)`. -/
theorem horizontalShearMap_sub_le_affine {p₀ p₁ q₀ q₁ T₁ l m : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : p₁ ≤ 1)
    (hq₀ : 0 < q₀) (hT : horizontalShearMap p₀ q₀ ≤ T₁) (hT₁ : 0 < T₁)
    (hl' : l * ((1 + q₀ ^ 2 - p₀ ^ 2) ^ 2 * (2 * T₁)) ≤ 8 * p₀ * q₀ ^ 2 * (1 + q₀ ^ 2))
    (hm' : m * (2 * T₁) ≤ 2 * q₀ * (3 + 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2))
    {p q : ℝ} (hp : p ∈ Icc p₀ p₁) (hq : q ∈ Icc q₀ q₁) (hD : p ^ 2 + 3 * q ^ 2 ≤ 1) :
    horizontalShearMap p q - p ≤ (T₁ - p₀) - (1 + l) * (p - p₀) - m * (q - q₀) := by
  obtain ⟨hpa, hpb⟩ := hp
  obtain ⟨hqa, hqb⟩ := hq
  have hp0 : 0 ≤ p := hp₀.trans hpa
  have hq0 : 0 < q := hq₀.trans_le hqa
  have hpp : p₀ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hp₀ hpa 2
  have hqq : q₀ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hq₀.le hqa 2
  have hpq₀ : p ^ 2 + 3 * q₀ ^ 2 ≤ 1 := by linarith
  have hp₀q₀ : p₀ ^ 2 + 3 * q₀ ^ 2 ≤ 1 := by linarith
  set A := horizontalShearMap p₀ q₀
  set B := horizontalShearMap p q₀
  set C := horizontalShearMap p q
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hp1 : p ≤ 1 := hpb.trans hp₁
  have hpsq1 : p ^ 2 ≤ 1 := by nlinarith
  have hp₁sq : p₁ ^ 2 ≤ 1 := by nlinarith
  -- the step in `p` along the row `q₀`
  have hq₀2 : 0 < q₀ ^ 2 := pow_pos hq₀ 2
  have hden : 0 < 1 + q₀ ^ 2 - p₀ ^ 2 := by linarith
  have hden' : 0 < 1 + q₀ ^ 2 - p ^ 2 := by linarith
  have hd₁ : 0 < 1 + q ^ 2 - p ^ 2 := by linarith
  have hdp := horizontalShearMap_sq_sub_left hq₀ hp₀q₀ hpq₀
  have hXp : 0 ≤ 4 * q₀ ^ 2 * (1 + q₀ ^ 2) * (p ^ 2 - p₀ ^ 2) /
      ((1 + q₀ ^ 2 - p₀ ^ 2) * (1 + q₀ ^ 2 - p ^ 2)) :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_pos hden hden').le
  have hdp' : (A - B) * (A + B) = 4 * q₀ ^ 2 * (1 + q₀ ^ 2) * (p ^ 2 - p₀ ^ 2) /
      ((1 + q₀ ^ 2 - p₀ ^ 2) * (1 + q₀ ^ 2 - p ^ 2)) := by
    rw [← hdp]
    ring
  have hAB : B ≤ A := le_of_sq_sub hA hdp' hXp
  have hdq := horizontalShearMap_sq_sub_right hq₀ hq0 hpq₀ hD
  have hE : 0 ≤ 4 * p ^ 2 * (1 - p ^ 2) / ((1 + q₀ ^ 2 - p ^ 2) * (1 + q ^ 2 - p ^ 2)) :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_pos hden' hd₁).le
  have hXq : 0 ≤ (q ^ 2 - q₀ ^ 2) * (3 + 4 * p ^ 2 * (1 - p ^ 2) /
      ((1 + q₀ ^ 2 - p ^ 2) * (1 + q ^ 2 - p ^ 2))) :=
    mul_nonneg (by linarith) (by linarith)
  have hdq' : (B - C) * (B + C) = (q ^ 2 - q₀ ^ 2) * (3 + 4 * p ^ 2 * (1 - p ^ 2) /
      ((1 + q₀ ^ 2 - p ^ 2) * (1 + q ^ 2 - p ^ 2))) := by
    rw [← hdq]
    ring
  have hBC : C ≤ B := le_of_sq_sub hB hdq' hXq
  have key₁ : l * (p - p₀) ≤ A - B := by
    refine le_sub_of_sq_sub hA hB (by linarith) hT₁ hdp' hXp ?_
    have h1 : (p - p₀) * (2 * p₀) ≤ p ^ 2 - p₀ ^ 2 := by linarith [sq_nonneg (p - p₀)]
    calc l * (p - p₀) * (2 * T₁)
        ≤ (p - p₀) * (2 * p₀) * (4 * q₀ ^ 2 * (1 + q₀ ^ 2)) /
            ((1 + q₀ ^ 2 - p₀ ^ 2) * (1 + q₀ ^ 2 - p₀ ^ 2)) := by
          rw [le_div_iff₀ (by positivity)]
          linarith [mul_le_mul_of_nonneg_left hl' (sub_nonneg.2 hpa)]
      _ ≤ (p ^ 2 - p₀ ^ 2) * (4 * q₀ ^ 2 * (1 + q₀ ^ 2)) /
            ((1 + q₀ ^ 2 - p₀ ^ 2) * (1 + q₀ ^ 2 - p ^ 2)) :=
          div_le_div₀ (mul_nonneg (by linarith) (by positivity)) (by gcongr) (mul_pos hden hden')
            (by gcongr)
      _ = _ := by ring
  have key₂ : m * (q - q₀) ≤ B - C := by
    refine le_sub_of_sq_sub hB hC (by linarith) hT₁ hdq' hXq ?_
    have hq₁ : q ^ 2 ≤ q₁ ^ 2 := pow_le_pow_left₀ hq0.le hqb 2
    have hpp₁ : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ hp0 hpb 2
    have hD₁ : 0 < 1 + q₁ ^ 2 - p₀ ^ 2 := by linarith
    have hE' : 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2 ≤
        4 * p ^ 2 * (1 - p ^ 2) / ((1 + q₀ ^ 2 - p ^ 2) * (1 + q ^ 2 - p ^ 2)) :=
      div_le_div₀ (mul_nonneg (by positivity) (by linarith))
        (mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)) (mul_pos hden' hd₁)
        ((mul_le_mul (by linarith) (by linarith) hd₁.le hD₁.le).trans_eq (sq _).symm)
    have hm2 : m * (2 * T₁) ≤ 2 * q₀ * (3 + 4 * p ^ 2 * (1 - p ^ 2) /
        ((1 + q₀ ^ 2 - p ^ 2) * (1 + q ^ 2 - p ^ 2))) :=
      hm'.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    linarith [mul_le_mul_of_nonneg_left hm2 (sub_nonneg.2 hqa),
      mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (q - q₀)] :
        (q - q₀) * (2 * q₀) ≤ q ^ 2 - q₀ ^ 2) (by linarith : (0 : ℝ) ≤ 3 + 4 * p ^ 2 *
          (1 - p ^ 2) / ((1 + q₀ ^ 2 - p ^ 2) * (1 + q ^ 2 - p ^ 2)))]
  linarith

/-! ### The inner region -/

/-- On `D₁`, `p² + 3q² < 1`. -/
theorem sq_add_three_mul_sq_lt_one {p q : ℝ} (hq : 0 < q) (h3 : 3 * q ^ 2 < 1) (hp : 0 ≤ p)
    (hlt : p < lowerShearThreshold q) : p ^ 2 + 3 * q ^ 2 < 1 := by
  have hsq := lowerShearThreshold_sq h3.le
  have h1 : p ^ 2 < lowerShearThreshold q ^ 2 := pow_lt_pow_left₀ hlt hp two_ne_zero
  have h2 : 2 * q ≤ Real.sqrt (q ^ 2 + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith

/-- `h_c^-(q) ≤ 1 - q` for `0 ≤ q ≤ 1`. -/
theorem lowerShearThreshold_le_one_sub {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    lowerShearThreshold q ≤ 1 - q := by
  rw [lowerShearThreshold, Real.sqrt_le_left (by linarith)]
  have : 1 ≤ Real.sqrt (q ^ 2 + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith

/-- A point `p_b ∈ [0, 1]` with `Q(p_b, q) ≤ 0` lies at or above `h_c^-(q)`, for `3q² ≤ 1`. -/
theorem lowerShearThreshold_le_of_shearQuartic_nonpos {p q : ℝ} (hq : 0 ≤ q)
    (h3 : 3 * q ^ 2 ≤ 1) (hp : 0 ≤ p) (h : shearQuartic p q ≤ 0) : lowerShearThreshold q ≤ p := by
  by_contra hlt
  push Not at hlt
  have hsq := lowerShearThreshold_sq h3
  have h1 : p ^ 2 < lowerShearThreshold q ^ 2 := pow_lt_pow_left₀ hlt hp two_ne_zero
  rw [shearQuartic_eq_upper_lower] at h
  have hs := Real.sqrt_nonneg (q ^ 2 + 1)
  have hu : p ^ 2 - (q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1)) < 0 := by
    nlinarith [mul_nonneg hq hs]
  have hv : p ^ 2 - (q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1)) < 0 := by linarith
  have := mul_pos_of_neg_of_neg hu hv
  linarith

/-- For `3q² ≥ 1`, `h_c^-(q) = 0`: the inner region is empty. -/
theorem lowerShearThreshold_eq_zero {q : ℝ} (hq : 0 ≤ q) (h3 : 1 ≤ 3 * q ^ 2) :
    lowerShearThreshold q = 0 := by
  rw [lowerShearThreshold, Real.sqrt_eq_zero']
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q ^ 2 + 1 by positivity)
  have h2 : Real.sqrt (q ^ 2 + 1) ≤ 2 * q := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h1 : 1 ≤ Real.sqrt (q ^ 2 + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (q ^ 2 + 1))]

/-- Where `Q ≥ 0` and `p ≥ 0`, `Δ ≤ 0`. -/
theorem shearDifference_nonpos_of_shearQuartic_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (h : 0 ≤ shearQuartic p q) : shearDifference p q ≤ 0 := by
  have h₁ : (p + 1) ^ 2 + q ^ 2 ≠ 0 := by positivity
  have h₂ : (p - 1) ^ 2 + q ^ 2 ≠ 0 := by positivity
  rw [shearDifference_eq h₁ h₂]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

end IncompressibleFlow.SharpHolder
