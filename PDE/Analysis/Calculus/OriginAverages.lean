/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Taylor identities near the origin and weighted averages

Chen and Hou bound a function `F` near `0` by averages of its third derivatives. Write
`E(G, i)(x) = ∫₀¹ G(x t) (1 - t)^i dt`, so that `∫₀ˣ G(z) (x - z)^i dz = x^{i+1} E(G, i)(x)`; this
normalisation of the quotient `x^{-(i+1)} ∫₀ˣ G(z) (x - z)^i dz` extends to `x = 0` with value
`G(0) / (i + 1)`.

In two variables, if `F(0, s) = ∂_y F(0, 0) = 0` along the `y`-axis in the sense
`∂_y² F(0, s) = 0`, `∂_y F(0, 0) = 0`, `∂ₓ∂_y F(0, 0) = 0` and
`F(0, 0) = ∂ₓ F(0, 0) = ∂ₓ² F(0, 0) = 0` (all true for `F` odd in `x` with `∇ᵏF(0) = 0`,
`k ≤ 2`), then
`F(x, y) = ∫₀ʸ (y - s) ∫₀ˣ F_{xyy}(t, s) dt ds + y ∫₀ˣ (x - t) F_{xxy}(t, 0) dt
+ ½ ∫₀ˣ (x - t)² F_{xxx}(t, 0) dt`, the identity displayed before (8.64), and the bound with
constant derivative bounds follows. Keeping the averages gives the inequality before (8.64),
with `E_{xy}(G, i, j)(x, y) = ∫₀¹∫₀¹ G(x t, y s)(1 - t)^i (1 - s)^j dt ds`; it needs the
absolute double integral to be integrable, which joint continuity gives.

Piecewise bounds of `f` on the cells `[(i - 1) h, i h]` bound the average; this is the
"piecewise bound for powers" of Sec 8.5, written with `j = m - i`.

## Main definitions

* `weightedAverage`: the normalized average `E(G, i)(x) = ∫₀¹ G(x t) (1 - t)^i dt`.
* `doubleWeightedAverage`: the normalized double average `E_{xy}(G, i, j)(x, y)`.

## Main results

* `integral_mul_sub_pow_eq`: `∫₀ˣ G(z) (x - z)^i dz = x^{i+1} E(G, i)(x)`.
* `taylor_two_integral`: Taylor's formula of order two with integral remainder for a derivative
  chain.
* `taylor_three_integral`: Taylor's formula of order three with integral remainder for a
  derivative chain.
* `eq_taylor_origin`: the identity before (8.64) for `F(x, y)`.
* `abs_le_taylor_origin`: the bound of `|F(x, y)|` from constant bounds of the third derivatives.
* `abs_le_taylor_origin_averages`: `|F(x, y)| ≤ x y² E_{xy}(|F_{xyy}|, 0, 1) +
  x² y E(|F_{xxy}(·, 0)|, 1)(x) + x³/2 E(|F_{xxx}(·, 0)|, 2)(x)`.
* `weightedAverage_le_piecewise`: for `x ∈ [(m - 1) h, m h]`, `E(f, k)(x) ≤
  ∑_{j < m} max(f_j, f_{j+1}) ((m - j)^{k+1} - (m - j - 1)^{k+1}) / ((k + 1) m^{k+1})`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.5, the identity and the bound before (8.64), and
  (8.66). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open Set intervalIntegral MeasureTheory

/-- The normalized weighted average `∫₀¹ G(x t) (1 - t)^i dt`. -/
noncomputable def weightedAverage (G : ℝ → ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, G (x * t) * (1 - t) ^ i

/-- **The average as a normalized integral:** `∫₀ˣ G(z) (x - z)^i dz = x^{i+1} E(G, i)(x)`
(Supp II Sec 8.5, `z = x t`). -/
theorem integral_mul_sub_pow_eq (G : ℝ → ℝ) (i : ℕ) (x : ℝ) :
    ∫ z in (0 : ℝ)..x, G z * (x - z) ^ i = x ^ (i + 1) * weightedAverage G i x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [weightedAverage]
  · unfold weightedAverage
    have h := intervalIntegral.integral_comp_mul_left (fun z ↦ G z * (x - z) ^ i) hx
      (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at h
    have h' : ∫ z in (0 : ℝ)..x, G z * (x - z) ^ i =
        x * ∫ t in (0 : ℝ)..1, G (x * t) * (x - x * t) ^ i := by
      rw [h, smul_eq_mul]
      field_simp
    rw [h', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [show x - x * t = x * (1 - t) by ring, mul_pow, pow_succ]
    ring

/-- **Taylor's formula of order two with integral remainder** for a derivative chain:
`g₀(x) = g₀(0) + x g₁(0) + ∫₀ˣ (x - t) g₂(t) dt`. -/
theorem taylor_two_integral {g₀ g₁ g₂ : ℝ → ℝ} {x : ℝ}
    (h₀ : ∀ t ∈ uIcc 0 x, HasDerivAt g₀ (g₁ t) t) (h₁ : ∀ t ∈ uIcc 0 x, HasDerivAt g₁ (g₂ t) t)
    (hc : ContinuousOn g₂ (uIcc 0 x)) :
    g₀ x = g₀ 0 + x * g₁ 0 + ∫ t in (0 : ℝ)..x, (x - t) * g₂ t := by
  have hH : ∀ t ∈ uIcc 0 x,
      HasDerivAt (fun s ↦ g₀ s + (x - s) * g₁ s) ((x - t) * g₂ t) t := by
    intro t ht
    have := (h₀ t ht).fun_add (((hasDerivAt_id' t).const_sub x).fun_mul (h₁ t ht))
    convert this using 1
    ring
  have hint : IntervalIntegrable (fun t ↦ (x - t) * g₂ t) volume 0 x :=
    ((continuousOn_const.sub continuousOn_id).mul hc).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint]
  ring

/-- **Taylor's formula of order three with integral remainder** for a derivative chain:
`g₀(x) = g₀(0) + x g₁(0) + x²/2 g₂(0) + ½ ∫₀ˣ (x - t)² g₃(t) dt`. -/
theorem taylor_three_integral {g₀ g₁ g₂ g₃ : ℝ → ℝ} {x : ℝ}
    (h₀ : ∀ t ∈ uIcc 0 x, HasDerivAt g₀ (g₁ t) t) (h₁ : ∀ t ∈ uIcc 0 x, HasDerivAt g₁ (g₂ t) t)
    (h₂ : ∀ t ∈ uIcc 0 x, HasDerivAt g₂ (g₃ t) t) (hc : ContinuousOn g₃ (uIcc 0 x)) :
    g₀ x = g₀ 0 + x * g₁ 0 + x ^ 2 / 2 * g₂ 0 + 1 / 2 * ∫ t in (0 : ℝ)..x, (x - t) ^ 2 * g₃ t := by
  have hH : ∀ t ∈ uIcc 0 x, HasDerivAt (fun s ↦ g₀ s + (x - s) * g₁ s + (x - s) ^ 2 / 2 * g₂ s)
      ((x - t) ^ 2 / 2 * g₃ t) t := by
    intro t ht
    have hl : HasDerivAt (fun s ↦ x - s) (-1) t := by simpa using (hasDerivAt_id' t).const_sub x
    have := ((h₀ t ht).fun_add (hl.fun_mul (h₁ t ht))).fun_add
      (((hl.fun_pow 2).div_const 2).fun_mul (h₂ t ht))
    convert this using 1
    push_cast
    ring
  have hint : IntervalIntegrable (fun t ↦ (x - t) ^ 2 / 2 * g₃ t) volume 0 x :=
    ((((continuousOn_const.sub continuousOn_id).pow 2).div_const 2).mul hc).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint
  rw [show (∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 * g₃ t) =
      1 / 2 * ∫ t in (0 : ℝ)..x, (x - t) ^ 2 * g₃ t by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring] at h
  linarith

/-- **Supp II Sec 8.5, the identity before (8.64).** Let `F` have the partial derivatives below
along the lines used, with `∂_y² F(0, s) = 0` for `s` between `0` and `y`, `∂_y F(0, 0) =
∂ₓ∂_y F(0, 0) = 0` and `F(0, 0) = ∂ₓ F(0, 0) = ∂ₓ² F(0, 0) = 0`. Then
`F(x, y) = ∫₀ʸ (y - s) ∫₀ˣ F_{xyy}(t, s) dt ds + y ∫₀ˣ (x - t) F_{xxy}(t, 0) dt +
½ ∫₀ˣ (x - t)² F_{xxx}(t, 0) dt`. For `F` odd in `x` with `∇ᵏ F(0) = 0`, `k ≤ 2`, all the vanishing
hypotheses hold. -/
theorem eq_taylor_origin {F Fx Fxx Fxxx Fy Fxy Fxxy Fyy Fxyy : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy₀ : ∀ s ∈ uIcc 0 y, HasDerivAt (F x) (Fy x s) s)
    (hy₁ : ∀ s ∈ uIcc 0 y, HasDerivAt (Fy x) (Fyy x s) s)
    (hcy : ContinuousOn (Fyy x) (uIcc 0 y))
    (hxyy : ∀ s ∈ uIcc 0 y, ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fyy u s) (Fxyy t s) t)
    (hcxyy : ∀ s ∈ uIcc 0 y, ContinuousOn (fun t ↦ Fxyy t s) (uIcc 0 x))
    (hxy₀ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fy u 0) (Fxy t 0) t)
    (hxy₁ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fxy u 0) (Fxxy t 0) t)
    (hcxxy : ContinuousOn (fun t ↦ Fxxy t 0) (uIcc 0 x))
    (hx₀ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ F u 0) (Fx t 0) t)
    (hx₁ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fx u 0) (Fxx t 0) t)
    (hx₂ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fxx u 0) (Fxxx t 0) t)
    (hcxxx : ContinuousOn (fun t ↦ Fxxx t 0) (uIcc 0 x))
    (hFyy : ∀ s ∈ uIcc 0 y, Fyy 0 s = 0) (hFy : Fy 0 0 = 0) (hFxy : Fxy 0 0 = 0)
    (hF : F 0 0 = 0) (hFx : Fx 0 0 = 0) (hFxx : Fxx 0 0 = 0) :
    F x y = (∫ s in (0 : ℝ)..y, (y - s) * ∫ t in (0 : ℝ)..x, Fxyy t s) +
      y * (∫ t in (0 : ℝ)..x, (x - t) * Fxxy t 0) +
      1 / 2 * ∫ t in (0 : ℝ)..x, (x - t) ^ 2 * Fxxx t 0 := by
  have h1 := taylor_two_integral hy₀ hy₁ hcy
  have hinner : ∀ s ∈ uIcc 0 y, ∫ t in (0 : ℝ)..x, Fxyy t s = Fyy x s := by
    intro s hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (hxyy s hs)
      ((hcxyy s hs).intervalIntegrable), hFyy s hs, sub_zero]
  have hcongr : ∫ s in (0 : ℝ)..y, (y - s) * Fyy x s =
      ∫ s in (0 : ℝ)..y, (y - s) * ∫ t in (0 : ℝ)..x, Fxyy t s :=
    intervalIntegral.integral_congr fun s hs ↦ by simp only [hinner s hs]
  have h2 := taylor_two_integral (g₀ := fun u ↦ Fy u 0) hxy₀ hxy₁ hcxxy
  have h3 := taylor_three_integral (g₀ := fun u ↦ F u 0) hx₀ hx₁ hx₂ hcxxx
  simp only [hFy, hFxy, hF, hFx, hFxx, mul_zero, add_zero, zero_add] at h2 h3
  rw [h1, ← hcongr, h2, h3]
  ring

/-- **Supp II Sec 8.5, constant bounds.** Under the hypotheses of `eq_taylor_origin`, for
`x, y ≥ 0` and `|F_{xyy}| ≤ M₁`, `|F_{xxy}(·, 0)| ≤ M₂`, `|F_{xxx}(·, 0)| ≤ M₃` on the relevant
segments, `|F(x, y)| ≤ M₁ x y² / 2 + M₂ x² y / 2 + M₃ x³ / 6`. These are the averages
`E_{xy}(|F_{xyy}|, 0, 1)`, `E_x(|F_{xxy}|, 1)`, `E_x(|F_{xxx}|, 2)` of (8.64) bounded by their
masses `1/2`, `1/2`, `1/3`. -/
theorem abs_le_taylor_origin {F Fx Fxx Fxxx Fy Fxy Fxxy Fyy Fxyy : ℝ → ℝ → ℝ} {x y M₁ M₂ M₃ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy₀ : ∀ s ∈ uIcc 0 y, HasDerivAt (F x) (Fy x s) s)
    (hy₁ : ∀ s ∈ uIcc 0 y, HasDerivAt (Fy x) (Fyy x s) s)
    (hcy : ContinuousOn (Fyy x) (uIcc 0 y))
    (hxyy : ∀ s ∈ uIcc 0 y, ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fyy u s) (Fxyy t s) t)
    (hcxyy : ∀ s ∈ uIcc 0 y, ContinuousOn (fun t ↦ Fxyy t s) (uIcc 0 x))
    (hxy₀ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fy u 0) (Fxy t 0) t)
    (hxy₁ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fxy u 0) (Fxxy t 0) t)
    (hcxxy : ContinuousOn (fun t ↦ Fxxy t 0) (uIcc 0 x))
    (hx₀ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ F u 0) (Fx t 0) t)
    (hx₁ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fx u 0) (Fxx t 0) t)
    (hx₂ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fxx u 0) (Fxxx t 0) t)
    (hcxxx : ContinuousOn (fun t ↦ Fxxx t 0) (uIcc 0 x))
    (hFyy : ∀ s ∈ uIcc 0 y, Fyy 0 s = 0) (hFy : Fy 0 0 = 0) (hFxy : Fxy 0 0 = 0)
    (hF : F 0 0 = 0) (hFx : Fx 0 0 = 0) (hFxx : Fxx 0 0 = 0)
    (hM₁ : ∀ s ∈ uIcc 0 y, ∀ t ∈ uIcc 0 x, |Fxyy t s| ≤ M₁)
    (hM₂ : ∀ t ∈ uIcc 0 x, |Fxxy t 0| ≤ M₂) (hM₃ : ∀ t ∈ uIcc 0 x, |Fxxx t 0| ≤ M₃) :
    |F x y| ≤ M₁ * x * y ^ 2 / 2 + M₂ * x ^ 2 * y / 2 + M₃ * x ^ 3 / 6 := by
  rw [eq_taylor_origin hy₀ hy₁ hcy hxyy hcxyy hxy₀ hxy₁ hcxxy hx₀ hx₁ hx₂ hcxxx hFyy hFy hFxy
    hF hFx hFxx]
  have hux : uIcc 0 x = Icc 0 x := uIcc_of_le hx
  have huy : uIcc 0 y = Icc 0 y := uIcc_of_le hy
  -- the inner integral in `t`
  have hinner : ∀ s ∈ uIcc 0 y, ∫ t in (0 : ℝ)..x, Fxyy t s = Fyy x s := by
    intro s hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (hxyy s hs)
      ((hcxyy s hs).intervalIntegrable), hFyy s hs, sub_zero]
  have hin : ∀ s ∈ Icc 0 y, |∫ t in (0 : ℝ)..x, Fxyy t s| ≤ M₁ * x := by
    intro s hs
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (f := fun t ↦ Fxyy t s) (C := M₁) fun t ht ↦ by
        rw [Real.norm_eq_abs]
        exact hM₁ s (huy ▸ hs) t (uIoc_subset_uIcc ht)
    simpa [Real.norm_eq_abs, abs_of_nonneg hx] using this
  have hgc : ContinuousOn (fun s ↦ ∫ t in (0 : ℝ)..x, Fxyy t s) (Icc 0 y) :=
    (huy ▸ hcy).congr fun s hs ↦ hinner s (huy ▸ hs)
  -- weighted integrals over `[0, b]` with a nonnegative continuous weight
  have hweight {b C : ℝ} (hb : 0 ≤ b) {w g : ℝ → ℝ} (hw : ∀ t ∈ Icc 0 b, 0 ≤ w t)
      (hg : ∀ t ∈ Icc 0 b, |g t| ≤ C) (hwc : ContinuousOn w (Icc 0 b))
      (hgc : ContinuousOn g (Icc 0 b)) :
      |∫ t in (0 : ℝ)..b, w t * g t| ≤ C * ∫ t in (0 : ℝ)..b, w t := by
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs hb).trans ?_
    have hwgc : ContinuousOn (fun t ↦ |w t * g t|) (uIcc 0 b) := by
      rw [uIcc_of_le hb]
      exact (hwc.mul hgc).abs
    have hwc' : ContinuousOn (fun t ↦ C * w t) (uIcc 0 b) := by
      rw [uIcc_of_le hb]
      exact continuousOn_const.mul hwc
    refine intervalIntegral.integral_mono_on hb hwgc.intervalIntegrable hwc'.intervalIntegrable
      fun t ht ↦ ?_
    rw [abs_mul, abs_of_nonneg (hw t ht), mul_comm]
    exact mul_le_mul_of_nonneg_right (hg t ht) (hw t ht)
  have hlin {b : ℝ} : ∫ t in (0 : ℝ)..b, (b - t) = b ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ (b - t) ^ 2 * (-1 / 2))
      (fun t _ ↦ by
        have h := (((hasDerivAt_id' t).const_sub b).fun_pow 2).mul_const (-1 / 2 : ℝ)
        convert h using 1
        push_cast
        ring) ((by fun_prop : Continuous fun t : ℝ ↦ b - t).intervalIntegrable 0 b)]
    ring
  have hquad {b : ℝ} : ∫ t in (0 : ℝ)..b, (b - t) ^ 2 = b ^ 3 / 3 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ (b - t) ^ 3 * (-1 / 3))
      (fun t _ ↦ by
        have h := (((hasDerivAt_id' t).const_sub b).fun_pow 3).mul_const (-1 / 3 : ℝ)
        convert h using 1
        push_cast
        ring) ((by fun_prop : Continuous fun t : ℝ ↦ (b - t) ^ 2).intervalIntegrable 0 b)]
    ring
  have hA := hweight hy (w := fun s ↦ y - s) (fun s hs ↦ by linarith [hs.2]) hin
    (by fun_prop) hgc
  have hB := hweight hx (w := fun t ↦ x - t) (g := fun t ↦ Fxxy t 0)
    (fun t ht ↦ by linarith [ht.2]) (fun t ht ↦ hM₂ t (hux ▸ ht)) (by fun_prop) (hux ▸ hcxxy)
  have hC := hweight hx (w := fun t ↦ (x - t) ^ 2) (g := fun t ↦ Fxxx t 0)
    (fun t _ ↦ sq_nonneg _) (fun t ht ↦ hM₃ t (hux ▸ ht)) (by fun_prop) (hux ▸ hcxxx)
  rw [hlin] at hA hB
  rw [hquad] at hC
  calc _ ≤ |∫ s in (0 : ℝ)..y, (y - s) * ∫ t in (0 : ℝ)..x, Fxyy t s| +
        |y * ∫ t in (0 : ℝ)..x, (x - t) * Fxxy t 0| +
        |1 / 2 * ∫ t in (0 : ℝ)..x, (x - t) ^ 2 * Fxxx t 0| := abs_add_three _ _ _
    _ ≤ M₁ * x * (y ^ 2 / 2) + y * (M₂ * (x ^ 2 / 2)) + 1 / 2 * (M₃ * (x ^ 3 / 3)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
    _ = M₁ * x * y ^ 2 / 2 + M₂ * x ^ 2 * y / 2 + M₃ * x ^ 3 / 6 := by ring

/-- `∫` of `(1 - t)^k` over `[u, v]`. -/
theorem integral_one_sub_pow (k : ℕ) (u v : ℝ) :
    ∫ t in u..v, (1 - t) ^ k = ((1 - u) ^ (k + 1) - (1 - v) ^ (k + 1)) / (k + 1) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t ↦ (1 - t) ^ (k + 1) * (-1 / ((k : ℝ) + 1)))
    (fun t _ ↦ by
      have h := (((hasDerivAt_id' t).const_sub 1).fun_pow (k + 1)).mul_const (-1 / ((k : ℝ) + 1))
      convert h using 1
      push_cast
      field_simp) ((by fun_prop : Continuous fun t : ℝ ↦ (1 - t) ^ k).intervalIntegrable u v)]
  field_simp
  ring

/-- **Supp II Sec 8.5, piecewise bound for powers.** Let `f` be continuous on `[0, x]` with
`f ≤ F i` on `[(i - 1) h, i h] ∩ [0, x]` for `i ≥ 1`, and `x ∈ [(m - 1) h, m h]`, `m ≥ 1`. Then
`E(f, k)(x) ≤ ∑_{j < m} max(F j, F (j + 1)) ((m - j)^{k+1} - (m - j - 1)^{k+1}) /
((k + 1) m^{k+1})`.
On `t ∈ [j/m, (j + 1)/m]` the point `x t` lies in `[(j - 1) h, (j + 1) h]`. -/
theorem weightedAverage_le_piecewise {f : ℝ → ℝ} {Fb : ℕ → ℝ} {h x : ℝ} {m : ℕ} (k : ℕ)
    (hh : 0 < h) (hm : 1 ≤ m) (hxl : ((m : ℝ) - 1) * h ≤ x) (hxu : x ≤ m * h)
    (hcont : ContinuousOn f (Icc 0 x))
    (hfb : ∀ i : ℕ, 1 ≤ i → ∀ z ∈ Icc (((i : ℝ) - 1) * h) (i * h), z ∈ Icc 0 x → f z ≤ Fb i) :
    weightedAverage f k x ≤ ∑ j ∈ Finset.range m, max (Fb j) (Fb (j + 1)) *
      ((((m : ℝ) - j) ^ (k + 1) - ((m : ℝ) - j - 1) ^ (k + 1)) /
        ((k + 1) * (m : ℝ) ^ (k + 1))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (by linarith [(by exact_mod_cast hm : (1 : ℝ) ≤ m)])
    hh.le) hxl
  set a : ℕ → ℝ := fun j ↦ (j : ℝ) / m
  have hcomp : ContinuousOn (fun t ↦ f (x * t) * (1 - t) ^ k) (Icc 0 1) := by
    refine (hcont.comp (by fun_prop : Continuous fun t : ℝ ↦ x * t).continuousOn
      fun t ht ↦ ?_).mul (by fun_prop)
    exact ⟨mul_nonneg hx0 ht.1, by nlinarith [ht.2]⟩
  have hsub : ∀ j < m, uIcc (a j) (a (j + 1)) ⊆ Icc 0 1 := by
    intro j hj
    rw [uIcc_of_le (by simp only [a]; gcongr; simp)]
    refine Icc_subset_Icc (by positivity) ?_
    simp only [a]
    rw [div_le_one hm']
    exact_mod_cast hj
  have hint : ∀ j < m, IntervalIntegrable (fun t ↦ f (x * t) * (1 - t) ^ k) volume (a j)
      (a (j + 1)) := fun j hj ↦ (hcomp.mono (hsub j hj)).intervalIntegrable
  unfold weightedAverage
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have e0 : a 0 = 0 := by simp [a]
  have em : a m = 1 := by simp [a, hm'.ne']
  rw [e0, em] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hle : a j ≤ a (j + 1) := by simp only [a]; gcongr; simp
  -- the bound on the piece
  have hpt : ∀ t ∈ Icc (a j) (a (j + 1)), f (x * t) * (1 - t) ^ k ≤
      max (Fb j) (Fb (j + 1)) * (1 - t) ^ k := by
    intro t ht
    have ht01 := hsub j hj' (by rw [uIcc_of_le hle]; exact ht)
    have hw : 0 ≤ (1 - t) ^ k := pow_nonneg (by linarith [ht01.2]) k
    refine mul_le_mul_of_nonneg_right ?_ hw
    have hxt : x * t ∈ Icc 0 x := ⟨mul_nonneg hx0 ht01.1, by nlinarith [ht01.2]⟩
    have hlo : ((j : ℝ) - 1) * h ≤ x * t := by
      have h1 : ((m : ℝ) - 1) * h * ((j : ℝ) / m) ≤ x * t :=
        mul_le_mul hxl ht.1 (by positivity) hx0
      have h2 : ((j : ℝ) - 1) * h ≤ ((m : ℝ) - 1) * h * ((j : ℝ) / m) := by
        rw [show ((m : ℝ) - 1) * h * ((j : ℝ) / m) = (j - j / m) * h by field_simp]
        have : (j : ℝ) / m ≤ 1 := by rw [div_le_one hm']; exact_mod_cast hj'.le
        nlinarith
      linarith
    have hhi : x * t ≤ ((j : ℝ) + 1) * h := by
      have h1 : x * t ≤ m * h * (((j : ℝ) + 1) / m) := by
        have := ht.2
        simp only [a, Nat.cast_add, Nat.cast_one] at this
        exact mul_le_mul hxu this ht01.1 (by positivity)
      rw [show (m : ℝ) * h * (((j : ℝ) + 1) / m) = ((j : ℝ) + 1) * h by field_simp] at h1
      exact h1
    rcases le_total (x * t) (j * h) with hc | hc
    · -- the cell `[(j - 1) h, j h]`, or `j = 0` and the point `0` of the first cell
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · have hz : x * t = 0 := le_antisymm (by simpa using hc) hxt.1
        have := hfb 1 le_rfl (x * t) ⟨by rw [hz]; simp, by rw [hz]; positivity⟩ hxt
        exact this.trans (le_max_right _ _)
      · exact (hfb j hjpos (x * t) ⟨hlo, hc⟩ hxt).trans (le_max_left _ _)
    · have := hfb (j + 1) (by omega) (x * t) ⟨by push_cast; linarith, by push_cast; linarith⟩ hxt
      exact this.trans (le_max_right _ _)
  calc ∫ t in a j..a (j + 1), f (x * t) * (1 - t) ^ k ≤
        ∫ t in a j..a (j + 1), max (Fb j) (Fb (j + 1)) * (1 - t) ^ k :=
        intervalIntegral.integral_mono_on hle (hint j hj')
          ((by fun_prop : Continuous fun t : ℝ ↦ max (Fb j) (Fb (j + 1)) * (1 - t) ^ k)
            |>.intervalIntegrable _ _) hpt
    _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_one_sub_pow]
        congr 1
        have e1 : 1 - a j = ((m : ℝ) - j) / m := by simp only [a]; field_simp
        have e2 : 1 - a (j + 1) = ((m : ℝ) - j - 1) / m := by
          simp only [a]
          push_cast
          field_simp
          ring
        rw [e1, e2, div_pow, div_pow]
        field_simp

/-- The normalized double average `∫₀¹ ∫₀¹ G(x t, y s) (1 - t)^i (1 - s)^j dt ds`. -/
noncomputable def doubleWeightedAverage (G : ℝ → ℝ → ℝ) (i j : ℕ) (x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, G (x * t) (y * s) * (1 - t) ^ i) * (1 - s) ^ j

/-- The double average as a normalized integral. -/
theorem integral_integral_mul_sub_pow_eq (G : ℝ → ℝ → ℝ) (i j : ℕ) (x y : ℝ) :
    ∫ s in (0 : ℝ)..y, (y - s) ^ j * ∫ t in (0 : ℝ)..x, G t s * (x - t) ^ i =
      x ^ (i + 1) * y ^ (j + 1) * doubleWeightedAverage G i j x y := by
  have hin : ∀ s, ∫ t in (0 : ℝ)..x, G t s * (x - t) ^ i =
      x ^ (i + 1) * weightedAverage (fun t ↦ G t s) i x := fun s ↦
    integral_mul_sub_pow_eq (fun t ↦ G t s) i x
  simp only [hin]
  have h := integral_mul_sub_pow_eq (fun s ↦ x ^ (i + 1) * weightedAverage (fun t ↦ G t s) i x)
    j y
  rw [show (∫ s in (0 : ℝ)..y, (y - s) ^ j * (x ^ (i + 1) * weightedAverage (fun t ↦ G t s) i x)) =
      ∫ s in (0 : ℝ)..y, x ^ (i + 1) * weightedAverage (fun t ↦ G t s) i x * (y - s) ^ j by
    congr 1
    funext s
    ring, h]
  unfold weightedAverage doubleWeightedAverage
  rw [← intervalIntegral.integral_const_mul]
  have e : ∀ s, x ^ (i + 1) * (∫ t in (0 : ℝ)..1, G (x * t) (y * s) * (1 - t) ^ i) * (1 - s) ^ j =
      x ^ (i + 1) * ((∫ t in (0 : ℝ)..1, G (x * t) (y * s) * (1 - t) ^ i) * (1 - s) ^ j) :=
    fun s ↦ by ring
  simp only [e, intervalIntegral.integral_const_mul]
  ring

/-- **Supp II Sec 8.5, the averaged bound before (8.64).** Under the hypotheses of
`eq_taylor_origin`, for `x, y ≥ 0` and integrability of the absolute inner integral,
`|F(x, y)| ≤ x y² E_{xy}(|F_{xyy}|, 0, 1)(x, y) + x² y E(|F_{xxy}(·, 0)|, 1)(x) +
x³ / 2 E(|F_{xxx}(·, 0)|, 2)(x)`. -/
theorem abs_le_taylor_origin_averages {F Fx Fxx Fxxx Fy Fxy Fxxy Fyy Fxyy : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy₀ : ∀ s ∈ uIcc 0 y, HasDerivAt (F x) (Fy x s) s)
    (hy₁ : ∀ s ∈ uIcc 0 y, HasDerivAt (Fy x) (Fyy x s) s)
    (hcy : ContinuousOn (Fyy x) (uIcc 0 y))
    (hxyy : ∀ s ∈ uIcc 0 y, ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fyy u s) (Fxyy t s) t)
    (hcxyy : ∀ s ∈ uIcc 0 y, ContinuousOn (fun t ↦ Fxyy t s) (uIcc 0 x))
    (hxy₀ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fy u 0) (Fxy t 0) t)
    (hxy₁ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fxy u 0) (Fxxy t 0) t)
    (hcxxy : ContinuousOn (fun t ↦ Fxxy t 0) (uIcc 0 x))
    (hx₀ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ F u 0) (Fx t 0) t)
    (hx₁ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fx u 0) (Fxx t 0) t)
    (hx₂ : ∀ t ∈ uIcc 0 x, HasDerivAt (fun u ↦ Fxx u 0) (Fxxx t 0) t)
    (hcxxx : ContinuousOn (fun t ↦ Fxxx t 0) (uIcc 0 x))
    (hFyy : ∀ s ∈ uIcc 0 y, Fyy 0 s = 0) (hFy : Fy 0 0 = 0) (hFxy : Fxy 0 0 = 0)
    (hF : F 0 0 = 0) (hFx : Fx 0 0 = 0) (hFxx : Fxx 0 0 = 0)
    (hint : IntervalIntegrable (fun s ↦ (y - s) ^ 1 * ∫ t in (0 : ℝ)..x, |Fxyy t s| * (x - t) ^ 0)
      volume 0 y) :
    |F x y| ≤ x * y ^ 2 * doubleWeightedAverage (fun t s ↦ |Fxyy t s|) 0 1 x y +
      x ^ 2 * y * weightedAverage (fun t ↦ |Fxxy t 0|) 1 x +
      x ^ 3 / 2 * weightedAverage (fun t ↦ |Fxxx t 0|) 2 x := by
  rw [eq_taylor_origin hy₀ hy₁ hcy hxyy hcxyy hxy₀ hxy₁ hcxxy hx₀ hx₁ hx₂ hcxxx hFyy hFy hFxy
    hF hFx hFxx]
  have hux : uIcc 0 x = Icc 0 x := uIcc_of_le hx
  have huy : uIcc 0 y = Icc 0 y := uIcc_of_le hy
  -- the double integral
  have hinner : ∀ s ∈ uIcc 0 y, ∫ t in (0 : ℝ)..x, Fxyy t s = Fyy x s := by
    intro s hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (hxyy s hs)
      ((hcxyy s hs).intervalIntegrable), hFyy s hs, sub_zero]
  have hgc : ContinuousOn (fun s ↦ ∫ t in (0 : ℝ)..x, Fxyy t s) (uIcc 0 y) :=
    hcy.congr fun s hs ↦ hinner s hs
  have hA : |∫ s in (0 : ℝ)..y, (y - s) * ∫ t in (0 : ℝ)..x, Fxyy t s| ≤
      ∫ s in (0 : ℝ)..y, (y - s) ^ 1 * ∫ t in (0 : ℝ)..x, |Fxyy t s| * (x - t) ^ 0 := by
    refine (intervalIntegral.abs_integral_le_integral_abs hy).trans ?_
    refine intervalIntegral.integral_mono_on hy ?_ hint fun s hs ↦ ?_
    · exact ((continuousOn_const.sub continuousOn_id).mul hgc).abs.intervalIntegrable
    · rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : 0 ≤ y - s), pow_one]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith [hs.2])
      simp only [pow_zero, mul_one]
      exact intervalIntegral.abs_integral_le_integral_abs hx
  rw [integral_integral_mul_sub_pow_eq (fun t s ↦ |Fxyy t s|) 0 1 x y] at hA
  -- the one-dimensional integrals
  have h1d {i : ℕ} {G : ℝ → ℝ} (hG : ContinuousOn G (uIcc 0 x)) :
      |∫ t in (0 : ℝ)..x, (x - t) ^ i * G t| ≤
        x ^ (i + 1) * weightedAverage (fun t ↦ |G t|) i x := by
    rw [← integral_mul_sub_pow_eq]
    refine (intervalIntegral.abs_integral_le_integral_abs hx).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [hux] at ht
    simp only [abs_mul, abs_pow, abs_of_nonneg (by linarith [ht.2] : 0 ≤ x - t), mul_comm]
  have hB := h1d (i := 1) hcxxy
  have hC := h1d (i := 2) hcxxx
  simp only [pow_one] at hB
  calc _ ≤ |∫ s in (0 : ℝ)..y, (y - s) * ∫ t in (0 : ℝ)..x, Fxyy t s| +
        |y * ∫ t in (0 : ℝ)..x, (x - t) * Fxxy t 0| +
        |1 / 2 * ∫ t in (0 : ℝ)..x, (x - t) ^ 2 * Fxxx t 0| := abs_add_three _ _ _
    _ ≤ x ^ (0 + 1) * y ^ (1 + 1) * doubleWeightedAverage (fun t s ↦ |Fxyy t s|) 0 1 x y +
        y * (x ^ (1 + 1) * weightedAverage (fun t ↦ |Fxxy t 0|) 1 x) +
        1 / 2 * (x ^ (2 + 1) * weightedAverage (fun t ↦ |Fxxx t 0|) 2 x) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
    _ = _ := by ring

end PDE.Analysis
