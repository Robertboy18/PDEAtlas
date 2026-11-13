/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.NewtonBounds

/-!
# Hermite interpolation on a cell from values and slopes

Chen and Hou, Part II, Supplementary Sec 8.3, interpolate a function on `[x₀, x₁]`, `x₁ = x₀ + h`,
from `lᵢ = f(xᵢ)` and the scaled slopes `mᵢ = h f'(xᵢ)`. In the local variable `t = (x - x₀) / h`
the cubic Hermite interpolant is
`G₄(t) = l₀ (1 - t) + l₁ t + t² (t - 1) (m₁ - (l₁ - l₀)) + (t - 1)² t (m₀ - (l₁ - l₀))`
(`hermiteCubic`, (8.22)); the quartic `H₅` adds `(l₂ - G₄(2)) t² (t - 1)² / 4` to match the value
`l₂ = f(x₀ + 2h)` (`hermiteQuartic`, (8.19)). The slope errors are in `HermiteSlopeBounds`.

Here `L` is a Lipschitz constant of the third (fourth) derivative, as Supp II Sec 8.3.1 needs
for `C^{4,1}` data. The slope bound (8.30)-(8.33) is stated with `|mᵢ|`, for the local slope
`∂ₜG₄`; the physical slope is that divided by `h` (`abs_deriv_le_of_hermiteCubic`). The three
cases (8.30)-(8.32) are the three terms of the maximum `hermiteSlopeBound`.

## Main definitions

* `hermiteCubic`: the cubic Hermite interpolant `G₄` in the local variable (8.22).
* `hermiteQuartic`: the quartic interpolant `H₅` in the local variable (8.19).
* `hermiteCubicBound`: the bound `max(|l₀|, |l₁|) + (4/27) M₁` of `G₄` on `[0, 1]` (8.23)-(8.24),
  with `M₁` the largest of `|m₁ - m₀|`, `|m₁ - (l₁ - l₀)|` and `|m₀ - (l₁ - l₀)|`.
* `hermiteSlopeBound`: the bound of the local slope `∂ₜG₄` on `[0, 1]` (8.33).
* `hermiteCubicPoly`: `G₄` as a polynomial in the physical variable; `hermiteQuarticPoly` is `H₅`.

## Main results

* `abs_hermiteCubic_le`: `|G₄| ≤ max(|l₀|, |l₁|) + (4/27) M₁` on `[0, 1]` (8.24).
* `abs_hermiteQuartic_le`: `|H₅| ≤ |G₄| + |l₂ - G₄(2)| / 64` on `[0, 1]` (8.26).
* `abs_hermiteCubicSlope_le`: `|∂ₜG₄| ≤ hermiteSlopeBound` on `[0, 1]` (8.29)-(8.33).
* `abs_quarticWeightSlope_le`: `|∂ₜ (t² (t - 1)² / 4)| ≤ 1 / (12 √3)` on `[0, 1]` (8.34).
* `abs_sub_hermiteCubic_le`: `|f - H₄| ≤ L (x - x₀)² (x - x₁)² / 24` on `[x₀, x₀ + 2h]` (8.20).
* `abs_sub_hermiteCubic_le_left`: `|f - H₄| ≤ L h⁴ / 384` on `[x₀, x₁]` (8.21).
* `abs_sub_hermiteQuartic_le_left`: `|f - H₅| ≤ L h⁵ / 1200` on `[x₀, x₁]` (8.21).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.3, (8.19)-(8.34).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Polynomial

/-! ### The local interpolants and their bounds -/

/-- The cubic Hermite interpolant `G₄` in the local variable (Supp II (8.22)). -/
def hermiteCubic (l₀ l₁ m₀ m₁ t : ℝ) : ℝ :=
  l₀ * (1 - t) + l₁ * t + t ^ 2 * (t - 1) * (m₁ - (l₁ - l₀)) +
    (t - 1) ^ 2 * t * (m₀ - (l₁ - l₀))

/-- The local slope `∂ₜ G₄` (Supp II (8.29)). -/
def hermiteCubicSlope (l₀ l₁ m₀ m₁ t : ℝ) : ℝ :=
  (l₁ - l₀) + (3 * t ^ 2 - 2 * t) * (m₁ - (l₁ - l₀)) + (3 * t ^ 2 - 4 * t + 1) * (m₀ - (l₁ - l₀))

/-- The quartic interpolant `H₅` in the local variable (Supp II (8.19), equal spacing). -/
noncomputable def hermiteQuartic (l₀ l₁ l₂ m₀ m₁ t : ℝ) : ℝ :=
  hermiteCubic l₀ l₁ m₀ m₁ t + (l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2) * (t ^ 2 * (t - 1) ^ 2 / 4)

/-- **Supp II, the display before (8.25).** `G₄(2) = l₀ + 2 m₀ + 4 (m₁ - (l₁ - l₀))`. -/
theorem hermiteCubic_two (l₀ l₁ m₀ m₁ : ℝ) :
    hermiteCubic l₀ l₁ m₀ m₁ 2 = l₀ + 2 * m₀ + 4 * (m₁ - (l₁ - l₀)) := by
  unfold hermiteCubic
  ring

/-- The bound `max(|l₀|, |l₁|) + (4/27) max(|m₁ - m₀|, |m₁ - (l₁ - l₀)|, |m₀ - (l₁ - l₀)|)` of the
cubic Hermite interpolant on a cell (Supp II (8.23)-(8.24)). -/
noncomputable def hermiteCubicBound (l₀ l₁ m₀ m₁ : ℝ) : ℝ :=
  max |l₀| |l₁| + 4 / 27 * max (max |m₁ - m₀| |m₁ - (l₁ - l₀)|) |m₀ - (l₁ - l₀)|

/-- The bound of the local slope `∂ₜG₄` on a cell (Supp II (8.33)), with `L = l₁ - l₀`:
`max(max(|L|, |m₀|) + |L - m₁| / 3, max(|L|, |m₁|) + |L - m₀| / 3,
|L| + max(|L - m₀|, |L - m₁|) / 2)`. -/
noncomputable def hermiteSlopeBound (l₀ l₁ m₀ m₁ : ℝ) : ℝ :=
  max (max (max |l₁ - l₀| |m₀| + |l₁ - l₀ - m₁| / 3)
    (max |l₁ - l₀| |m₁| + |l₁ - l₀ - m₀| / 3))
    (|l₁ - l₀| + max |l₁ - l₀ - m₀| |l₁ - l₀ - m₁| / 2)

/-- **Supp II (8.24).** On `[0, 1]`,
`|G₄| ≤ max(|l₀|, |l₁|) + (4/27) max(|m₁ - m₀|, |m₁ - (l₁ - l₀)|, |m₀ - (l₁ - l₀)|)`. -/
theorem abs_hermiteCubic_le {l₀ l₁ m₀ m₁ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |hermiteCubic l₀ l₁ m₀ m₁ t| ≤ hermiteCubicBound l₀ l₁ m₀ m₁ := by
  unfold hermiteCubicBound
  set M := max (max |m₁ - m₀| |m₁ - (l₁ - l₀)|) |m₀ - (l₁ - l₀)|
  have hM₁ : |m₁ - m₀| ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM₂ : |m₁ - (l₁ - l₀)| ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM₃ : |m₀ - (l₁ - l₀)| ≤ M := le_max_right _ _
  obtain ⟨h0, h1⟩ := ht
  have hlin := abs_lerp_le (u := l₀) (w := l₁) ⟨h0, h1⟩
  have hII : |t ^ 2 * (t - 1) * (m₁ - (l₁ - l₀)) + (t - 1) ^ 2 * t * (m₀ - (l₁ - l₀))| ≤
      4 / 27 * M := by
    rcases le_total t (1 / 2) with hle | hle
    · -- `II = t (t - 1) (t (m₁ - m₀) + (2t - 1) (m₀ - (l₁ - l₀)))`
      have hid : t ^ 2 * (t - 1) * (m₁ - (l₁ - l₀)) + (t - 1) ^ 2 * t * (m₀ - (l₁ - l₀)) =
          t * (t - 1) * (t * (m₁ - m₀) + (2 * t - 1) * (m₀ - (l₁ - l₀))) := by ring
      rw [hid, abs_mul]
      have hA : |t * (t - 1)| = t * (1 - t) := by
        rw [abs_of_nonpos (by nlinarith)]
        ring
      have hB : |t * (m₁ - m₀) + (2 * t - 1) * (m₀ - (l₁ - l₀))| ≤ (1 - t) * M := by
        calc _ ≤ |t * (m₁ - m₀)| + |(2 * t - 1) * (m₀ - (l₁ - l₀))| := abs_add_le _ _
          _ = t * |m₁ - m₀| + (1 - 2 * t) * |m₀ - (l₁ - l₀)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg h0,
              abs_of_nonpos (show 2 * t - 1 ≤ 0 by linarith)]
            ring
          _ ≤ t * M + (1 - 2 * t) * M := by gcongr; linarith
          _ = (1 - t) * M := by ring
      have hM0 : 0 ≤ M := (abs_nonneg _).trans hM₁
      have hcube := mul_sub_one_sq_le (t := t) ⟨h0, h1⟩
      rw [hA]
      calc t * (1 - t) * |t * (m₁ - m₀) + (2 * t - 1) * (m₀ - (l₁ - l₀))| ≤
            t * (1 - t) * ((1 - t) * M) := by
            gcongr
        _ = t * (t - 1) ^ 2 * M := by ring
        _ ≤ 4 / 27 * M := by gcongr
    · -- `II = t (t - 1) ((t - 1) (m₀ - m₁) + (2t - 1) (m₁ - (l₁ - l₀)))`
      have hid : t ^ 2 * (t - 1) * (m₁ - (l₁ - l₀)) + (t - 1) ^ 2 * t * (m₀ - (l₁ - l₀)) =
          t * (t - 1) * ((t - 1) * (m₀ - m₁) + (2 * t - 1) * (m₁ - (l₁ - l₀))) := by ring
      rw [hid, abs_mul]
      have hA : |t * (t - 1)| = t * (1 - t) := by
        rw [abs_of_nonpos (by nlinarith)]
        ring
      have hB : |(t - 1) * (m₀ - m₁) + (2 * t - 1) * (m₁ - (l₁ - l₀))| ≤ t * M := by
        calc _ ≤ |(t - 1) * (m₀ - m₁)| + |(2 * t - 1) * (m₁ - (l₁ - l₀))| := abs_add_le _ _
          _ = (1 - t) * |m₁ - m₀| + (2 * t - 1) * |m₁ - (l₁ - l₀)| := by
            rw [abs_mul, abs_mul, abs_of_nonpos (show t - 1 ≤ 0 by linarith),
              abs_of_nonneg (show 0 ≤ 2 * t - 1 by linarith), abs_sub_comm m₀ m₁]
            ring
          _ ≤ (1 - t) * M + (2 * t - 1) * M := by gcongr; linarith
          _ = t * M := by ring
      have hM0 : 0 ≤ M := (abs_nonneg _).trans hM₁
      have hcube := mul_sub_one_sq_le (t := 1 - t) ⟨by linarith, by linarith⟩
      rw [hA]
      calc t * (1 - t) * |(t - 1) * (m₀ - m₁) + (2 * t - 1) * (m₁ - (l₁ - l₀))| ≤
            t * (1 - t) * (t * M) := by
            gcongr
        _ = (1 - t) * (1 - t - 1) ^ 2 * M := by ring
        _ ≤ 4 / 27 * M := by gcongr
  have hid : hermiteCubic l₀ l₁ m₀ m₁ t = (l₀ + t * (l₁ - l₀)) +
      (t ^ 2 * (t - 1) * (m₁ - (l₁ - l₀)) + (t - 1) ^ 2 * t * (m₀ - (l₁ - l₀))) := by
    unfold hermiteCubic
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hlin hII)

/-- **Supp II (8.25)-(8.26).** On `[0, 1]`, `|H₅| ≤ |G₄| + |l₂ - G₄(2)| / 64`. -/
theorem abs_hermiteQuartic_le {l₀ l₁ l₂ m₀ m₁ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |hermiteQuartic l₀ l₁ l₂ m₀ m₁ t| ≤
      |hermiteCubic l₀ l₁ m₀ m₁ t| + |l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2| / 64 := by
  unfold hermiteQuartic
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  have hq : |t * (t - 1)| ≤ 1 / 4 := by simpa using abs_sub_mul_sub_le (a := 0) (b := 1) ht
  have hw : |t ^ 2 * (t - 1) ^ 2 / 4| ≤ 1 / 64 := by
    rw [show t ^ 2 * (t - 1) ^ 2 / 4 = (t * (t - 1)) ^ 2 / 4 by ring, abs_div, abs_pow,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : |t * (t - 1)| ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hq 2
    linarith
  rw [abs_mul]
  calc |l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2| * |t ^ 2 * (t - 1) ^ 2 / 4| ≤
        |l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2| * (1 / 64) := by gcongr
    _ = _ := by ring

/-- **Supp II (8.30)-(8.33).** On `[0, 1]` the local slope satisfies
`|∂ₜG₄| ≤ max(max(|L|, |m₀|) + |L - m₁| / 3, max(|L|, |m₁|) + |L - m₀| / 3,
|L| + max(|L - m₀|, |L - m₁|) / 2)` with `L = l₁ - l₀`: the first term is the case `t ≤ 1/3`,
the second `t ≥ 2/3`, the third `t ∈ [1/3, 2/3]`. -/
theorem abs_hermiteCubicSlope_le {l₀ l₁ m₀ m₁ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |hermiteCubicSlope l₀ l₁ m₀ m₁ t| ≤ hermiteSlopeBound l₀ l₁ m₀ m₁ := by
  unfold hermiteSlopeBound
  set D := l₁ - l₀
  obtain ⟨h0, h1⟩ := ht
  -- a nonnegative combination with weights summing to one
  have hcomb {α β u v : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β = 1) :
      |α * u + β * v| ≤ max |u| |v| := by
    calc |α * u + β * v| ≤ α * |u| + β * |v| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
      _ ≤ α * max |u| |v| + β * max |u| |v| := by gcongr; exacts [le_max_left _ _, le_max_right _ _]
      _ = max |u| |v| := by rw [← add_mul, hs, one_mul]
  rcases le_total t (1 / 3) with ha | ha
  · have hid : hermiteCubicSlope l₀ l₁ m₀ m₁ t = ((4 * t - 3 * t ^ 2) * D +
        (3 * t ^ 2 - 4 * t + 1) * m₀) + (2 * t - 3 * t ^ 2) * (D - m₁) := by
      unfold hermiteCubicSlope; ring
    rw [hid]
    have h1' := hcomb (u := D) (v := m₀) (α := 4 * t - 3 * t ^ 2)
      (β := 3 * t ^ 2 - 4 * t + 1) (by nlinarith) (by nlinarith) (by ring)
    have h2' : |(2 * t - 3 * t ^ 2) * (D - m₁)| ≤ |D - m₁| / 3 := by
      rw [abs_mul, abs_of_nonneg (by nlinarith)]
      have : 2 * t - 3 * t ^ 2 ≤ 1 / 3 := by nlinarith [sq_nonneg (t - 1 / 3)]
      nlinarith [abs_nonneg (D - m₁)]
    calc _ ≤ |(4 * t - 3 * t ^ 2) * D + (3 * t ^ 2 - 4 * t + 1) * m₀| +
          |(2 * t - 3 * t ^ 2) * (D - m₁)| := abs_add_le _ _
      _ ≤ max |D| |m₀| + |D - m₁| / 3 := add_le_add h1' h2'
      _ ≤ _ := (le_max_left _ _).trans (le_max_left _ _)
  rcases le_total (2 / 3) t with hb | hb
  · have hid : hermiteCubicSlope l₀ l₁ m₀ m₁ t = ((4 * (1 - t) - 3 * (1 - t) ^ 2) * D +
        (3 * (1 - t) ^ 2 - 4 * (1 - t) + 1) * m₁) + (2 * (1 - t) - 3 * (1 - t) ^ 2) * (D - m₀) := by
      unfold hermiteCubicSlope; ring
    rw [hid]
    have h1' := hcomb (u := D) (v := m₁) (α := 4 * (1 - t) - 3 * (1 - t) ^ 2)
      (β := 3 * (1 - t) ^ 2 - 4 * (1 - t) + 1) (by nlinarith) (by nlinarith) (by ring)
    have h2' : |(2 * (1 - t) - 3 * (1 - t) ^ 2) * (D - m₀)| ≤ |D - m₀| / 3 := by
      rw [abs_mul, abs_of_nonneg (by nlinarith)]
      have : 2 * (1 - t) - 3 * (1 - t) ^ 2 ≤ 1 / 3 := by nlinarith [sq_nonneg (1 - t - 1 / 3)]
      nlinarith [abs_nonneg (D - m₀)]
    calc _ ≤ |(4 * (1 - t) - 3 * (1 - t) ^ 2) * D + (3 * (1 - t) ^ 2 - 4 * (1 - t) + 1) * m₁| +
          |(2 * (1 - t) - 3 * (1 - t) ^ 2) * (D - m₀)| := abs_add_le _ _
      _ ≤ max |D| |m₁| + |D - m₀| / 3 := add_le_add h1' h2'
      _ ≤ _ := (le_max_right _ _).trans (le_max_left _ _)
  · have hid : hermiteCubicSlope l₀ l₁ m₀ m₁ t = D + ((4 * t - 3 * t ^ 2 - 1) * (D - m₀) +
        (2 * t - 3 * t ^ 2) * (D - m₁)) := by
      unfold hermiteCubicSlope; ring
    rw [hid]
    have hα : 0 ≤ 4 * t - 3 * t ^ 2 - 1 := by nlinarith
    have hβ : 0 ≤ 2 * t - 3 * t ^ 2 := by nlinarith
    have hsum : (4 * t - 3 * t ^ 2 - 1) + (2 * t - 3 * t ^ 2) ≤ 1 / 2 := by
      nlinarith [sq_nonneg (t - 1 / 2)]
    have h2' : |(4 * t - 3 * t ^ 2 - 1) * (D - m₀) + (2 * t - 3 * t ^ 2) * (D - m₁)| ≤
        max |D - m₀| |D - m₁| / 2 := by
      calc _ ≤ (4 * t - 3 * t ^ 2 - 1) * |D - m₀| + (2 * t - 3 * t ^ 2) * |D - m₁| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
        _ ≤ (4 * t - 3 * t ^ 2 - 1) * max |D - m₀| |D - m₁| +
            (2 * t - 3 * t ^ 2) * max |D - m₀| |D - m₁| := by
            gcongr; exacts [le_max_left _ _, le_max_right _ _]
        _ ≤ 1 / 2 * max |D - m₀| |D - m₁| := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right hsum ((abs_nonneg _).trans (le_max_left _ _))
        _ = _ := by ring
    calc _ ≤ |D| + |(4 * t - 3 * t ^ 2 - 1) * (D - m₀) + (2 * t - 3 * t ^ 2) * (D - m₁)| :=
          abs_add_le _ _
      _ ≤ |D| + max |D - m₀| |D - m₁| / 2 := add_le_add le_rfl h2'
      _ ≤ _ := le_max_right _ _

/-- **Supp II (8.34).** `|t (t - 1) (t - 1/2)| ≤ 1 / (12 √3)` on `[0, 1]`; this is the local slope
of `t² (t - 1)² / 4`. -/
theorem abs_quarticWeightSlope_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |t * (t - 1) * (t - 1 / 2)| ≤ 1 / (12 * Real.sqrt 3) := by
  have h := abs_cubicNodal_le (t := 2 * t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hid : t * (t - 1) * (t - 1 / 2) = 2 * t * (2 * t - 1) * (2 * t - 2) / 8 := by ring
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [hid, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  calc |2 * t * (2 * t - 1) * (2 * t - 2)| / 8 ≤ 2 / (3 * Real.sqrt 3) / 8 := by gcongr
    _ = 1 / (12 * Real.sqrt 3) := by field_simp; ring

/-! ### Polynomial forms in the physical variable -/

/-- The local variable `t = (x - x₀) / h` as a polynomial. -/
noncomputable def localCoordinate (x₀ h : ℝ) : ℝ[X] := C h⁻¹ * (X - C x₀)

/-- The polynomial `localCoordinate x₀ h` takes the value `(x - x₀) / h` at `x`. -/
@[simp] theorem eval_localCoordinate (x₀ h x : ℝ) :
    (localCoordinate x₀ h).eval x = (x - x₀) / h := by
  simp [localCoordinate, div_eq_inv_mul]

/-- The derivative of `localCoordinate x₀ h` is the constant `h⁻¹`. -/
@[simp] theorem derivative_localCoordinate (x₀ h : ℝ) :
    derivative (localCoordinate x₀ h) = C h⁻¹ := by
  simp [localCoordinate]

/-- The cubic Hermite interpolant as a polynomial in the physical variable. -/
noncomputable def hermiteCubicPoly (x₀ h l₀ l₁ m₀ m₁ : ℝ) : ℝ[X] :=
  C l₀ * (1 - localCoordinate x₀ h) + C l₁ * localCoordinate x₀ h +
    localCoordinate x₀ h ^ 2 * (localCoordinate x₀ h - 1) * C (m₁ - (l₁ - l₀)) +
    (localCoordinate x₀ h - 1) ^ 2 * localCoordinate x₀ h * C (m₀ - (l₁ - l₀))

/-- The quartic interpolant `H₅` as a polynomial in the physical variable. -/
noncomputable def hermiteQuarticPoly (x₀ h l₀ l₁ l₂ m₀ m₁ : ℝ) : ℝ[X] :=
  hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁ + C ((l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2) / 4) *
    (localCoordinate x₀ h ^ 2 * (localCoordinate x₀ h - 1) ^ 2)

/-- The cubic Hermite interpolant has degree at most `3`. -/
theorem hermiteCubicPoly_natDegree_le (x₀ h l₀ l₁ m₀ m₁ : ℝ) :
    (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁).natDegree ≤ 3 := by
  unfold hermiteCubicPoly localCoordinate
  compute_degree

/-- The quartic interpolant `H₅` has degree at most `4`. -/
theorem hermiteQuarticPoly_natDegree_le (x₀ h l₀ l₁ l₂ m₀ m₁ : ℝ) :
    (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁).natDegree ≤ 4 := by
  unfold hermiteQuarticPoly hermiteCubicPoly localCoordinate
  compute_degree

/-- At `x` the polynomial `hermiteCubicPoly` takes the value of `hermiteCubic` at `t = (x - x₀) /
h`. -/
theorem eval_hermiteCubicPoly (x₀ h l₀ l₁ m₀ m₁ x : ℝ) :
    (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁).eval x = hermiteCubic l₀ l₁ m₀ m₁ ((x - x₀) / h) := by
  simp only [hermiteCubicPoly, hermiteCubic, eval_add, eval_mul, eval_C, eval_sub, eval_one,
    eval_pow, eval_localCoordinate]

/-- At `x` the polynomial `hermiteQuarticPoly` takes the value of `hermiteQuartic` at `t = (x - x₀)
/ h`. -/
theorem eval_hermiteQuarticPoly (x₀ h l₀ l₁ l₂ m₀ m₁ x : ℝ) :
    (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁).eval x =
      hermiteQuartic l₀ l₁ l₂ m₀ m₁ ((x - x₀) / h) := by
  simp only [hermiteQuarticPoly, hermiteQuartic, eval_add, eval_mul, eval_C, eval_sub, eval_one,
    eval_pow, eval_localCoordinate, eval_hermiteCubicPoly]
  ring

/-- The derivative of `hermiteCubicPoly` at `x` is `hermiteCubicSlope` at `t = (x - x₀) / h`,
divided by `h`. -/
theorem eval_derivative_hermiteCubicPoly (x₀ h l₀ l₁ m₀ m₁ x : ℝ) :
    (derivative (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁)).eval x =
      hermiteCubicSlope l₀ l₁ m₀ m₁ ((x - x₀) / h) / h := by
  simp only [hermiteCubicPoly, derivative_add, derivative_mul, derivative_sub, derivative_C,
    derivative_one, derivative_pow, derivative_localCoordinate, eval_add, eval_mul, eval_C,
    eval_sub, eval_one, eval_pow, eval_localCoordinate, eval_zero, zero_mul, zero_add,
    sub_zero, add_zero, mul_zero]
  unfold hermiteCubicSlope
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- The derivative of `hermiteQuarticPoly` at `x` is `(hermiteCubicSlope t + (l₂ - G₄(2)) t (t - 1)
(t - 1/2)) / h` with `t = (x - x₀) / h`. -/
theorem eval_derivative_hermiteQuarticPoly (x₀ h l₀ l₁ l₂ m₀ m₁ x : ℝ) :
    (derivative (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁)).eval x =
      (hermiteCubicSlope l₀ l₁ m₀ m₁ ((x - x₀) / h) + (l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2) *
        ((x - x₀) / h * ((x - x₀) / h - 1) * ((x - x₀) / h - 1 / 2))) / h := by
  rw [hermiteQuarticPoly, derivative_add, eval_add, eval_derivative_hermiteCubicPoly]
  simp only [derivative_mul, derivative_sub, derivative_C, derivative_one, derivative_pow,
    derivative_localCoordinate, eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_pow,
    eval_localCoordinate, zero_mul, zero_add, sub_zero]
  rw [div_eq_mul_inv]
  push_cast
  ring

/-! ### Interpolation errors -/

/-- Membership and multiplicities in the multiset `{u, u, v, v}` of two double nodes. -/
theorem mem_doubleNodes {u v z : ℝ} (hz : z ∈ u ::ₘ u ::ₘ v ::ₘ v ::ₘ 0) : z = u ∨ z = v := by
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
  tauto

/-- For `u ≠ v`, the node `u` has multiplicity `2` in `{u, u, v, v}`. -/
theorem count_doubleNodes_left {u v : ℝ} (huv : u ≠ v) :
    (u ::ₘ u ::ₘ v ::ₘ v ::ₘ 0).count u = 2 := by
  rw [Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_cons_of_ne huv,
    Multiset.count_cons_of_ne huv, Multiset.count_zero]

/-- For `u ≠ v`, the node `v` has multiplicity `2` in `{u, u, v, v}`. -/
theorem count_doubleNodes_right {u v : ℝ} (huv : u ≠ v) :
    (u ::ₘ u ::ₘ v ::ₘ v ::ₘ 0).count v = 2 := by
  rw [Multiset.count_cons_of_ne huv.symm, Multiset.count_cons_of_ne huv.symm,
    Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_zero]

/-- The cubic Hermite interpolant takes the values `l₀`, `l₁` and the slopes `m₀ / h`, `m₁ / h`
at `x₀` and `x₀ + h`. -/
theorem hermiteCubicPoly_interpolates {x₀ h : ℝ} (hh : h ≠ 0) (l₀ l₁ m₀ m₁ : ℝ) :
    (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁).eval x₀ = l₀ ∧
      (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁).eval (x₀ + h) = l₁ ∧
      (derivative (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁)).eval x₀ = m₀ / h ∧
      (derivative (hermiteCubicPoly x₀ h l₀ l₁ m₀ m₁)).eval (x₀ + h) = m₁ / h := by
  have h1 : (x₀ + h - x₀) / h = 1 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [eval_hermiteCubicPoly, sub_self, zero_div, hermiteCubic]
    ring
  · simp only [eval_hermiteCubicPoly, h1, hermiteCubic]
    ring
  · simp only [eval_derivative_hermiteCubicPoly, sub_self, zero_div, hermiteCubicSlope]
    ring
  · simp only [eval_derivative_hermiteCubicPoly, h1, hermiteCubicSlope]
    ring

/-- The local interpolant matches the data at the two double nodes: values and slopes. -/
theorem hermiteCubicPoly_agree {x₀ h : ℝ} (hh : h ≠ 0) (Φ : ℕ → ℝ → ℝ) :
    ∀ z ∈ x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ 0,
      ∀ k < (x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ 0).count z,
        Φ k z = (derivative^[k] (hermiteCubicPoly x₀ h (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀)
          (h * Φ 1 (x₀ + h)))).eval z := by
  have hne : x₀ ≠ x₀ + h := fun h' ↦ hh (by linarith)
  obtain ⟨e₀, e₁, d₀, d₁⟩ := hermiteCubicPoly_interpolates (x₀ := x₀) hh (Φ 0 x₀) (Φ 0 (x₀ + h))
    (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
  rw [mul_div_cancel_left₀ _ hh] at d₀ d₁
  intro z hz k hk
  rcases mem_doubleNodes hz with rfl | rfl
  · rw [count_doubleNodes_left hne] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact e₀.symm
    · exact d₀.symm
  · rw [count_doubleNodes_right hne] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact e₁.symm
    · exact d₁.symm

/-- **Supp II (8.20).** If the third derivative of `f = Φ 0` is `L`-Lipschitz on `[x₀, b]` with
`x₀ + h ≤ b`, the cubic Hermite interpolant from `f(xᵢ)` and `h f'(xᵢ)` at `x₀`, `x₁ = x₀ + h`
satisfies `|f - H₄| ≤ L (x - x₀)² (x - x₁)² / 24` on `[x₀, b]`. -/
theorem abs_sub_hermiteCubic_le {x₀ h b L : ℝ} (hh : 0 < h) (hb : x₀ + h ≤ b)
    (Φ : ℕ → ℝ → ℝ) (hcontinuous : ∀ j < 3, ContinuousOn (Φ j) (Icc x₀ b))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo x₀ b, HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ b, ∀ y ∈ Icc x₀ b, |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ b) :
    |Φ 0 x - hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
      ((x - x₀) / h)| ≤ L / 24 * ((x - x₀) ^ 2 * (x - (x₀ + h)) ^ 2) := by
  have hrem := abs_sub_eval_le_of_lipschitz Φ hcontinuous hderiv hlip
    (hermiteCubicPoly x₀ h (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)))
    (hermiteCubicPoly_natDegree_le _ _ _ _ _ _) (x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ 0)
    (by simp) (fun z hz ↦ by
      rcases mem_doubleNodes hz with rfl | rfl
      · exact ⟨le_rfl, by linarith⟩
      · exact ⟨by linarith, hb⟩) (hermiteCubicPoly_agree hh.ne' Φ) hx
  rw [eval_hermiteCubicPoly] at hrem
  have hprod : ((x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ 0).map fun z ↦ x - z).prod =
      (x - x₀) ^ 2 * (x - (x₀ + h)) ^ 2 := by
    simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero]
    ring
  have h24 : ((3 + 1).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hprod, h24, abs_of_nonneg (show 0 ≤ (x - x₀) ^ 2 * (x - (x₀ + h)) ^ 2 by positivity)]
    at hrem
  exact hrem

/-- **Supp II (8.21), first estimate.** On `[x₀, x₁]`, `|f - H₄| ≤ L h⁴ / 384` for an
`L`-Lipschitz third derivative on `[x₀, x₁]`. -/
theorem abs_sub_hermiteCubic_le_left {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 3, ContinuousOn (Φ j) (Icc x₀ (x₀ + h)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo x₀ (x₀ + h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc x₀ (x₀ + h), |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 0 x - hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
      ((x - x₀) / h)| ≤ L * h ^ 4 / 384 := by
  have hrem := abs_sub_hermiteCubic_le hh le_rfl Φ hcontinuous hderiv hlip hx
  refine hrem.trans ?_
  have hL : 0 ≤ L := by
    have := hlip x₀ ⟨le_rfl, by linarith⟩ (x₀ + h) ⟨by linarith, le_rfl⟩
    have hpos : 0 < |x₀ - (x₀ + h)| := abs_pos.mpr (by linarith)
    nlinarith [abs_nonneg (Φ 3 x₀ - Φ 3 (x₀ + h))]
  have hq := abs_sub_mul_sub_le hx
  rw [show x₀ + h - x₀ = h by ring] at hq
  have hsq : (x - x₀) ^ 2 * (x - (x₀ + h)) ^ 2 ≤ (h ^ 2 / 4) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hq 2
    rw [sq_abs] at this
    nlinarith
  calc L / 24 * ((x - x₀) ^ 2 * (x - (x₀ + h)) ^ 2) ≤ L / 24 * (h ^ 2 / 4) ^ 2 := by gcongr
    _ = L * h ^ 4 / 384 := by ring

/-- The quartic interpolant takes the values `l₀`, `l₁`, `l₂` at `x₀`, `x₀ + h`, `x₀ + 2h` and the
slopes `m₀ / h`, `m₁ / h` at `x₀`, `x₀ + h`. -/
theorem hermiteQuarticPoly_interpolates {x₀ h : ℝ} (hh : h ≠ 0) (l₀ l₁ l₂ m₀ m₁ : ℝ) :
    (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁).eval x₀ = l₀ ∧
      (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁).eval (x₀ + h) = l₁ ∧
      (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁).eval (x₀ + 2 * h) = l₂ ∧
      (derivative (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁)).eval x₀ = m₀ / h ∧
      (derivative (hermiteQuarticPoly x₀ h l₀ l₁ l₂ m₀ m₁)).eval (x₀ + h) = m₁ / h := by
  have h1 : (x₀ + h - x₀) / h = 1 := by field_simp; ring
  have h2 : (x₀ + 2 * h - x₀) / h = 2 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [eval_hermiteQuarticPoly, sub_self, zero_div, hermiteQuartic, hermiteCubic]
    ring
  · simp only [eval_hermiteQuarticPoly, h1, hermiteQuartic, hermiteCubic]
    ring
  · simp only [eval_hermiteQuarticPoly, h2, hermiteQuartic]
    ring
  · simp only [eval_derivative_hermiteQuarticPoly, sub_self, zero_div, hermiteCubicSlope]
    ring
  · simp only [eval_derivative_hermiteQuarticPoly, h1, hermiteCubicSlope]
    ring

/-- The quartic interpolant matches values and slopes at `x₀`, `x₁` and the value at `x₂`. -/
theorem hermiteQuarticPoly_agree {x₀ h : ℝ} (hh : h ≠ 0) (Φ : ℕ → ℝ → ℝ) :
    ∀ z ∈ x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ (x₀ + 2 * h) ::ₘ 0,
      ∀ k < (x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ (x₀ + 2 * h) ::ₘ 0).count z,
        Φ k z = (derivative^[k] (hermiteQuarticPoly x₀ h (Φ 0 x₀) (Φ 0 (x₀ + h))
          (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)))).eval z := by
  have h01 : x₀ ≠ x₀ + h := fun h' ↦ hh (by linarith)
  have h02 : x₀ ≠ x₀ + 2 * h := fun h' ↦ hh (by linarith)
  have h12 : x₀ + h ≠ x₀ + 2 * h := fun h' ↦ hh (by linarith)
  obtain ⟨e₀, e₁, e₂, d₀, d₁⟩ := hermiteQuarticPoly_interpolates (x₀ := x₀) hh (Φ 0 x₀)
    (Φ 0 (x₀ + h)) (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
  rw [mul_div_cancel_left₀ _ hh] at d₀ d₁
  intro z hz k hk
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · rw [Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_cons_of_ne h01,
      Multiset.count_cons_of_ne h01, Multiset.count_cons_of_ne h02, Multiset.count_zero] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact e₀.symm
    · exact d₀.symm
  · rw [Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_cons_of_ne h01,
      Multiset.count_cons_of_ne h01, Multiset.count_cons_of_ne h02, Multiset.count_zero] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact e₀.symm
    · exact d₀.symm
  · rw [Multiset.count_cons_of_ne h01.symm, Multiset.count_cons_of_ne h01.symm,
      Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_cons_of_ne h12,
      Multiset.count_zero] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact e₁.symm
    · exact d₁.symm
  · rw [Multiset.count_cons_of_ne h01.symm, Multiset.count_cons_of_ne h01.symm,
      Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_cons_of_ne h12,
      Multiset.count_zero] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact e₁.symm
    · exact d₁.symm
  · rw [Multiset.count_cons_of_ne h02.symm, Multiset.count_cons_of_ne h02.symm,
      Multiset.count_cons_of_ne h12.symm, Multiset.count_cons_of_ne h12.symm,
      Multiset.count_cons_self, Multiset.count_zero] at hk
    obtain rfl : k = 0 := by omega
    exact e₂.symm

/-- A nonnegative Lipschitz constant: an `L`-Lipschitz function on an interval with two distinct
points has `0 ≤ L`. -/
theorem lipschitz_const_nonneg {g : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g x - g y| ≤ L * |x - y|) : 0 ≤ L := by
  have := hlip a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
  have hpos : 0 < |a - b| := abs_pos.mpr (by linarith)
  nlinarith [abs_nonneg (g a - g b)]

/-- **Supp II (8.21), second estimate.** If the fourth derivative of `f = Φ 0` is `L`-Lipschitz on
`[x₀, x₀ + 2h]`, the quartic interpolant `H₅` satisfies `|f - H₅| ≤ L h⁵ / 1200` on `[x₀, x₁]`; the
pointwise bound is `L |(x - x₀)² (x - x₁)² (x - x₂)| / 120`. -/
theorem abs_sub_hermiteQuartic_le_left {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 4, ContinuousOn (Φ j) (Icc x₀ (x₀ + 2 * h)))
    (hderiv : ∀ j < 4, ∀ z ∈ Ioo x₀ (x₀ + 2 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + 2 * h), ∀ y ∈ Icc x₀ (x₀ + 2 * h),
      |Φ 4 x - Φ 4 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 0 x - hermiteQuartic (Φ 0 x₀) (Φ 0 (x₀ + h)) (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀)
      (h * Φ 1 (x₀ + h)) ((x - x₀) / h)| ≤ L * h ^ 5 / 1200 := by
  have hrem := abs_sub_eval_le_of_lipschitz Φ hcontinuous hderiv hlip
    (hermiteQuarticPoly x₀ h (Φ 0 x₀) (Φ 0 (x₀ + h)) (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀)
      (h * Φ 1 (x₀ + h))) (hermiteQuarticPoly_natDegree_le _ _ _ _ _ _ _)
    (x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ (x₀ + 2 * h) ::ₘ 0) (by simp) (fun z hz ↦ by
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> constructor <;> linarith)
    (hermiteQuarticPoly_agree hh.ne' Φ) ⟨hx.1, by linarith [hx.2]⟩
  rw [eval_hermiteQuarticPoly] at hrem
  refine hrem.trans ?_
  set t := (x - x₀) / h
  have hxt : x = x₀ + t * h := by simp only [t]; field_simp; ring
  have hprod : ((x₀ ::ₘ x₀ ::ₘ (x₀ + h) ::ₘ (x₀ + h) ::ₘ (x₀ + 2 * h) ::ₘ 0).map
      fun z ↦ x - z).prod = h ^ 5 * (t ^ 2 * (t - 1) ^ 2 * (t - 2)) := by
    simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero]
    rw [hxt]
    ring
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hx.1]) hh.le
    · rw [div_le_iff₀ hh]
      linarith [hx.2]
  have hL := lipschitz_const_nonneg (by linarith : x₀ < x₀ + 2 * h) hlip
  have h120 : ((4 + 1).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hprod, h120, abs_mul, abs_of_pos (by positivity : 0 < h ^ 5)]
  have := abs_quinticNodal_le ht
  calc L / 120 * (h ^ 5 * |t ^ 2 * (t - 1) ^ 2 * (t - 2)|) ≤ L / 120 * (h ^ 5 * (1 / 10)) := by
        gcongr
    _ = L * h ^ 5 / 1200 := by ring

/-- Zeros of the error of an interpolant: Rolle's theorem between two interpolation points. -/
theorem exists_deriv_sub_eval_eq_zero {Φ₀ Φ₁ : ℝ → ℝ} {p : ℝ[X]} {u v : ℝ} (huv : u < v)
    (hcont : ContinuousOn Φ₀ (Icc u v)) (hderiv : ∀ z ∈ Ioo u v, HasDerivAt Φ₀ (Φ₁ z) z)
    (hu : Φ₀ u = p.eval u) (hv : Φ₀ v = p.eval v) :
    ∃ ξ ∈ Ioo u v, Φ₁ ξ = (derivative p).eval ξ := by
  obtain ⟨ξ, hξ, h0⟩ := exists_hasDerivAt_eq_zero (f := fun y ↦ Φ₀ y - p.eval y)
    (f' := fun y ↦ Φ₁ y - (derivative p).eval y) huv
    (hcont.sub p.continuous.continuousOn) (by simp [hu, hv])
    (fun z hz ↦ (hderiv z hz).sub (p.hasDerivAt z))
  exact ⟨ξ, hξ, sub_eq_zero.mp h0⟩

end PDE.Analysis.Approximation
