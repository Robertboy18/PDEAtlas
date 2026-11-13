/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.PlanarKernelBalls

/-!
# Absolute integrals of the Biot–Savart kernels on cells

The shape integrals of Chen and Hou II, Remark 4.5: the integrals `∫_Q |K(s)| ds` over the cells
`Q` of the decompositions of the singular regions, which do not depend on the point `x` and are
computed once. The cells have their corners on a lattice through the pole, so each lies in a closed
quadrant (for `K₁ = hessianKernel 0 1` and `K₂ = hessianKernel 0 0`) and on one side of each axis
(for the gradient kernels `∂ⱼΦ = gradientKernel j`, with `π ∂ⱼΦ = ∂ⱼ G`).

`|K₁|` and `|K₂|` are even in each coordinate, so a rectangle in any quadrant has the integral of
its reflection into the first one, where `integral_rectangle_abs_hessianKernel_zero_zero_mem`
applies. On a rectangle on one side of the axis `{sⱼ = 0}` the integral of `|∂ⱼΦ|` is a corner
sum through the pole of `integral_rectangle_gradientKernel_zero_eq_cornerSum` and
`integral_rectangle_gradientKernel_one_eq_cornerSum`.

The certified bound takes rational corners, so a cell of a rational mesh is evaluated directly,
without rescaling it to a unit cell.

## Main results

* `integral_rectangle_abs_hessianKernel_zero_one`: on a rectangle in a closed quadrant avoiding
  the pole, `∫_Q |K₁| = |∫_Q K₁|`, the absolute value of a corner sum of `-log |s|²/4`.
* `integral_rectangle_abs_hessianKernel_zero_one_le`: `∫_Q |K₁| ≤ max(|lo|, |hi|)` from a ball
  check.
* `setIntegral_rectangle_abs_hessianKernel_reflect_zero`:
  `∫_{[a,b] × [c,d]} |Kᵢ| = ∫_{[-b,-a] × [c,d]} |Kᵢ|`.
* `setIntegral_rectangle_abs_hessianKernel_reflect_one`:
  `∫_{[a,b] × [c,d]} |Kᵢ| = ∫_{[a,b] × [-d,-c]} |Kᵢ|`.
* `integral_rectangle_abs_gradientKernel`: on a rectangle on one side of `{sⱼ = 0}`,
  `∫_Q |∂ⱼΦ| = |∫_Q ∂ⱼΦ|`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 4.1.9,
  Remark 4.5.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common
open CAS.Numerics CAS.Numerics.PlanarKernel

namespace PotentialTheory.Planar

/-- If `f` has constant sign on a measurable set `S`, then `∫_S |f| = |∫_S f|`. -/
private theorem abs_setIntegral_of_sign {f : ℝ^2 → ℝ} {S : Set (ℝ^2)} (hS : MeasurableSet S)
    (h : (∀ y ∈ S, 0 ≤ f y) ∨ ∀ y ∈ S, f y ≤ 0) :
    ∫ y in S, |f y| = |∫ y in S, f y| := by
  rcases h with h | h
  · rw [setIntegral_congr_fun hS fun y hy ↦ abs_of_nonneg (h y hy),
      abs_of_nonneg (setIntegral_nonneg hS h)]
  · rw [setIntegral_congr_fun hS fun y hy ↦ abs_of_nonpos (h y hy), integral_neg,
      abs_of_nonpos (setIntegral_nonpos hS h)]

/-- **`|K₁|` on a rectangle of a closed quadrant**: `∫_Q |K₁| = |∫_Q K₁|`, since `K₁ = s₁ s₂/|s|⁴`
has the sign of `s₁ s₂`. -/
theorem integral_rectangle_abs_hessianKernel_zero_one {a b c d : ℝ}
    (h₀ : 0 ≤ a ∨ b ≤ 0) (h₁ : 0 ≤ c ∨ d ≤ 0) :
    ∫ y in coordinateRectangle a b c d, |hessianKernel 0 1 y| =
      |∫ y in coordinateRectangle a b c d, hessianKernel 0 1 y| := by
  refine abs_setIntegral_of_sign (measurableSet_coordinateRectangle a b c d) ?_
  have hK : ∀ y : ℝ^2, hessianKernel 0 1 y = y 0 * y 1 / ‖y‖ ^ 4 := hessianKernel_zero_one
  rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
  · exact Or.inl fun y hy ↦ by
      rw [hK]; exact div_nonneg (mul_nonneg (h₀.trans hy.1.1) (h₁.trans hy.2.1)) (by positivity)
  · exact Or.inr fun y hy ↦ by
      rw [hK]; exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (h₀.trans hy.1.1) (hy.2.2.trans h₁)) (by positivity)
  · exact Or.inr fun y hy ↦ by
      rw [hK]; exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (hy.1.2.trans h₀) (h₁.trans hy.2.1)) (by positivity)
  · exact Or.inl fun y hy ↦ by
      rw [hK]; exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (hy.1.2.trans h₀)
        (hy.2.2.trans h₁)) (by positivity)

/-- **Certified bound of `∫_Q |K₁|`** on a rectangle of a closed quadrant avoiding the pole, from
the ball check of `integral_rectangle_hessianKernel_zero_one_mem`: `∫_Q |K₁| ≤ max(|lo|, |hi|)`. -/
theorem integral_rectangle_abs_hessianKernel_zero_one_le {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    (h₀ : 0 ≤ a ∨ b ≤ 0) (h₁ : 0 ≤ c ∨ d ≤ 0) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0)
    {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (kernelOneBall P bits a b c d) = true) :
    ∫ y in coordinateRectangle a b c d, |hessianKernel 0 1 y| ≤ max |(lo : ℝ)| |(hi : ℝ)| := by
  have h₀' : (0 : ℝ) ≤ a ∨ (b : ℝ) ≤ 0 := by
    rcases h₀ with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have h₁' : (0 : ℝ) ≤ c ∨ (d : ℝ) ≤ 0 := by
    rcases h₁ with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rw [integral_rectangle_abs_hessianKernel_zero_one h₀' h₁']
  obtain ⟨hl, hh⟩ := integral_rectangle_hessianKernel_zero_one_mem hab hcd h0 h
  exact abs_le_max_abs_abs hl hh

/-! ### Reflections -/

/-- The reflection `s₁ ↦ -s₁` maps `[a, b] × [c, d]` onto `[-b, -a] × [c, d]`. -/
private theorem preimage_reflection_zero_rectangle (a b c d : ℝ) :
    coordinateReflection 0 ⁻¹' coordinateRectangle (-b) (-a) c d = coordinateRectangle a b c d := by
  ext y
  simp only [mem_preimage, mem_coordinateRectangle, mem_Icc, coordinateReflection_apply_same,
    coordinateReflection_apply_of_ne (n := 2) 0 1 (by decide)]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩

/-- The reflection `s₂ ↦ -s₂` maps `[a, b] × [c, d]` onto `[a, b] × [-d, -c]`. -/
private theorem preimage_reflection_one_rectangle (a b c d : ℝ) :
    coordinateReflection 1 ⁻¹' coordinateRectangle a b (-d) (-c) = coordinateRectangle a b c d := by
  ext y
  simp only [mem_preimage, mem_coordinateRectangle, mem_Icc, coordinateReflection_apply_same,
    coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩

/-- `|K₁|` and `|K₂|` are even in `s₁`: `∫_{[a,b] × [c,d]} |Kᵢ| = ∫_{[-b,-a] × [c,d]} |Kᵢ|`. -/
theorem setIntegral_rectangle_abs_hessianKernel_reflect_zero (j : Fin 2) (a b c d : ℝ) :
    ∫ y in coordinateRectangle a b c d, |hessianKernel 0 j y| =
      ∫ y in coordinateRectangle (-b) (-a) c d, |hessianKernel 0 j y| := by
  have h := GreenFunction.setIntegral_preimage_coordinateReflection 0 (coordinateRectangle (-b)
      (-a) c d)
    (fun y ↦ |hessianKernel 0 j y|)
  rw [preimage_reflection_zero_rectangle] at h
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _) fun y _ ↦ ?_
  fin_cases j
  · simp [hessianKernel_zero_zero_coordinateReflection]
  · simp [hessianKernel_zero_one_coordinateReflection]

/-- `|K₁|` and `|K₂|` are even in `s₂`: `∫_{[a,b] × [c,d]} |Kᵢ| = ∫_{[a,b] × [-d,-c]} |Kᵢ|`. -/
theorem setIntegral_rectangle_abs_hessianKernel_reflect_one (j : Fin 2) (a b c d : ℝ) :
    ∫ y in coordinateRectangle a b c d, |hessianKernel 0 j y| =
      ∫ y in coordinateRectangle a b (-d) (-c), |hessianKernel 0 j y| := by
  have h := GreenFunction.setIntegral_preimage_coordinateReflection 1 (coordinateRectangle a b (-d)
      (-c))
    (fun y ↦ |hessianKernel 0 j y|)
  rw [preimage_reflection_one_rectangle] at h
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _) fun y _ ↦ ?_
  fin_cases j
  · simp [hessianKernel_zero_zero_coordinateReflection]
  · simp [hessianKernel_zero_one_coordinateReflection]

/-! ### Gradient kernels -/

/-- **`|∂ⱼΦ|` on a rectangle on one side of `{sⱼ = 0}`**: `∫_Q |∂ⱼΦ| = |∫_Q ∂ⱼΦ|`, since
`∂ⱼΦ = -sⱼ/(2π |s|²)` has the sign of `-sⱼ`. -/
theorem integral_rectangle_abs_gradientKernel (j : Fin 2) {a b c d : ℝ}
    (h : if j = 0 then (0 ≤ a ∨ b ≤ 0) else (0 ≤ c ∨ d ≤ 0)) :
    ∫ y in coordinateRectangle a b c d, |gradientKernel j y| =
      |∫ y in coordinateRectangle a b c d, gradientKernel j y| := by
  refine abs_setIntegral_of_sign (measurableSet_coordinateRectangle a b c d) ?_
  have hG : ∀ y : ℝ^2, gradientKernel j y = -(1 / (2 * Real.pi)) * y j / ‖y‖ ^ 2 :=
    gradientKernel_eq_div j
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  have key : ∀ (lo hi : ℝ), (0 ≤ lo ∨ hi ≤ 0) → (∀ y ∈ coordinateRectangle a b c d,
      lo ≤ y j ∧ y j ≤ hi) →
      (∀ y ∈ coordinateRectangle a b c d, 0 ≤ gradientKernel j y) ∨
        ∀ y ∈ coordinateRectangle a b c d, gradientKernel j y ≤ 0 := by
    intro lo hi hs hy
    rcases hs with hs | hs
    · exact Or.inr fun y hy' ↦ by
        rw [hG]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [(hy y hy').1])
          (by positivity)
    · exact Or.inl fun y hy' ↦ by
        rw [hG]; exact div_nonneg (by nlinarith [(hy y hy').2]) (by positivity)
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at h
    exact key a b h fun y hy ↦ hy.1
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at h
    exact key c d h fun y hy ↦ hy.2

end PotentialTheory.Planar
