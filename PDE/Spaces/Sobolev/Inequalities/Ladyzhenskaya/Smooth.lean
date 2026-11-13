/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Spaces.Sobolev.Inequalities.Ladyzhenskaya.LineProduct

/-!
# Ladyzhenskaya's inequality for compactly supported `C¹` functions on `ℝ³`

For a compactly supported `C¹` function `u` on `ℝ^n` and every coordinate direction `j`,
`u(x)² ≤ ∫ |u ∂ⱼu|` along the coordinate line through `x` in direction `j`. In Cartesian
coordinates `ℝ³ ≅ ℝ × ℝ × ℝ` the three-slice estimate then gives Ladyzhenskaya's inequality

`(∫ u⁴)² ≤ (∫ u²) (∫ (∂₀u)²) (∫ (∂₁u)²) (∫ (∂₂u)²)`,

that is `‖u‖₄⁴ ≤ ‖u‖₂ ‖∂₀u‖₂ ‖∂₁u‖₂ ‖∂₂u‖₂`, with constant one.

## Main results

* `enorm_sq_le_lintegral_coordinateLine`: the line bound at a point of `ℝ^n`.
* `cartesianEquivThree`, `measurePreserving_cartesianEquivThree`: Cartesian coordinates on `ℝ^3`
  preserve Lebesgue measure.
* `lintegral_enorm_pow_four_sq_le_of_contDiff`: Ladyzhenskaya's inequality for compactly
  supported `C¹` functions on `ℝ^3`.
-/

@[expose] public section

open MeasureTheory Set PDE
open scoped ENNReal

noncomputable section

namespace SobolevSpace.Inequalities

/-- The line bound in direction `j` at a point of `ℝ^n`: `u(x)²` is at most the integral of
`|u ∂ⱼu|` along the coordinate line through `x` in direction `j`. -/
theorem enorm_sq_le_lintegral_coordinateLine {n : ℕ} {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) (j : Fin n) (x : ℝ^n) :
    ‖u x‖ₑ ^ 2 ≤
      ∫⁻ s, ‖u (coordinateLine j x s)‖ₑ * ‖(∂[j] u) (coordinateLine j x s)‖ₑ := by
  let φ : ℝ → ℝ := u ∘ coordinateLine j x
  have hφ : ContDiff ℝ 1 φ :=
    hu.comp ((contDiff_coordinateLine j x).of_le (by exact_mod_cast le_top))
  have hφc : HasCompactSupport φ := by
    let K : Set ℝ := (fun y : ℝ^n ↦ y j) '' tsupport u
    have hK : IsCompact K := huc.image (EuclideanSpace.proj j).continuous
    refine HasCompactSupport.intro hK fun s hs ↦ ?_
    by_contra hne
    exact hs ⟨coordinateLine j x s, subset_tsupport _ hne, coordinateLine_apply_same j x s⟩
  have hderiv (s : ℝ) : deriv φ s = (∂[j] u) (coordinateLine j x s) := by
    have hd := ((hu.differentiable one_ne_zero) (coordinateLine j x s)).hasFDerivAt
      |>.comp_hasDerivAt s (hasDerivAt_coordinateLine j x s)
    rw [hd.deriv]
    rfl
  have h := enorm_sq_le_lintegral_enorm_mul_enorm_deriv hφ hφc (x j)
  calc ‖u x‖ₑ ^ 2 = ‖φ (x j)‖ₑ ^ 2 := by simp [φ]
    _ ≤ ∫⁻ s, ‖φ s‖ₑ * ‖deriv φ s‖ₑ := h
    _ = _ := lintegral_congr fun s ↦ by rw [hderiv]; rfl

/-- Cartesian coordinates `(a, b, c) ↦ (a, b, c)` from `ℝ × ℝ × ℝ` to `ℝ^3`. -/
def cartesianEquivThree : ℝ × ℝ × ℝ ≃ᵐ ℝ^3 :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm.trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

/-- Cartesian coordinates of a point of `ℝ^3`. -/
theorem cartesianEquivThree_apply (p : ℝ × ℝ × ℝ) :
    cartesianEquivThree p = WithLp.toLp 2 ![p.1, p.2.1, p.2.2] := by
  ext i
  fin_cases i <;> rfl

/-- The first Cartesian coordinate. -/
@[simp]
theorem cartesianEquivThree_apply_zero (p : ℝ × ℝ × ℝ) : cartesianEquivThree p 0 = p.1 := by
  simp [cartesianEquivThree_apply]

/-- The second Cartesian coordinate. -/
@[simp]
theorem cartesianEquivThree_apply_one (p : ℝ × ℝ × ℝ) : cartesianEquivThree p 1 = p.2.1 := by
  simp [cartesianEquivThree_apply]

/-- The third Cartesian coordinate. -/
@[simp]
theorem cartesianEquivThree_apply_two (p : ℝ × ℝ × ℝ) : cartesianEquivThree p 2 = p.2.2 := by
  simp [cartesianEquivThree_apply]

/-- Cartesian coordinates preserve Lebesgue measure. -/
theorem measurePreserving_cartesianEquivThree : MeasurePreserving cartesianEquivThree := by
  have h₁ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm :
        ℝ × ℝ × ℝ ≃ᵐ ℝ × (Fin 2 → ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ).symm
  have h₂ := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm
  have h₃ : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) :=
    PiLp.volume_preserving_toLp (Fin 3)
  exact (h₁.trans h₂).trans h₃

/-- Moving along the first coordinate line changes only the first Cartesian coordinate. -/
theorem coordinateLine_zero_cartesianEquivThree (a b c s : ℝ) :
    coordinateLine 0 (cartesianEquivThree (a, b, c)) s = cartesianEquivThree (s, b, c) := by
  ext i
  fin_cases i <;> simp [coordinateLine]

/-- Moving along the second coordinate line changes only the second Cartesian coordinate. -/
theorem coordinateLine_one_cartesianEquivThree (a b c s : ℝ) :
    coordinateLine 1 (cartesianEquivThree (a, b, c)) s = cartesianEquivThree (a, s, c) := by
  ext i
  fin_cases i <;> simp [coordinateLine]

/-- Moving along the third coordinate line changes only the third Cartesian coordinate. -/
theorem coordinateLine_two_cartesianEquivThree (a b c s : ℝ) :
    coordinateLine 2 (cartesianEquivThree (a, b, c)) s = cartesianEquivThree (a, b, s) := by
  ext i
  fin_cases i <;> simp [coordinateLine]

/-- Lower Lebesgue integrals over `ℝ^3` in Cartesian coordinates. -/
theorem lintegral_comp_cartesianEquivThree (F : ℝ^3 → ℝ≥0∞) :
    ∫⁻ p, F (cartesianEquivThree p) ∂(volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) = ∫⁻ x, F x :=
  measurePreserving_cartesianEquivThree.lintegral_comp_emb cartesianEquivThree.measurableEmbedding F

/-- Ladyzhenskaya's inequality on `ℝ³` for compactly supported `C¹` functions, with
constant one: `(∫ u⁴)² ≤ (∫ u²) (∫ (∂₀u)²) (∫ (∂₁u)²) (∫ (∂₂u)²)`. -/
theorem lintegral_enorm_pow_four_sq_le_of_contDiff {u : ℝ^3 → ℝ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    (∫⁻ x, ‖u x‖ₑ ^ 4) ^ 2 ≤
      (∫⁻ x, ‖u x‖ₑ ^ 2) * ∏ j : Fin 3, ∫⁻ x, ‖(∂[j] u) x‖ₑ ^ 2 := by
  have hcont (j : Fin 3) : Continuous fun x ↦ (∂[j] u) x := by
    have hfd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    simpa [partialDeriv] using
      hfd.clm_apply (continuous_const (y := EuclideanSpace.single j (1 : ℝ)))
  let g : ℝ × ℝ × ℝ → ℝ≥0∞ := fun p ↦ ‖u (cartesianEquivThree p)‖ₑ
  let d : Fin 3 → ℝ × ℝ × ℝ → ℝ≥0∞ := fun j p ↦ ‖(∂[j] u) (cartesianEquivThree p)‖ₑ
  have hg : Measurable g :=
    (hu.continuous.measurable.comp cartesianEquivThree.measurable).enorm
  have hd (j : Fin 3) : Measurable (d j) :=
    ((hcont j).measurable.comp cartesianEquivThree.measurable).enorm
  have h₀ : ∀ a q, g (a, q) ^ 2 ≤ ∫⁻ a', g (a', q) * d 0 (a', q) := by
    rintro a ⟨b, c⟩
    simpa only [g, d, coordinateLine_zero_cartesianEquivThree] using
      enorm_sq_le_lintegral_coordinateLine hu huc 0 (cartesianEquivThree (a, b, c))
  have h₁ : ∀ a b c, g (a, b, c) ^ 2 ≤ ∫⁻ b', g (a, b', c) * d 1 (a, b', c) := by
    intro a b c
    simpa only [g, d, coordinateLine_one_cartesianEquivThree] using
      enorm_sq_le_lintegral_coordinateLine hu huc 1 (cartesianEquivThree (a, b, c))
  have h₂ : ∀ a b c, g (a, b, c) ^ 2 ≤ ∫⁻ c', g (a, b, c') * d 2 (a, b, c') := by
    intro a b c
    simpa only [g, d, coordinateLine_two_cartesianEquivThree] using
      enorm_sq_le_lintegral_coordinateLine hu huc 2 (cartesianEquivThree (a, b, c))
  have h := lintegral_pow_four_sq_le_of_lineBounds hg (hd 0) (hd 1) (hd 2) h₀ h₁ h₂
  simp only [g, d, lintegral_comp_cartesianEquivThree (fun x ↦ ‖u x‖ₑ ^ 4),
    lintegral_comp_cartesianEquivThree (fun x ↦ ‖u x‖ₑ ^ 2),
    lintegral_comp_cartesianEquivThree (fun x ↦ ‖(∂[0] u) x‖ₑ ^ 2),
    lintegral_comp_cartesianEquivThree (fun x ↦ ‖(∂[1] u) x‖ₑ ^ 2),
    lintegral_comp_cartesianEquivThree (fun x ↦ ‖(∂[2] u) x‖ₑ ^ 2)] at h
  rw [Fin.prod_univ_three]
  calc _ ≤ _ := h
    _ = _ := by ring

end SobolevSpace.Inequalities
