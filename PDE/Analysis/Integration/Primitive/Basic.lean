/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The primitive of a real function

`primitive f x = ∫ s in 0..x, f s` is the primitive of `f : ℝ → ℝ` that vanishes at the origin.
For continuous `f` it has derivative `f` everywhere (`hasDerivAt_primitive`) and is continuous.
A function on `[0, T]` of the form `f₀ + ∫₀ᵗ g` with `|g| ≤ M` is `M`-Lipschitz
(`lipschitzWith_of_eq_integral`).
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Set

/-- The primitive `x ↦ ∫ s in 0..x, f s` of `f`, normalized to vanish at the origin. -/
def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, f s

@[simp] theorem primitive_zero (f : ℝ → ℝ) : primitive f 0 = 0 := by
  simp [primitive]

/-- The fundamental theorem of calculus for the primitive. -/
theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem continuous_primitive {f : ℝ → ℝ} (hf : Continuous f) : Continuous (primitive f) :=
  intervalIntegral.continuous_primitive (fun a b ↦ hf.intervalIntegrable a b) 0

/-- A function on `[0, T]` given by `f₀ + ∫₀ᵗ g` with `|g| ≤ M` is `M`-Lipschitz. -/
theorem lipschitzWith_of_eq_integral {T : ℝ} {f : Icc (0 : ℝ) T → ℝ} {g : ℝ → ℝ} {f₀ M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ t : Icc (0 : ℝ) T, IntervalIntegrable g volume 0 t)
    (hgb : ∀ s ∈ Icc (0 : ℝ) T, |g s| ≤ M)
    (hf : ∀ t : Icc (0 : ℝ) T, f t = f₀ + ∫ s in 0..(t : ℝ), g s) :
    LipschitzWith ⟨M, hM⟩ f := by
  apply LipschitzWith.of_dist_le_mul
  intro t t'
  rw [hf, hf, Real.dist_eq, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hg t) (hg t')]
  have hsub : uIoc (t' : ℝ) t ⊆ Icc 0 T := by
    intro s hs
    rcases le_total (t' : ℝ) t with hle | hle
    · rw [uIoc_of_le hle] at hs
      exact ⟨t'.property.1.trans hs.1.le, hs.2.trans t.property.2⟩
    · rw [uIoc_of_ge hle] at hs
      exact ⟨t.property.1.trans hs.1.le, hs.2.trans t'.property.2⟩
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (t' : ℝ)) (b := t)
    (f := g) (C := M) (fun s hs ↦ by rw [Real.norm_eq_abs]; exact hgb s (hsub hs))
  rw [Real.norm_eq_abs] at hn
  rw [Subtype.dist_eq, Real.dist_eq]
  convert hn using 2
  rfl

end PDE.Analysis
