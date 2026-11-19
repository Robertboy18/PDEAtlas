/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Taylor bounds for the even part of a function

For a function `f` of one real variable, the even combination `f(x) + f(-x) - 2 f(0)` has
vanishing first and third derivatives at the origin. Hence it is bounded by `x² ‖f''‖`, and
after removing the quadratic term `x² f''(0)` by `x⁴ ‖f⁽⁴⁾‖ / 12`, with the supremum taken over
`[-x, x]`. This is Lemma B.1 of Chen and Hou, Part II, Appendix B.1.

Derivatives are given as explicit functions (`HasDerivAt f (f₁ t) t` and so on), and the
values may lie in any real normed space, so the bounds apply to complex-valued restrictions of
holomorphic functions to lines.

## Main results

* `norm_le_of_norm_deriv_le_pow`: a function vanishing at `0` whose derivative is bounded by
  `c t^n` on `[0, x]` is bounded by `c x^(n+1)/(n+1)`.
* `norm_add_neg_sub_two_smul_le`: `‖f x + f (-x) - 2 f 0‖ ≤ x² M` if `‖f''‖ ≤ M` on `[-x, x]`.
* `norm_add_neg_sub_two_smul_sub_sq_smul_le`: `‖f x + f (-x) - 2 f 0 - x² f''(0)‖ ≤ x⁴ M / 12`
  if `‖f⁽⁴⁾‖ ≤ M` on `[-x, x]`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix B.1,
  Lemma B.1. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reflection rule for derivatives: `t ↦ g (-t)` has derivative `-g'` at `t`. -/
private theorem hasDerivAt_comp_neg {g : ℝ → E} {g' : E} {t : ℝ}
    (h : HasDerivAt g g' (-t)) : HasDerivAt (fun s ↦ g (-s)) (-g') t := by
  have h' := h.scomp t (hasDerivAt_neg t)
  rw [neg_one_smul] at h'
  exact h'

/-- A function vanishing at the origin, with derivative bounded by `c t ^ n` on `[0, x]`, is
bounded by `c x ^ (n + 1) / (n + 1)` at `x`. -/
theorem norm_le_of_norm_deriv_le_pow {g g' : ℝ → E} {x c : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hg0 : g 0 = 0) (hg : ∀ t ∈ Icc 0 x, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc 0 x, ‖g' t‖ ≤ c * t ^ n) :
    ‖g x‖ ≤ c * x ^ (n + 1) / (n + 1) := by
  have hB (t : ℝ) : HasDerivAt (fun s : ℝ ↦ c * s ^ (n + 1) / (n + 1)) (c * t ^ n) t := by
    have h := ((hasDerivAt_pow (n + 1) t).const_mul c).div_const ((n : ℝ) + 1)
    convert h using 1
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  have hcont : ContinuousOn g (Icc 0 x) := fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun t ht ↦ (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ hB
    (fun t ht ↦ hbound t (Ico_subset_Icc_self ht)) (right_mem_Icc.mpr hx)
  simp [hg0]

/-- **Even second-order Taylor bound** (Chen–Hou II, Lemma B.1, first estimate).
If `‖f''‖ ≤ M` on `[-x, x]`, then `‖f(x) + f(-x) - 2 f(0)‖ ≤ x² M`. -/
theorem norm_add_neg_sub_two_smul_le {f f₁ f₂ : ℝ → E} {x M : ℝ} (hx : 0 ≤ x)
    (hf : ∀ t ∈ Icc (-x) x, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (-x) x, HasDerivAt f₁ (f₂ t) t)
    (hM : ∀ t ∈ Icc (-x) x, ‖f₂ t‖ ≤ M) :
    ‖f x + f (-x) - (2 : ℝ) • f 0‖ ≤ x ^ 2 * M := by
  have hmem {t : ℝ} (ht : t ∈ Icc 0 x) : t ∈ Icc (-x) x := ⟨by linarith [ht.1], ht.2⟩
  have hmemNeg {t : ℝ} (ht : t ∈ Icc 0 x) : -t ∈ Icc (-x) x := ⟨by linarith [ht.2], by
    linarith [ht.1]⟩
  -- the odd first derivative `f₁ t - f₁ (-t)`
  have hd₁ : ∀ t ∈ Icc 0 x, HasDerivAt (fun s ↦ f₁ s - f₁ (-s)) (f₂ t + f₂ (-t)) t := by
    intro t ht
    exact ((hf₁ t (hmem ht)).sub (hasDerivAt_comp_neg (hf₁ (-t) (hmemNeg ht)))).congr_deriv
      (sub_neg_eq_add _ _)
  have hb₁ : ∀ t ∈ Icc 0 x, ‖f₁ t - f₁ (-t)‖ ≤ (2 * M) * t ^ 1 / (0 + 1) := by
    intro t ht
    have := norm_le_of_norm_deriv_le_pow (g := fun s ↦ f₁ s - f₁ (-s)) (c := 2 * M) 0 ht.1
      (by simp) (fun s hs ↦ hd₁ s ⟨hs.1, hs.2.trans ht.2⟩) (fun s hs ↦ by
        have hs' : s ∈ Icc 0 x := ⟨hs.1, hs.2.trans ht.2⟩
        calc ‖f₂ s + f₂ (-s)‖ ≤ ‖f₂ s‖ + ‖f₂ (-s)‖ := norm_add_le _ _
          _ ≤ M + M := add_le_add (hM s (hmem hs')) (hM (-s) (hmemNeg hs'))
          _ = 2 * M * s ^ 0 := by ring)
    simpa using this
  have hd₀ : ∀ t ∈ Icc 0 x, HasDerivAt (fun s ↦ f s + f (-s) - (2 : ℝ) • f 0)
      (f₁ t - f₁ (-t)) t := by
    intro t ht
    exact (((hf t (hmem ht)).add (hasDerivAt_comp_neg (hf (-t) (hmemNeg ht)))).sub_const
      ((2 : ℝ) • f 0)).congr_deriv (by abel)
  have := norm_le_of_norm_deriv_le_pow (g := fun s ↦ f s + f (-s) - (2 : ℝ) • f 0)
    (c := 2 * M) 1 hx (by simp [two_smul]) hd₀ (fun t ht ↦ by simpa using hb₁ t ht)
  calc ‖f x + f (-x) - (2 : ℝ) • f 0‖ ≤ 2 * M * x ^ (1 + 1) / (1 + 1) := by exact_mod_cast this
    _ = x ^ 2 * M := by ring

/-- **Even fourth-order Taylor bound** (Chen–Hou II, Lemma B.1, second estimate).
If `‖f⁽⁴⁾‖ ≤ M` on `[-x, x]`, then `‖f(x) + f(-x) - 2 f(0) - x² f''(0)‖ ≤ x⁴ M / 12`. -/
theorem norm_add_neg_sub_two_smul_sub_sq_smul_le {f f₁ f₂ f₃ f₄ : ℝ → E} {x M : ℝ}
    (hx : 0 ≤ x)
    (hf : ∀ t ∈ Icc (-x) x, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (-x) x, HasDerivAt f₁ (f₂ t) t)
    (hf₂ : ∀ t ∈ Icc (-x) x, HasDerivAt f₂ (f₃ t) t)
    (hf₃ : ∀ t ∈ Icc (-x) x, HasDerivAt f₃ (f₄ t) t)
    (hM : ∀ t ∈ Icc (-x) x, ‖f₄ t‖ ≤ M) :
    ‖f x + f (-x) - (2 : ℝ) • f 0 - x ^ 2 • f₂ 0‖ ≤ x ^ 4 / 12 * M := by
  have hmem {t : ℝ} (ht : t ∈ Icc 0 x) : t ∈ Icc (-x) x := ⟨by linarith [ht.1], ht.2⟩
  have hmemNeg {t : ℝ} (ht : t ∈ Icc 0 x) : -t ∈ Icc (-x) x := ⟨by linarith [ht.2], by
    linarith [ht.1]⟩
  have hsub {t s : ℝ} (ht : t ∈ Icc 0 x) (hs : s ∈ Icc 0 t) : s ∈ Icc 0 x :=
    ⟨hs.1, hs.2.trans ht.2⟩
  -- third derivative of the even part
  have hd₃ : ∀ t ∈ Icc 0 x, HasDerivAt (fun s ↦ f₃ s - f₃ (-s)) (f₄ t + f₄ (-t)) t := by
    intro t ht
    exact ((hf₃ t (hmem ht)).sub (hasDerivAt_comp_neg (hf₃ (-t) (hmemNeg ht)))).congr_deriv
      (sub_neg_eq_add _ _)
  have hb₃ : ∀ t ∈ Icc 0 x, ‖f₃ t - f₃ (-t)‖ ≤ 2 * M * t ^ 1 := by
    intro t ht
    have := norm_le_of_norm_deriv_le_pow (g := fun s ↦ f₃ s - f₃ (-s)) (c := 2 * M) 0 ht.1
      (by simp) (fun s hs ↦ hd₃ s (hsub ht hs)) (fun s hs ↦ by
        calc ‖f₄ s + f₄ (-s)‖ ≤ ‖f₄ s‖ + ‖f₄ (-s)‖ := norm_add_le _ _
          _ ≤ M + M := add_le_add (hM s (hmem (hsub ht hs))) (hM (-s) (hmemNeg (hsub ht hs)))
          _ = 2 * M * s ^ 0 := by ring)
    simpa using this
  -- second derivative of the even part
  have hd₂ : ∀ t ∈ Icc 0 x, HasDerivAt (fun s ↦ f₂ s + f₂ (-s) - (2 : ℝ) • f₂ 0)
      (f₃ t - f₃ (-t)) t := by
    intro t ht
    exact (((hf₂ t (hmem ht)).add (hasDerivAt_comp_neg (hf₂ (-t) (hmemNeg ht)))).sub_const
      ((2 : ℝ) • f₂ 0)).congr_deriv (by abel)
  have hb₂ : ∀ t ∈ Icc 0 x, ‖f₂ t + f₂ (-t) - (2 : ℝ) • f₂ 0‖ ≤ M * t ^ 2 := by
    intro t ht
    have := norm_le_of_norm_deriv_le_pow
      (g := fun s ↦ f₂ s + f₂ (-s) - (2 : ℝ) • f₂ 0) (c := 2 * M) 1 ht.1
      (by simp [two_smul]) (fun s hs ↦ hd₂ s (hsub ht hs)) (fun s hs ↦ hb₃ s (hsub ht hs))
    calc _ ≤ 2 * M * t ^ (1 + 1) / ((1 : ℕ) + 1) := this
      _ = M * t ^ 2 := by push_cast; ring
  -- first derivative of the even part
  have hd₁ : ∀ t ∈ Icc 0 x, HasDerivAt (fun s ↦ f₁ s - f₁ (-s) - (2 * s) • f₂ 0)
      (f₂ t + f₂ (-t) - (2 : ℝ) • f₂ 0) t := by
    intro t ht
    have h := (hf₁ t (hmem ht)).sub (hasDerivAt_comp_neg (hf₁ (-t) (hmemNeg ht)))
    have hl : HasDerivAt (fun s : ℝ ↦ (2 * s) • f₂ 0) ((2 : ℝ) • f₂ 0) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).smul_const (f₂ 0)
    exact (h.sub hl).congr_deriv (by abel)
  have hb₁ : ∀ t ∈ Icc 0 x, ‖f₁ t - f₁ (-t) - (2 * t) • f₂ 0‖ ≤ M / 3 * t ^ 3 := by
    intro t ht
    have := norm_le_of_norm_deriv_le_pow
      (g := fun s ↦ f₁ s - f₁ (-s) - (2 * s) • f₂ 0) (c := M) 2 ht.1
      (by simp) (fun s hs ↦ hd₁ s (hsub ht hs)) (fun s hs ↦ hb₂ s (hsub ht hs))
    calc _ ≤ M * t ^ (2 + 1) / ((2 : ℕ) + 1) := this
      _ = M / 3 * t ^ 3 := by push_cast; ring
  -- the even part itself
  have hd₀ : ∀ t ∈ Icc 0 x, HasDerivAt
      (fun s ↦ f s + f (-s) - (2 : ℝ) • f 0 - s ^ 2 • f₂ 0)
      (f₁ t - f₁ (-t) - (2 * t) • f₂ 0) t := by
    intro t ht
    have h := ((hf t (hmem ht)).add (hasDerivAt_comp_neg (hf (-t) (hmemNeg ht)))).sub_const
      ((2 : ℝ) • f 0)
    have hl : HasDerivAt (fun s : ℝ ↦ s ^ 2 • f₂ 0) ((2 * t) • f₂ 0) t := by
      simpa using (hasDerivAt_pow 2 t).smul_const (f₂ 0)
    exact (h.sub hl).congr_deriv (by abel)
  have := norm_le_of_norm_deriv_le_pow
    (g := fun s ↦ f s + f (-s) - (2 : ℝ) • f 0 - s ^ 2 • f₂ 0) (c := M / 3) 3 hx
    (by simp [two_smul]) hd₀ hb₁
  calc _ ≤ M / 3 * x ^ (3 + 1) / ((3 : ℕ) + 1) := this
    _ = x ^ 4 / 12 * M := by push_cast; ring

end PDE.Analysis.Calculus
