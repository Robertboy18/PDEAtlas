/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Optimizing a logarithm against a power

Scalar facts behind the choice of the singular region in Chen and Hou, Part II, Supplementary
material II, Section 7.3.1 ((7.19)-(7.21), the estimate of the logarithm term, and the estimate
of `u_A/|x₁|^{1/2}`). A singular region of size `a` costs `C₁ log(b/a)` in the sup norm and
`C₃ √a` in the Hölder seminorm (Section 7.1.2). With the scale factors `C₃ λ^{a_n - b_n + 1/2}`
the optimal size is the choice `a = (2C₁/C₃)² λ^{2(b_n - a_n) - 1}` of (7.21), for which
`C₃ a^{1/2} λ^{-b_n + 1/2} = 2 C₁ λ^{-a_n}`.

## Main results

* `add_sqrt_le_log_div`: for `C₁, C₃ > 0` the choice `a* = (2C₁/C₃)²` gives
  `C₁ log(b/a*) + C₃ √a* = C₁ log(b/a*) + 2 C₁ ≤ C₁ log(b/a) + C₃ √a` for every `a > 0`.
* `log_mul_rpow_le`: for `β > 0 > C` and `b, d > 0`, `F(λ) = log(b/(d λ^{-β})) λ^C` increases up
  to `λ_c = (d/b)^{1/β} e^{-1/C}` and decreases after it, so `F(λ) ≤ F(max(λ_c, λ_*))` for
  `λ ≥ λ_* > 0`.
* `min_div_sqrt_mul_sqrt_le`: `min(C₁/√c, C₂ √c) ≤ √(C₁ C₂)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 7.1.2 and Section 7.3.1, (7.19)-(7.21).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

/-- **The optimal singular region**: for `C₁, C₃ > 0`, `b > 0` and `a > 0`, with
`a* = (2C₁/C₃)²`, `C₁ log(b/a*) + 2C₁ ≤ C₁ log(b/a) + C₃ √a`, and `C₃ √a* = 2C₁`. -/
theorem add_sqrt_le_log_div {C₁ C₃ b a : ℝ} (hC₁ : 0 < C₁) (hC₃ : 0 < C₃) (hb : 0 < b)
    (ha : 0 < a) :
    C₁ * Real.log (b / (2 * C₁ / C₃) ^ 2) + 2 * C₁ ≤ C₁ * Real.log (b / a) + C₃ * √a ∧
      C₃ * √((2 * C₁ / C₃) ^ 2) = 2 * C₁ := by
  set s := 2 * C₁ / C₃ with hs
  have hs0 : 0 < s := by positivity
  refine ⟨?_, by rw [Real.sqrt_sq hs0.le, hs]; field_simp⟩
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  -- `log(b/s²) - log(b/a) = 2 log(√a/s) ≤ 2 (√a/s - 1)`
  have hlog : Real.log (b / s ^ 2) - Real.log (b / a) = 2 * Real.log (√a / s) := by
    rw [Real.log_div hb.ne' (by positivity), Real.log_div hb.ne' ha.ne', Real.log_div hsa.ne'
      hs0.ne', Real.log_pow, Real.log_sqrt ha.le]
    push_cast; ring
  have hle := Real.log_le_sub_one_of_pos (div_pos hsa hs0)
  have hC₃s : C₃ = 2 * C₁ / s := by rw [hs]; field_simp
  have key : C₁ * (Real.log (b / s ^ 2) - Real.log (b / a)) ≤ C₃ * √a - 2 * C₁ := by
    rw [hlog, hC₃s]
    have : 2 * C₁ / s * √a - 2 * C₁ = 2 * C₁ * (√a / s - 1) := by field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * C₁)]
  linarith

/-- **The logarithmic term**: for `β > 0 > C` and `b, d > 0`, `F(λ) = log(b / (d λ^{-β})) λ^C`
satisfies `F(λ) ≤ F(max(λ_c, λ_*))` for `λ ≥ λ_* > 0`, `λ_c = (d/b)^{1/β} e^{-1/C}`. -/
theorem log_mul_rpow_le {b d β C l₀ l : ℝ} (hb : 0 < b) (hd : 0 < d) (hβ : 0 < β) (hC : C < 0)
    (hl₀ : 0 < l₀) (hl : l₀ ≤ l) :
    Real.log (b / (d * l ^ (-β))) * l ^ C ≤
      Real.log (b / (d * (max ((d / b) ^ (1 / β) * Real.exp (-1 / C)) l₀) ^ (-β))) *
        (max ((d / b) ^ (1 / β) * Real.exp (-1 / C)) l₀) ^ C := by
  set F : ℝ → ℝ := fun l ↦ Real.log (b / (d * l ^ (-β))) * l ^ C with hF
  set lc := (d / b) ^ (1 / β) * Real.exp (-1 / C) with hlc
  have hlc0 : 0 < lc := by positivity
  -- `F(λ) = (log(b/d) + β log λ) λ^C` and its derivative
  have hFeq : ∀ l, 0 < l → F l = (Real.log (b / d) + β * Real.log l) * l ^ C := fun l hl ↦ by
    simp only [hF]
    rw [Real.log_div hb.ne' (by positivity), Real.log_mul hd.ne' (by positivity),
      Real.log_rpow hl, Real.log_div hb.ne' hd.ne']
    ring
  have hd' : ∀ l, 0 < l → HasDerivAt (fun l ↦ (Real.log (b / d) + β * Real.log l) * l ^ C)
      (l ^ (C - 1) * (C * (Real.log (b / d) + β * Real.log l) + β)) l := fun l hl ↦ by
    have h1 := ((Real.hasDerivAt_log hl.ne').const_mul β).const_add (Real.log (b / d))
    have h2 := Real.hasDerivAt_rpow_const (p := C) (Or.inl hl.ne')
    refine (h1.mul h2).congr_deriv ?_
    rw [Real.rpow_sub hl, Real.rpow_one]
    field_simp
    ring
  -- the sign of the derivative changes at `λ_c`
  have hcrit : ∀ l, 0 < l → (C * (Real.log (b / d) + β * Real.log l) + β ≤ 0 ↔ lc ≤ l) := by
    intro l hl
    have hβlc : β * Real.log lc = -Real.log (b / d) - β / C := by
      rw [hlc, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
        Real.log_exp, Real.log_div hd.ne' hb.ne', Real.log_div hb.ne' hd.ne']
      field_simp
      ring
    have e1 : C * (Real.log (b / d) + β * Real.log l) + β ≤ 0 ↔
        -β / C ≤ Real.log (b / d) + β * Real.log l := by
      rw [div_le_iff_of_neg hC]
      constructor <;> intro h <;> linarith
    rw [e1, ← Real.log_le_log_iff hlc0 hl, neg_div]
    constructor
    · intro h
      have h2 : β * Real.log lc ≤ β * Real.log l := by rw [hβlc]; linarith
      exact le_of_mul_le_mul_left h2 hβ
    · intro h
      have h2 := mul_le_mul_of_nonneg_left h hβ.le
      rw [hβlc] at h2
      linarith
  have hmono : MonotoneOn F (Ioc 0 lc) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 lc) ?_ ?_ ?_
    · exact fun l hl ↦ ((hd' l hl.1).continuousAt.congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioi_mem_nhds hl.1) fun m hm ↦ hFeq m hm)).continuousWithinAt
    · intro l hl
      rw [interior_Ioc] at hl
      exact ((hd' l hl.1).congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hl.1)
        fun m hm ↦ hFeq m hm)).differentiableAt.differentiableWithinAt
    · intro l hl
      rw [interior_Ioc] at hl
      rw [((hd' l hl.1).congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hl.1)
        fun m hm ↦ hFeq m hm)).deriv]
      refine mul_nonneg (Real.rpow_nonneg hl.1.le _) ?_
      by_contra hneg
      exact absurd ((hcrit l hl.1).1 (not_le.1 hneg).le) (not_le.2 hl.2)
  have hanti : AntitoneOn F (Ici lc) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici lc) ?_ ?_ ?_
    · exact fun l hl ↦ ((hd' l (hlc0.trans_le hl)).continuousAt.congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioi_mem_nhds (hlc0.trans_le hl)) fun m hm ↦
          hFeq m hm)).continuousWithinAt
    · intro l hl
      rw [interior_Ici] at hl
      have hl0 : 0 < l := hlc0.trans hl
      exact ((hd' l hl0).congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hl0)
        fun m hm ↦ hFeq m hm)).differentiableAt.differentiableWithinAt
    · intro l hl
      rw [interior_Ici] at hl
      have hl0 : 0 < l := hlc0.trans hl
      rw [((hd' l hl0).congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hl0)
        fun m hm ↦ hFeq m hm)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hl0.le _)
        ((hcrit l hl0).2 hl.le)
  change F l ≤ F (max lc l₀)
  have hl0 : 0 < l := hl₀.trans_le hl
  rcases le_total lc l₀ with h | h
  · rw [max_eq_right h]
    exact hanti (mem_Ici.2 h) (mem_Ici.2 (h.trans hl)) hl
  · rw [max_eq_left h]
    rcases le_total l lc with h' | h'
    · exact hmono ⟨hl0, h'⟩ ⟨hlc0, le_rfl⟩ h'
    · exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 h') h'

/-- `min(C₁/√c, C₂ √c) ≤ √(C₁ C₂)` for `C₁, C₂ ≥ 0` and `c > 0`. -/
theorem min_div_sqrt_mul_sqrt_le {C₁ C₂ c : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc : 0 < c) :
    min (C₁ / √c) (C₂ * √c) ≤ √(C₁ * C₂) := by
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  have hprod : C₁ / √c * (C₂ * √c) = C₁ * C₂ := by field_simp
  have hm0 : 0 ≤ min (C₁ / √c) (C₂ * √c) := le_min (by positivity) (by positivity)
  rw [← hprod, ← Real.sqrt_sq hm0]
  refine Real.sqrt_le_sqrt ?_
  rw [sq]
  exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 (by positivity)

end PDE.Analysis
