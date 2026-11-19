/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.FaaDiBrunoBounds
public import Mathlib.Analysis.Calculus.MeanValue
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Hölder bounds of Lipschitz maps and of products

Elementary facts about the `α`-Hölder condition `‖F y - F z‖ ≤ M ‖y - z‖^α` on a set `S`, for
`0 < α ≤ 1`. A product of Hölder maps is Hölder. For iterated derivatives within a convex set
`S` with unique differentiability, the lower derivatives of a `C^n` map are Lipschitz, hence
Hölder when they are bounded (`norm_sub_le_max_mul_rpow`), and a bounded bilinear map `B`
applied to a `C^{n+1}` map `w` and a `C^{n,α}` map `f` has `C^{n,α}` bounds.

## Main results

* `norm_smul_sub_smul_le`: the product `h • F` of a scalar map `h` with `|h| ≤ Bh` and Hölder
  constant `Mh` and a map `F` with `‖F‖ ≤ BF` and Hölder constant `MF` has Hölder constant
  `Bh MF + BF Mh`.
* `norm_iteratedFDerivWithin_sub_le_of_convex`: a derivative of order `j < n` of a `C^n` map is
  Lipschitz with the bound of the derivative of order `j + 1`.
* `norm_iteratedFDerivWithin_sub_le_rpow_of_convex`: such a derivative is `α`-Hölder when the
  derivatives of orders `j` and `j + 1` are bounded.
* `norm_iteratedFDerivWithin_bilinear_le_mul`: with derivatives of `w` at most `Mw` and of `f` at
  most `Mf`, the derivatives of order `j` of `B(w, f)` are at most `‖B‖ 2^j Mw Mf`.
* `norm_iteratedFDerivWithin_bilinear_sub_le_rpow`: when moreover `Mf` bounds the Hölder
  constant of `Dⁿ f`, the derivative of order `n` of `B(w, f)` is `α`-Hölder with constant
  `6 ‖B‖ 2^n Mw Mf`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

variable {E G : Type*} [SeminormedAddCommGroup E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Hölder bound of a product**: `‖h y • F y - h z • F z‖ ≤ (Bh MF + BF Mh) ‖y - z‖^α` when
`|h| ≤ Bh`, `‖F‖ ≤ BF` and `h`, `F` are `α`-Hölder with constants `Mh`, `MF` on `S`. -/
theorem norm_smul_sub_smul_le {S : Set E} {h : E → ℝ} {F : E → G} {Bh BF Mh MF α : ℝ}
    (hh : ∀ y ∈ S, |h y| ≤ Bh) (hF : ∀ y ∈ S, ‖F y‖ ≤ BF)
    (hMh : ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Mh * ‖y - z‖ ^ α)
    (hMF : ∀ y ∈ S, ∀ z ∈ S, ‖F y - F z‖ ≤ MF * ‖y - z‖ ^ α) {y z : E} (hy : y ∈ S)
    (hz : z ∈ S) :
    ‖h y • F y - h z • F z‖ ≤ (Bh * MF + BF * Mh) * ‖y - z‖ ^ α := by
  have heq : h y • F y - h z • F z = h y • (F y - F z) + (h y - h z) • F z := by
    rw [smul_sub, sub_smul]; abel
  have h1 : ‖h y • (F y - F z)‖ ≤ Bh * (MF * ‖y - z‖ ^ α) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hh y hy) (hMF y hy z hz) (norm_nonneg _)
      ((abs_nonneg _).trans (hh y hy))
  have h2 : ‖(h y - h z) • F z‖ ≤ Mh * ‖y - z‖ ^ α * BF := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hMh y hy z hz) (hF z hz) (norm_nonneg _)
      ((abs_nonneg _).trans (hMh y hy z hz))
  rw [heq]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ Bh * (MF * ‖y - z‖ ^ α) + Mh * ‖y - z‖ ^ α * BF := add_le_add h1 h2
    _ = (Bh * MF + BF * Mh) * ‖y - z‖ ^ α := by ring

section Convex

variable {D E' : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- **Lipschitz bound of a lower derivative**: on a convex set with unique differentiability, a
derivative of order `j < N` of a `C^N` map is Lipschitz with the bound of the derivative of
order `j + 1`. -/
theorem norm_iteratedFDerivWithin_sub_le_of_convex {F : D → E'} {N : WithTop ℕ∞} {j : ℕ}
    {S : Set D} (hS : Convex ℝ S) (hu : UniqueDiffOn ℝ S) (hF : ContDiffOn ℝ N F S)
    (hj : (j : WithTop ℕ∞) < N) {M : ℝ}
    (hM : ∀ x ∈ S, ‖iteratedFDerivWithin ℝ (j + 1) F S x‖ ≤ M) {x y : D} (hx : x ∈ S)
    (hy : y ∈ S) :
    ‖iteratedFDerivWithin ℝ j F S x - iteratedFDerivWithin ℝ j F S y‖ ≤ M * ‖x - y‖ :=
  hS.norm_image_sub_le_of_norm_fderivWithin_le (hF.differentiableOn_iteratedFDerivWithin hj hu)
    (fun z hz ↦ by rw [norm_fderivWithin_iteratedFDerivWithin]; exact hM z hz) hy hx

/-- **Hölder bound of a lower derivative**: on a convex set with unique differentiability, a
derivative of order `j < N` of a `C^N` map whose derivatives of orders `j` and `j + 1` are at
most `M` is `α`-Hölder with constant `3M`, for `0 < α ≤ 1`. -/
theorem norm_iteratedFDerivWithin_sub_le_rpow_of_convex {F : D → E'} {N : WithTop ℕ∞} {j : ℕ}
    {S : Set D} (hS : Convex ℝ S) (hu : UniqueDiffOn ℝ S) (hF : ContDiffOn ℝ N F S)
    (hj : (j : WithTop ℕ∞) < N) {M α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hM₀ : ∀ x ∈ S, ‖iteratedFDerivWithin ℝ j F S x‖ ≤ M)
    (hM : ∀ x ∈ S, ‖iteratedFDerivWithin ℝ (j + 1) F S x‖ ≤ M) {x y : D} (hx : x ∈ S)
    (hy : y ∈ S) :
    ‖iteratedFDerivWithin ℝ j F S x - iteratedFDerivWithin ℝ j F S y‖ ≤ 3 * M * ‖x - y‖ ^ α := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM₀ x hx)
  have h := norm_sub_le_max_mul_rpow (S := S) (f := iteratedFDerivWithin ℝ j F S)
    (fun x hx y hy ↦ by
      rw [dist_eq_norm]; exact norm_iteratedFDerivWithin_sub_le_of_convex hS hu hF hj hM hx hy)
    hM₀ hα.le hα1 hx hy
  rw [max_eq_right (by linarith), dist_eq_norm] at h
  linarith [mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg (x - y)) α)]

end Convex

section Derivatives

universe u

variable {D E' F' G' : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G']
  [NormedSpace ℝ G']

/-- **Size of the derivatives of a bilinear product**: `‖Dⁿ B(w, f)‖ ≤ ‖B‖ 2ⁿ Mw Mf` when the
derivatives of orders at most `n` of `w` and `f` are at most `Mw` and `Mf`. -/
theorem norm_iteratedFDerivWithin_bilinear_le_mul (B : E' →L[ℝ] F' →L[ℝ] G') {w : D → E'}
    {f : D → F'} {n : ℕ} {S : Set D} (hu : UniqueDiffOn ℝ S) (hw : ContDiffOn ℝ n w S)
    (hf : ContDiffOn ℝ n f S) {Mw Mf : ℝ}
    (hwb : ∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ j w S x‖ ≤ Mw)
    (hfb : ∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ j f S x‖ ≤ Mf) {x : D} (hx : x ∈ S) :
    ‖iteratedFDerivWithin ℝ n (fun y ↦ B (w y) (f y)) S x‖ ≤ ‖B‖ * (2 ^ n * (Mw * Mf)) := by
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear hw hf hu hx le_rfl).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hwb 0 (Nat.zero_le _) x hx)
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i w S x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) f S x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Mw * Mf) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hwb i hi' x hx)
          (hfb (n - i) (Nat.sub_le _ _) x hx) (norm_nonneg _) hMw) (Nat.cast_nonneg _)
    _ = 2 ^ n * (Mw * Mf) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

/-- **Hölder bound of the top derivative of a bilinear product**: for `w` of class `C^{n+1}`
with derivatives at most `Mw` and `f` of class `C^n` with derivatives at most `Mf` and `Dⁿf`
`α`-Hölder with constant `Mf`, on a convex set with unique differentiability, `Dⁿ B(w, f)` is
`α`-Hölder with constant `6 ‖B‖ 2ⁿ Mw Mf`. -/
theorem norm_iteratedFDerivWithin_bilinear_sub_le_rpow (B : E' →L[ℝ] F' →L[ℝ] G') {w : D → E'}
    {f : D → F'} {n : ℕ} {S : Set D} (hS : Convex ℝ S) (hu : UniqueDiffOn ℝ S)
    (hw : ContDiffOn ℝ (n + 1) w S) (hf : ContDiffOn ℝ n f S) {Mw Mf α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hwb : ∀ j ≤ n + 1, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ j w S x‖ ≤ Mw)
    (hfb : ∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ j f S x‖ ≤ Mf)
    (hfh : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDerivWithin ℝ n f S x - iteratedFDerivWithin ℝ n f S y‖ ≤ Mf * ‖x - y‖ ^ α)
    {x y : D} (hx : x ∈ S) (hy : y ∈ S) :
    ‖iteratedFDerivWithin ℝ n (fun z ↦ B (w z) (f z)) S x -
        iteratedFDerivWithin ℝ n (fun z ↦ B (w z) (f z)) S y‖ ≤
      ‖B‖ * (2 ^ n * (6 * (Mw * Mf))) * ‖x - y‖ ^ α := by
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hwb 0 (Nat.zero_le _) x hx)
  have hMf : 0 ≤ Mf := (norm_nonneg _).trans (hfb 0 (Nat.zero_le _) x hx)
  set t := ‖x - y‖ ^ α
  have ht : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) _
  have hwd : ∀ i ≤ n,
      ‖iteratedFDerivWithin ℝ i w S x - iteratedFDerivWithin ℝ i w S y‖ ≤ 3 * Mw * t :=
    fun i hi ↦ norm_iteratedFDerivWithin_sub_le_rpow_of_convex hS hu hw
      (by exact_mod_cast Nat.lt_succ_of_le hi) hα hα1 (fun z hz ↦ hwb i (by omega) z hz)
      (fun z hz ↦ hwb (i + 1) (by omega) z hz) hx hy
  have hfd : ∀ i ≤ n, ‖iteratedFDerivWithin ℝ (n - i) f S x -
      iteratedFDerivWithin ℝ (n - i) f S y‖ ≤ 3 * Mf * t := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Nat.sub_zero]
      nlinarith [hfh x hx y hy]
    · exact norm_iteratedFDerivWithin_sub_le_rpow_of_convex hS hu hf
        (by exact_mod_cast (by omega : n - i < n)) hα hα1 (fun z hz ↦ hfb (n - i) (by omega) z hz)
        (fun z hz ↦ hfb (n - i + 1) (by omega) z hz) hx hy
  refine (norm_iteratedFDerivWithin_bilinear_sub_le B (hw.of_le le_self_add) hf hu hx hy).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (6 * (Mw * Mf) * t) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have h1 := mul_le_mul (hwd i hi') (hfb (n - i) (Nat.sub_le _ _) x hx) (norm_nonneg _)
          (by positivity)
        have h2 := mul_le_mul (hwb i (by omega) y hy) (hfd i hi') (norm_nonneg _) hMw
        nlinarith
    _ = 2 ^ n * (6 * (Mw * Mf)) * t := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]
        ring

end Derivatives

end PDE.Analysis
