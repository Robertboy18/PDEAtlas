/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Taylor.StarVanishing
public import PDE.FDeriv.PartialDeriv.Energy
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Vanishing orders on the upper half disc

Two mean value bounds on the upper half disc `{x₁ > 0, |x| < r}` of the plane, for functions
known only through their partial derivatives there: integration along the ray from the origin,
and integration along the horizontal segment from the vertical axis. The second gives the factor
`x₀` that the weights singular at the axis need.

## Main results

* `abs_le_mul_pow_succ_of_partialDeriv_le`: if `g` tends to `0` at the origin from the open upper
  half-plane and `|∂ₖg(y)| ≤ C |y|ᵐ` for both `k`, then `|g(y)| ≤ 2 C |y|ᵐ⁺¹`.
* `abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le`: if `g` vanishes on the vertical axis and
  `|∂₀g(y)| ≤ A |y₀|ᵃ |y|ᵐ`, then `|g(y)| ≤ A |y₀|ᵃ⁺¹ |y|ᵐ`.
* `abs_le_of_partialDeriv_three_le`: zero jets of order `≤ 2` at the origin and third partial
  derivatives at most `M` give `|∂ₗ∂ₖg| ≤ 2M|y|`, `|∂ₖg| ≤ 4M|y|²`, `|g| ≤ 8M|y|³`.
* `Convex.abs_sub_le_mul_norm_sub_of_partialDeriv_le`: `|g x - g z| ≤ K |x - z|` from
  `|∂₀g| + |∂₁g| ≤ K` on a convex set.
* `abs_sub_le_mul_norm_sub_of_partialDeriv_le`: the same two-point bound on the half disc.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology

namespace PDE.Analysis

/-- **Vanishing order on the upper half disc from the partial derivatives**: if `g` is
differentiable on `{x₁ > 0, |x| < r}`, tends to `0` at the origin from the open upper half-plane,
and `|∂ₖg(y)| ≤ C |y|ᵐ` there for both `k`, then `|g(y)| ≤ 2 C |y|ᵐ⁺¹` there. -/
theorem abs_le_mul_pow_succ_of_partialDeriv_le {g : ℝ^2 → ℝ} {r C : ℝ} {m : ℕ}
    (hg : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → DifferentiableAt ℝ g y)
    (h0 : Tendsto g (𝓝[{z : ℝ^2 | 0 < z 1}] 0) (𝓝 0)) (hC : 0 ≤ C)
    (hd : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ k : Fin 2, |(∂[k] g) y| ≤ C * ‖y‖ ^ m)
    {y : ℝ^2} (hy1 : 0 < y 1) (hyr : ‖y‖ < r) : |g y| ≤ 2 * C * ‖y‖ ^ (m + 1) := by
  set V : Set (ℝ^2) := {z | 0 < z 1} ∩ ball 0 r with hVdef
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous).inter isOpen_ball
  have hmem : ∀ z, z ∈ V ↔ 0 < z 1 ∧ ‖z‖ < r := fun z ↦ by
    simp [hVdef]
  have hstar : ∀ x ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1, (0 : ℝ^2) + t • (x - 0) ∈ V := by
    intro x hx t ht
    rw [hmem] at hx ⊢
    simp only [zero_add, sub_zero, PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht.1]
    exact ⟨mul_pos ht.1 hx.1, (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hx.2⟩
  have hf : DifferentiableOn ℝ g V := fun z hz ↦
    (hg z ((hmem z).1 hz).1 ((hmem z).1 hz).2).differentiableWithinAt
  have hV : V ⊆ {z : ℝ^2 | 0 < z 1} := fun z hz ↦ ((hmem z).1 hz).1
  have h0' : Tendsto g (𝓝[V] 0) (𝓝 0) := h0.mono_left (nhdsWithin_mono _ hV)
  have hd' : ∀ z ∈ V, ‖fderiv ℝ g z‖ ≤ 2 * C * ‖z - 0‖ ^ m := by
    intro z hz
    obtain ⟨hz1, hzr⟩ := (hmem z).1 hz
    refine (norm_fderiv_le_sum_norm_partialDeriv g z).trans ?_
    rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero]
    linarith [hd z hz1 hzr 0, hd z hz1 hzr 1]
  have h := norm_le_mul_pow_succ_of_norm_fderiv_le hVo hstar hf h0' (by positivity) hd'
    ((hmem y).2 ⟨hy1, hyr⟩)
  rwa [Real.norm_eq_abs, sub_zero] at h

/-- **The axis factor on the upper half disc**: if `g` is differentiable on
`{x₁ > 0, |x| < r}`, vanishes on the vertical axis there and `|∂₀g(y)| ≤ A |y₀|ᵃ |y|ᵐ` there,
then `|g(x)| ≤ A |x₀|ᵃ⁺¹ |x|ᵐ` there: `g(x) - g(0, x₁)` is the integral of `x₀ ∂₀g` along the
horizontal segment, whose points `y` have `|y₀| ≤ |x₀|` and `|y| ≤ |x|`. -/
theorem abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le {g : ℝ^2 → ℝ} {r A : ℝ} {a m : ℕ}
    (hA : 0 ≤ A) (hg : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → DifferentiableAt ℝ g y)
    (haxis : ∀ y : ℝ^2, y 0 = 0 → 0 < y 1 → ‖y‖ < r → g y = 0)
    (hd : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[(0 : Fin 2)] g) y| ≤ A * |y 0| ^ a * ‖y‖ ^ m)
    {x : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) : |g x| ≤ A * |x 0| ^ (a + 1) * ‖x‖ ^ m := by
  set e : ℝ^2 := EuclideanSpace.single 0 (1 : ℝ) with hedef
  set x' : ℝ^2 := x - x 0 • e with hx'def
  have hx'0 : x' 0 = 0 := by simp [hx'def, hedef]
  have hx'1 : x' 1 = x 1 := by simp [hx'def, hedef]
  set γ : ℝ → ℝ^2 := fun t ↦ x' + (t * x 0) • e with hγdef
  have hγ0 : γ 0 = x' := by simp [hγdef]
  have hγ1 : γ 1 = x := by simp [hγdef, hx'def]
  have hγc : ∀ t, (γ t) 1 = x 1 := fun t ↦ by simp [hγdef, hx'1, hedef]
  have hγ00 : ∀ t, (γ t) 0 = t * x 0 := fun t ↦ by simp [hγdef, hx'0, hedef]
  have hγn : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ ‖x‖ := by
    intro t ht
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two,
      hγ00, hγc]
    refine Real.sqrt_le_sqrt ?_
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow]
    nlinarith [sq_nonneg (x 0)]
  have hγ0n : ∀ t ∈ Icc (0 : ℝ) 1, |(γ t) 0| ≤ |x 0| := by
    intro t ht
    rw [hγ00, abs_mul, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t ↦ g (γ t))
      (x 0 * (∂[(0 : Fin 2)] g) (γ t)) (Icc 0 1) t := by
    intro t ht
    have hγd : HasDerivAt γ (x 0 • e) t := by
      have : HasDerivAt (fun t : ℝ ↦ (t * x 0) • e) ((1 * x 0) • e) t :=
        ((hasDerivAt_id t).mul_const (x 0)).smul_const e
      simpa [hγdef] using this.const_add x'
    have hgd : DifferentiableAt ℝ g (γ t) :=
      hg (γ t) (by rw [hγc]; exact hx1) ((hγn t ht).trans_lt hxr)
    have h := hgd.hasFDerivAt.comp_hasDerivAt t hγd
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
    rfl
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖x 0 * (∂[(0 : Fin 2)] g) (γ t)‖ ≤ A * |x 0| ^ (a + 1) * ‖x‖ ^ m := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    rw [Real.norm_eq_abs, abs_mul]
    have h := hd (γ t) (by rw [hγc]; exact hx1) ((hγn t htI).trans_lt hxr)
    have hn := pow_le_pow_left₀ (norm_nonneg _) (hγn t htI) m
    have ha := pow_le_pow_left₀ (abs_nonneg _) (hγ0n t htI) a
    calc |x 0| * |(∂[(0 : Fin 2)] g) (γ t)| ≤ |x 0| * (A * |x 0| ^ a * ‖x‖ ^ m) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) (abs_nonneg _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left ha hA) hn (by positivity) (by positivity)
      _ = A * |x 0| ^ (a + 1) * ‖x‖ ^ m := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩
  have hgx' : g (γ 0) = 0 := by
    rw [hγ0]
    have hn0 : ‖x'‖ < r := by
      have := (hγn 0 ⟨le_rfl, zero_le_one⟩).trans_lt hxr
      rwa [hγ0] at this
    exact haxis x' hx'0 (by rw [hx'1]; exact hx1) hn0
  rw [hγ1, hgx', sub_zero, Real.norm_eq_abs, sub_zero, mul_one] at hmv
  exact hmv

/-- **The third-order Taylor bounds on the upper half disc**: if `g` is `C³` on
`{x₁ > 0, |x| < r}`, `g`, its partial derivatives and its second partial derivatives tend to `0` at
the origin from the open upper half-plane, and its third partial derivatives are at most `M`
there, then `|∂ₗ∂ₖg| ≤ 2 M |y|`, `|∂ₖg| ≤ 4 M |y|²` and `|g| ≤ 8 M |y|³` there. -/
theorem abs_le_of_partialDeriv_three_le {g : ℝ^2 → ℝ} {r M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ContDiffAt ℝ 3 g y)
    (h0 : Tendsto g (𝓝[{z : ℝ^2 | 0 < z 1}] 0) (𝓝 0))
    (h1 : ∀ k : Fin 2, Tendsto (∂[k] g) (𝓝[{z : ℝ^2 | 0 < z 1}] 0) (𝓝 0))
    (h2 : ∀ k l : Fin 2, Tendsto (∂[l] (∂[k] g)) (𝓝[{z : ℝ^2 | 0 < z 1}] 0) (𝓝 0))
    (h3 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ j k l : Fin 2,
      |(∂[j] (∂[l] (∂[k] g))) y| ≤ M)
    {y : ℝ^2} (hy1 : 0 < y 1) (hyr : ‖y‖ < r) :
    (∀ k l : Fin 2, |(∂[l] (∂[k] g)) y| ≤ 2 * M * ‖y‖) ∧
      (∀ k : Fin 2, |(∂[k] g) y| ≤ 4 * M * ‖y‖ ^ 2) ∧ |g y| ≤ 8 * M * ‖y‖ ^ 3 := by
  have hd1 : ∀ z : ℝ^2, 0 < z 1 → ‖z‖ < r → ∀ k : Fin 2, DifferentiableAt ℝ (∂[k] g) z :=
    fun z hz1 hz k ↦ ((hg z hz1 hz).partialDeriv k
      (by norm_num : ((2 : ℕ) : WithTop ℕ∞) + 1 ≤ 3)).differentiableAt (by norm_num)
  have hd2 : ∀ z : ℝ^2, 0 < z 1 → ‖z‖ < r → ∀ k l : Fin 2,
      DifferentiableAt ℝ (∂[l] (∂[k] g)) z :=
    fun z hz1 hz k l ↦ (((hg z hz1 hz).partialDeriv k
      (by norm_num : ((2 : ℕ) : WithTop ℕ∞) + 1 ≤ 3)).partialDeriv l
        (by norm_num : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have s2 : ∀ z : ℝ^2, 0 < z 1 → ‖z‖ < r → ∀ k l : Fin 2,
      |(∂[l] (∂[k] g)) z| ≤ 2 * M * ‖z‖ := by
    intro z hz1 hz k l
    have h := abs_le_mul_pow_succ_of_partialDeriv_le (g := ∂[l] (∂[k] g)) (r := r) (m := 0)
      (fun w hw1 hw ↦ hd2 w hw1 hw k l) (h2 k l) hM
      (fun w hw1 hw j ↦ by rw [pow_zero, mul_one]; exact h3 w hw1 hw j k l) hz1 hz
    simpa using h
  have s1 : ∀ z : ℝ^2, 0 < z 1 → ‖z‖ < r → ∀ k : Fin 2, |(∂[k] g) z| ≤ 4 * M * ‖z‖ ^ 2 := by
    intro z hz1 hz k
    have h := abs_le_mul_pow_succ_of_partialDeriv_le (g := ∂[k] g) (r := r) (m := 1)
      (fun w hw1 hw ↦ hd1 w hw1 hw k) (h1 k) (by positivity : (0 : ℝ) ≤ 2 * M)
      (fun w hw1 hw l ↦ by rw [pow_one]; exact s2 w hw1 hw k l) hz1 hz
    calc _ ≤ 2 * (2 * M) * ‖z‖ ^ (1 + 1) := h
      _ = 4 * M * ‖z‖ ^ 2 := by ring
  refine ⟨fun k l ↦ s2 y hy1 hyr k l, fun k ↦ s1 y hy1 hyr k, ?_⟩
  have h := abs_le_mul_pow_succ_of_partialDeriv_le (g := g) (r := r) (m := 2)
    (fun w hw1 hw ↦ (hg w hw1 hw).differentiableAt (by norm_num)) h0
    (by positivity : (0 : ℝ) ≤ 4 * M) (fun w hw1 hw k ↦ s1 w hw1 hw k) hy1 hyr
  calc _ ≤ 2 * (4 * M) * ‖y‖ ^ (2 + 1) := h
    _ = 8 * M * ‖y‖ ^ 3 := by ring

/-- **Two-point bound on a convex set from the partial derivatives**: if `g` is differentiable on a
convex set `s ⊆ ℝ²` and `|∂₀g| + |∂₁g| ≤ K` there, then `|g x - g z| ≤ K |x - z|` for `x`, `z`
in `s`. -/
theorem _root_.Convex.abs_sub_le_mul_norm_sub_of_partialDeriv_le {s : Set (ℝ^2)}
    (hs : Convex ℝ s) {g : ℝ^2 → ℝ} {K : ℝ} (hg : ∀ y ∈ s, DifferentiableAt ℝ g y)
    (hd : ∀ y ∈ s, |(∂[(0 : Fin 2)] g) y| + |(∂[(1 : Fin 2)] g) y| ≤ K)
    {x z : ℝ^2} (hx : x ∈ s) (hz : z ∈ s) : |g x - g z| ≤ K * ‖x - z‖ := by
  have h := hs.norm_image_sub_le_of_norm_fderiv_le (f := g) (C := K) hg
    (fun y hy ↦ by
      refine (norm_fderiv_le_sum_norm_partialDeriv g y).trans ?_
      rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
      exact hd y hy) hz hx
  rwa [Real.norm_eq_abs] at h

/-- **Two-point bound on the upper half disc from the partial derivatives**: if `g` is
differentiable on `{x₁ > 0, |x| < r}` and `|∂₀g| + |∂₁g| ≤ K` there, then
`|g x - g z| ≤ K |x - z|` for `x`, `z` there; the half disc is convex. -/
theorem abs_sub_le_mul_norm_sub_of_partialDeriv_le {g : ℝ^2 → ℝ} {r K : ℝ}
    (hg : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → DifferentiableAt ℝ g y)
    (hd : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r →
      |(∂[(0 : Fin 2)] g) y| + |(∂[(1 : Fin 2)] g) y| ≤ K)
    {x z : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) (hz1 : 0 < z 1) (hzr : ‖z‖ < r) :
    |g x - g z| ≤ K * ‖x - z‖ := by
  set V : Set (ℝ^2) := {y | 0 < y 1} ∩ ball 0 r with hVdef
  have hmem : ∀ y, y ∈ V ↔ 0 < y 1 ∧ ‖y‖ < r := fun y ↦ by simp [hVdef]
  have hVc : Convex ℝ V := by
    have h1 := convex_halfSpace_gt
      (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).isLinear (0 : ℝ)
    have := h1.inter (convex_ball (0 : ℝ^2) r)
    convert this using 1
    ext y; simp [hVdef]
  exact hVc.abs_sub_le_mul_norm_sub_of_partialDeriv_le
    (fun y hy ↦ hg y ((hmem y).1 hy).1 ((hmem y).1 hy).2)
    (fun y hy ↦ hd y ((hmem y).1 hy).1 ((hmem y).1 hy).2)
    ((hmem x).2 ⟨hx1, hxr⟩) ((hmem z).2 ⟨hz1, hzr⟩)

end PDE.Analysis
