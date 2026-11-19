/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators

/-!
# The family of dilations of a function

For `l ∈ ℝ` and `f : ℝ^n → E`, the dilation `x ↦ f(l x)` has the coordinate derivatives
`l ∂ᵢf(l x)` and the coordinate Laplacian `l² Δf(l x)`, with no regularity assumption on `f`: for
`l ≠ 0` the map `x ↦ l x` is a linear equivalence, which transports differentiability both ways,
and for `l = 0` the dilation is constant. For `f` of class `Cᵏ` and `j ≤ k`, the `j`-th
derivatives of the dilations converge to that of `f` uniformly on every ball as `l → 1`: the
derivative of order `j` of `f` is uniformly continuous on compact sets, and `l x → x` uniformly
on balls.

## Main results

* `partialDeriv_comp_smul`: `∂ᵢ(f(l ·))(x) = l ∂ᵢf(l x)`.
* `laplacian_comp_smul`: `Δ(f(l ·))(x) = l² Δf(l x)`.
* `eventually_norm_iteratedFDeriv_comp_smul_sub_le`: for `f` of class `Cᵏ` and `j ≤ k`, the
  `j`-th derivative of `x ↦ f(l x)` is within `ε` of that of `f` on a closed ball for `l` near
  `1`.
-/

@[expose] public section

noncomputable section

open Filter Metric
open scoped Topology

set_option linter.missingDocs true

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- A coordinate derivative of the dilation `y ↦ f(l y)` is `l ∂ᵢf(l x)`, for every `f`. -/
theorem partialDeriv_comp_smul (i : Fin n) (f : ℝ^n → E) (l : ℝ) (x : ℝ^n) :
    (∂[i] (fun y ↦ f (l • y))) x = l • (∂[i] f) (l • x) := by
  simp only [PDE.partialDeriv]
  rw [show (fun y ↦ f (l • y)) = (f <| l • ·) from rfl, fderiv_comp_smul]
  rfl

/-- The coordinate derivatives of the dilation `y ↦ f(l y)` are the dilations of
`l ∂ᵢf`. -/
theorem partialDeriv_comp_smul_eq (i : Fin n) (f : ℝ^n → E) (l : ℝ) :
    (∂[i] (fun y ↦ f (l • y))) = fun x ↦ l • (∂[i] f) (l • x) :=
  funext (partialDeriv_comp_smul i f l)

/-- The coordinate Laplacian of the dilation `y ↦ f(l y)` is `l² Δf(l x)`, for every `f`. -/
theorem laplacian_comp_smul (f : ℝ^n → E) (l : ℝ) (x : ℝ^n) :
    PDE.laplacian (fun y ↦ f (l • y)) x = l ^ 2 • PDE.laplacian f (l • x) := by
  unfold PDE.laplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [partialDeriv_comp_smul_eq i f l]
  change (∂[i] (fun y ↦ l • (fun z ↦ (∂[i] f) z) (l • y))) x = _
  have hs : (fun y ↦ l • (fun z ↦ (∂[i] f) z) (l • y)) =
      fun y ↦ (fun z ↦ l • (∂[i] f) z) (l • y) := rfl
  rw [hs, partialDeriv_comp_smul i (fun z ↦ l • (∂[i] f) z) l x]
  simp only [PDE.partialDeriv]
  rw [show (fun z ↦ l • fderiv ℝ f z (EuclideanSpace.single i 1)) =
      l • fun z ↦ fderiv ℝ f z (EuclideanSpace.single i 1) from rfl, fderiv_const_smul_field]
  simp [smul_smul, pow_two]

/-- **Dilations converge to the function in `Cᵏ` on balls.** For `f` of class `Cᵏ`, `j ≤ k`, a
radius `ρ` and `ε > 0`, the `j`-th derivative of `x ↦ f(l x)` is within `ε` of that of `f` on the
closed ball of radius `ρ` for all `l` near `1`. -/
theorem eventually_norm_iteratedFDeriv_comp_smul_sub_le {k : ℕ} {f : ℝ^n → E}
    (hf : ContDiff ℝ k f) {j : ℕ} (hj : j ≤ k) (ρ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ l in 𝓝 (1 : ℝ), ∀ x ∈ closedBall (0 : ℝ^n) ρ,
      ‖iteratedFDeriv ℝ j (fun y ↦ f (l • y)) x - iteratedFDeriv ℝ j f x‖ ≤ ε := by
  have hfj : ContDiff ℝ j f := hf.of_le (by exact_mod_cast hj)
  have hD : Continuous (iteratedFDeriv ℝ j f) := hfj.continuous_iteratedFDeriv le_rfl
  set r := |ρ| with hr
  set K := closedBall (0 : ℝ^n) (2 * r) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hD.continuousOn
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hD.continuousOn) (ε / 2) (by positivity)
  have hr0 : 0 ≤ r := abs_nonneg ρ
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have h1 : ∀ᶠ l in 𝓝 (1 : ℝ), |l - 1| < min (1 / 2) (δ / (r + 1)) := by
    have : Tendsto (fun l : ℝ ↦ |l - 1|) (𝓝 1) (𝓝 0) := by
      have hc : Continuous fun l : ℝ ↦ |l - 1| := by fun_prop
      simpa using hc.tendsto (1 : ℝ)
    exact this.eventually (gt_mem_nhds (by positivity))
  have h2 : ∀ᶠ l in 𝓝 (1 : ℝ), |l ^ j - 1| * (|M| + 1) < ε / 2 := by
    have : Tendsto (fun l : ℝ ↦ |l ^ j - 1| * (|M| + 1)) (𝓝 1) (𝓝 0) := by
      have hc : Continuous fun l : ℝ ↦ |l ^ j - 1| * (|M| + 1) := by fun_prop
      simpa using hc.tendsto (1 : ℝ)
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h1, h2] with l hl1 hl2 x hx
  have hl : |l - 1| < 1 / 2 := hl1.trans_le (min_le_left _ _)
  have hlδ : |l - 1| < δ / (r + 1) := hl1.trans_le (min_le_right _ _)
  have hxr : ‖x‖ ≤ r := by
    rw [mem_closedBall, dist_zero_right] at hx
    exact hx.trans (le_abs_self ρ)
  have habs : |l| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub l 1
    rw [abs_one] at this
    linarith
  have hxK : x ∈ K := by
    rw [hK, mem_closedBall, dist_zero_right]
    linarith
  have hlxK : l • x ∈ K := by
    rw [hK, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg l, norm_nonneg x]
  have hdist : dist (l • x) x < δ := by
    rw [dist_eq_norm, show l • x - x = (l - 1) • x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs]
    have hpos : 0 < r + 1 := by linarith
    calc |l - 1| * ‖x‖ ≤ |l - 1| * (r + 1) := by gcongr; linarith
      _ < δ / (r + 1) * (r + 1) := by gcongr
      _ = δ := by field_simp
  have hclose : ‖iteratedFDeriv ℝ j f (l • x) - iteratedFDeriv ℝ j f x‖ ≤ ε / 2 := by
    have := hu _ hlxK _ hxK hdist
    rw [dist_eq_norm] at this
    exact this.le
  have hbound : ‖iteratedFDeriv ℝ j f (l • x)‖ ≤ |M| + 1 :=
    (hM _ hlxK).trans ((le_abs_self M).trans (by linarith))
  rw [iteratedFDeriv_comp_const_smul l hfj]
  calc ‖l ^ j • iteratedFDeriv ℝ j f (l • x) - iteratedFDeriv ℝ j f x‖
      = ‖(l ^ j - 1) • iteratedFDeriv ℝ j f (l • x) +
          (iteratedFDeriv ℝ j f (l • x) - iteratedFDeriv ℝ j f x)‖ := by
        congr 1
        rw [sub_smul, one_smul]
        abel
    _ ≤ |l ^ j - 1| * ‖iteratedFDeriv ℝ j f (l • x)‖ +
          ‖iteratedFDeriv ℝ j f (l • x) - iteratedFDeriv ℝ j f x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |l ^ j - 1| * (|M| + 1) + ε / 2 := by gcongr
    _ ≤ ε := by linarith

end PDE
