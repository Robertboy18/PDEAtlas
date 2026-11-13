/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import PDE.Analysis.Calculus.HalfSpaceGluingWithin

/-!
# Limits of functions whose derivatives converge uniformly on a convex set

On a convex set `S`, let `gₙ` have derivatives `Gₙ` within `S`, let `gₙ → g` pointwise on `S` and
`Gₙ → G` uniformly on `S`, with `G` continuous on `S`. Then `G` is the derivative of `g` within
`S`: by the mean value inequality on the convex set `S ∩ B(x, δ)`,
`‖gₙ y - gₙ x - G x (y - x)‖ ≤ (sup_{S} ‖Gₙ - G‖ + c) ‖y - x‖` when `G` varies by at most `c` on
`S ∩ B(x, δ)`, and this bound passes to the limit. If the `Gₙ` are continuous on `S`, so is `G`,
and `g` is `C¹` within `S`.

Two facts about sequences in the `ε`-form are used with these limits.

## Main results

* `hasFDerivWithinAt_of_tendstoUniformlyOn_of_convex`: `G` is the derivative of `g` within `S`.
* `contDiffOn_one_of_tendstoUniformlyOn_of_convex`: with continuous `Gₙ`, `g` is `C¹` within `S`.
* `tendsto_limUnder_of_forall_norm_sub_le`: a sequence in a complete space with
  `‖vₙ - vₘ‖ ≤ ε` for `n, m ≥ n₀(ε)` converges to `limUnder atTop v`.
* `forall_abs_sub_le_of_tendstoUniformlyOn`: two sequences of real functions converging uniformly
  on a set to the same limit are uniformly close there.
-/

@[expose] public section

noncomputable section

open Set Filter Metric Asymptotics
open scoped Topology

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The derivative of a limit is the uniform limit of the derivatives** within a convex set. -/
theorem hasFDerivWithinAt_of_tendstoUniformlyOn_of_convex {S : Set E} (hS : Convex ℝ S)
    {g : ℕ → E → F} {G : ℕ → E → E →L[ℝ] F} {g₀ : E → F} {G₀ : E → E →L[ℝ] F}
    (hd : ∀ n, ∀ x ∈ S, HasFDerivWithinAt (g n) (G n x) S x)
    (hg : ∀ x ∈ S, Tendsto (fun n ↦ g n x) atTop (𝓝 (g₀ x)))
    (hG : TendstoUniformlyOn G G₀ atTop S) (hcont : ContinuousOn G₀ S) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt g₀ (G₀ x) S x := by
  refine HasFDerivWithinAt.of_isLittleO (isLittleO_iff.2 fun c hc ↦ ?_)
  have hcx := hcont x hx
  rw [Metric.continuousWithinAt_iff] at hcx
  obtain ⟨δ, hδ, hδx⟩ := hcx (c / 2) (half_pos hc)
  have hball : ∀ᶠ y in 𝓝[S] x, y ∈ S ∩ ball x δ :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ))
  filter_upwards [hball] with y hy
  have hev := Metric.tendstoUniformlyOn_iff.1 hG (c / 2) (half_pos hc)
  have hs : Convex ℝ (S ∩ ball x δ) := hS.inter (convex_ball x δ)
  have hbound : ∀ᶠ n in atTop, ‖g n y - g n x - G₀ x (y - x)‖ ≤ c * ‖y - x‖ := by
    filter_upwards [hev] with n hn
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := g n) (f' := G n)
      (φ := G₀ x) (C := c) (fun z hz ↦ (hd n z hz.1).mono inter_subset_left)
      (fun z hz ↦ ?_) hs ⟨hx, mem_ball_self hδ⟩ hy
    calc ‖G n z - G₀ x‖ ≤ ‖G n z - G₀ z‖ + ‖G₀ z - G₀ x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ c / 2 + c / 2 := by
          gcongr
          · have := hn z hz.1
            rw [dist_eq_norm, norm_sub_rev] at this
            exact this.le
          · have := hδx hz.1 (mem_ball.1 hz.2)
            rw [dist_eq_norm] at this
            exact this.le
      _ = c := by ring
  have hlim : Tendsto (fun n ↦ g n y - g n x - G₀ x (y - x)) atTop
      (𝓝 (g₀ y - g₀ x - G₀ x (y - x))) :=
    ((hg y hy.1).sub (hg x hx)).sub tendsto_const_nhds
  exact le_of_tendsto hlim.norm hbound

/-- **A limit with uniformly converging continuous derivatives is `C¹`** within a convex set. The
derivative within `S` of the limit is the limit of the derivatives. -/
theorem contDiffOn_one_of_tendstoUniformlyOn_of_convex {S : Set E} (hS : Convex ℝ S)
    {g : ℕ → E → F} {G : ℕ → E → E →L[ℝ] F} {g₀ : E → F} {G₀ : E → E →L[ℝ] F}
    (hd : ∀ n, ∀ x ∈ S, HasFDerivWithinAt (g n) (G n x) S x)
    (hGc : ∀ n, ContinuousOn (G n) S)
    (hg : ∀ x ∈ S, Tendsto (fun n ↦ g n x) atTop (𝓝 (g₀ x)))
    (hG : TendstoUniformlyOn G G₀ atTop S) :
    ContDiffOn ℝ 1 g₀ S ∧ ∀ x ∈ S, HasFDerivWithinAt g₀ (G₀ x) S x := by
  have hc : ContinuousOn G₀ S := hG.continuousOn (Eventually.of_forall hGc).frequently
  have h : ∀ x ∈ S, HasFDerivWithinAt g₀ (G₀ x) S x := fun x hx ↦
    hasFDerivWithinAt_of_tendstoUniformlyOn_of_convex hS hd hg hG hc hx
  exact ⟨contDiffOn_one_of_hasFDerivWithinAt h hc, h⟩

/-! ### Sequences in the `ε`-form -/

/-- A sequence in a complete space that is Cauchy in the `ε`-form converges to its limit. -/
theorem tendsto_limUnder_of_forall_norm_sub_le {G : Type*} [NormedAddCommGroup G]
    [CompleteSpace G] {v : ℕ → G}
    (h : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ‖v n - v m‖ ≤ ε) :
    Tendsto v atTop (𝓝 (limUnder atTop v)) := by
  refine tendsto_nhds_limUnder
    (cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε ↦ ?_))
  obtain ⟨n₀, hn₀⟩ := h (ε / 2) (half_pos hε)
  exact ⟨n₀, fun m hm n hn ↦ by rw [dist_eq_norm]; linarith [hn₀ m hm n hn]⟩

/-- Two sequences of real functions converging uniformly on a set to the same limit are uniformly
close there. -/
theorem forall_abs_sub_le_of_tendstoUniformlyOn {X : Type*} {s : Set X} {F G : ℕ → X → ℝ}
    {g : X → ℝ} (hF : TendstoUniformlyOn F g atTop s) (hG : TendstoUniformlyOn G g atTop s) :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ y ∈ s, |F n y - G m y| ≤ ε := by
  intro ε hε
  obtain ⟨n₁, h₁⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hF (ε / 2) (half_pos hε))
  obtain ⟨n₂, h₂⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hG (ε / 2) (half_pos hε))
  refine ⟨max n₁ n₂, fun n hn m hm y hy ↦ ?_⟩
  have a := h₁ n (le_of_max_le_left hn) y hy
  have b := h₂ m (le_of_max_le_right hm) y hy
  rw [Real.dist_eq, abs_sub_comm] at a
  rw [Real.dist_eq] at b
  have := abs_sub_le (F n y) (g y) (G m y)
  linarith

end PDE.Analysis
