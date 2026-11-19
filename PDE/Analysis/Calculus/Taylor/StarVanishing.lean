/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Vanishing order at a vertex from derivative bounds

Let `V` be an open set that is star-shaped from a point `p` of its closure in the weak sense that
the half-open segment `(p, x]` lies in `V` for every `x ∈ V`, as for the open upper half-plane and
the origin. Then

* a function differentiable on `V`, with limit `0` at `p` from `V` and `‖Df(y)‖ ≤ C ‖y - p‖ᵐ` on
  `V`, satisfies `‖f(x)‖ ≤ C ‖x - p‖ᵐ⁺¹` on `V` (mean value inequality on `[p + t (x - p), x]` and
  `t → 0⁺`);
* a function `K`-Lipschitz on `V` with limit `0` at `p` satisfies `‖g(y)‖ ≤ K ‖y - p‖` on `V`.

Together they give Taylor-type vanishing estimates at a boundary point from bounds and limits of
derivatives on the open side only, without differentiability at `p`.

## Main results

* `norm_le_mul_pow_succ_of_norm_fderiv_le`
* `LipschitzOnWith.norm_le_mul_norm_sub`
-/

@[expose] public section

open Filter Set
open scoped Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace PDE

/-- **Vanishing order from a derivative bound.** If `V` is open, the half-open segments `(p, x]`
lie in `V` for `x ∈ V`, `f` is differentiable on `V` with limit `0` at `p` from `V`, and
`‖Df(y)‖ ≤ C ‖y - p‖ᵐ` on `V` with `C ≥ 0`, then `‖f(x)‖ ≤ C ‖x - p‖ᵐ⁺¹` on `V`. -/
theorem norm_le_mul_pow_succ_of_norm_fderiv_le {f : E → F} {V : Set E} {p : E} {C : ℝ} {m : ℕ}
    (hV : IsOpen V) (hstar : ∀ x ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1, p + t • (x - p) ∈ V)
    (hf : DifferentiableOn ℝ f V) (h0 : Tendsto f (𝓝[V] p) (𝓝 0)) (hC : 0 ≤ C)
    (hd : ∀ y ∈ V, ‖fderiv ℝ f y‖ ≤ C * ‖y - p‖ ^ m) {x : E} (hx : x ∈ V) :
    ‖f x‖ ≤ C * ‖x - p‖ ^ (m + 1) := by
  set γ : ℝ → E := fun t ↦ p + t • (x - p)
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝[V] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto γ (𝓝 0) (𝓝 (γ 0)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      simpa [γ] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      exact hstar x hx t ⟨ht.1, ht.2.le⟩
  have hlim : Tendsto (fun t ↦ ‖f x - f (γ t)‖) (𝓝[>] 0) (𝓝 ‖f x - 0‖) :=
    ((h0.comp hγ).const_sub (f x)).norm
  rw [sub_zero] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with δ hδ
  have hsV : ∀ z ∈ segment ℝ (γ δ) x, z ∈ V ∧ ‖z - p‖ ≤ ‖x - p‖ := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have e : γ δ + θ • (x - γ δ) = p + (δ + θ * (1 - δ)) • (x - p) := by
      simp only [γ]
      module
    dsimp only
    rw [e]
    have ht0 : 0 < δ + θ * (1 - δ) := by nlinarith [hδ.1, hδ.2]
    have ht1 : δ + θ * (1 - δ) ≤ 1 := by nlinarith [hδ.1, hδ.2]
    refine ⟨hstar x hx _ ⟨ht0, ht1⟩, ?_⟩
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    exact mul_le_of_le_one_left (norm_nonneg _) ht1
  have hmv := (convex_segment (γ δ) x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := f) (f' := fderiv ℝ f) (C := C * ‖x - p‖ ^ m)
    (fun z hz ↦ ((hf z (hsV z hz).1).differentiableAt (hV.mem_nhds (hsV z hz).1)).hasFDerivAt
      |>.hasFDerivWithinAt)
    (fun z hz ↦ (hd z (hsV z hz).1).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hsV z hz).2 m) hC))
    (left_mem_segment ℝ (γ δ) x) (right_mem_segment ℝ (γ δ) x)
  have hdist : ‖x - γ δ‖ ≤ ‖x - p‖ := by
    have e : x - γ δ = (1 - δ) • (x - p) := by
      simp only [γ]
      module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hδ.2])]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hδ.1])
  calc ‖f x - f (γ δ)‖ ≤ C * ‖x - p‖ ^ m * ‖x - γ δ‖ := hmv
    _ ≤ C * ‖x - p‖ ^ m * ‖x - p‖ := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = C * ‖x - p‖ ^ (m + 1) := by ring

end PDE

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A function that is `K`-Lipschitz on `V` and tends to `0` at `p` from `V` is bounded by
`K ‖y - p‖` on `V`. -/
theorem LipschitzOnWith.norm_le_mul_norm_sub {g : E → F} {V : Set E} {p : E} {K : ℝ≥0}
    (hg : LipschitzOnWith K g V) (hp : (𝓝[V] p).NeBot) (h0 : Tendsto g (𝓝[V] p) (𝓝 0))
    {y : E} (hy : y ∈ V) : ‖g y‖ ≤ K * ‖y - p‖ := by
  have h1 : Tendsto (fun z ↦ ‖g y - g z‖) (𝓝[V] p) (𝓝 ‖g y - 0‖) := (h0.const_sub (g y)).norm
  have h2 : Tendsto (fun z ↦ (K : ℝ) * ‖y - z‖) (𝓝[V] p) (𝓝 (K * ‖y - p‖)) :=
    ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_sub y).norm.const_mul _
  rw [sub_zero] at h1
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact hg.dist_le_mul y hy z hz
