/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.WithinOperators
import Mathlib.Analysis.Calculus.MeanValue
import PDE.FDeriv.PartialDeriv.Energy

/-!
# Raising the order of vanishing within a convex set

On a convex set with unique derivatives in `ℝⁿ`, a function differentiable within the set that
vanishes at a point `p`, and whose partial derivatives within the set are `O(‖x - p‖ᵏ)` there, is
`O(‖x - p‖ᵏ⁺¹)`. Together with `PDE.isBigO_sq_of_contDiffOn` this gives Taylor-type vanishing of
every order from the vanishing of the jets within the set, for functions given only on the set
(such as fields on a closed half-plane).

## Main results

* `isBigO_pow_succ_of_partialDerivWithin`: vanishing at `p` and partial derivatives within `s`
  that are `O(‖x - p‖ᵏ)` make `f` itself `O(‖x - p‖ᵏ⁺¹)` within `s` at `p`.
-/

@[expose] public section

noncomputable section

open Filter Set Asymptotics
open scoped Topology

namespace PDE

variable {n : ℕ} {f : ℝ^n → ℝ} {s : Set (ℝ^n)} {p : ℝ^n}

/-- **Raising the order of vanishing within a convex set**: if `f` is differentiable within the
convex set `s`, vanishes at `p ∈ s`, and its partial derivatives within `s` are `O(‖x - p‖ᵏ)`
within `s` at `p`, then `f = O(‖x - p‖ᵏ⁺¹)` within `s` at `p`. -/
theorem isBigO_pow_succ_of_partialDerivWithin (hs : Convex ℝ s) (hp : p ∈ s)
    (hf : DifferentiableOn ℝ f s) (hf0 : f p = 0) {k : ℕ}
    (hd : ∀ i : Fin n, (fun x ↦ partialDerivWithin i f s x) =O[𝓝[s] p] fun x ↦ ‖x - p‖ ^ k) :
    f =O[𝓝[s] p] fun x ↦ ‖x - p‖ ^ (k + 1) := by
  choose C hC using fun i ↦ (hd i).bound
  have hall : ∀ᶠ y in 𝓝[s] p, ∀ i : Fin n,
      ‖partialDerivWithin i f s y‖ ≤ C i * ‖‖y - p‖ ^ k‖ :=
    eventually_all.2 hC
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hall
  set K := ∑ i : Fin n, |C i|
  set t₀ := Metric.ball p δ ∩ s
  have ht₀ : Convex ℝ t₀ := (convex_ball p δ).inter hs
  have hpt₀ : p ∈ t₀ := ⟨Metric.mem_ball_self hδ, hp⟩
  have hderiv : ∀ y ∈ t₀, ‖fderivWithin ℝ f s y‖ ≤ K * ‖y - p‖ ^ k := fun y hy ↦ by
    have hb := hδs hy
    refine (ContinuousLinearMap.norm_le_sum_norm_apply_single _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have := hb i
    rw [norm_pow, norm_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  refine IsBigO.of_bound K ?_
  filter_upwards [inter_mem_nhdsWithin s (Metric.ball_mem_nhds p hδ), self_mem_nhdsWithin]
    with x hx hxs
  have hxt : x ∈ t₀ := ⟨hx.2, hxs⟩
  set r := ‖x - p‖
  set t' := t₀ ∩ Metric.closedBall p r
  have ht' : Convex ℝ t' := ht₀.inter (convex_closedBall p r)
  have h := ht'.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := f)
    (f' := fderivWithin ℝ f s) (C := K * r ^ k)
    (fun z hz ↦ ((hf z hz.1.2).hasFDerivWithinAt).mono
      (inter_subset_left.trans inter_subset_right))
    (fun z hz ↦ (hderiv z hz.1).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hz.2) k)
      (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)))
    ⟨hpt₀, Metric.mem_closedBall_self (norm_nonneg _)⟩ ⟨hxt, by simp [r, dist_eq_norm]⟩
  rw [hf0, sub_zero] at h
  rw [norm_pow, norm_norm]
  calc ‖f x‖ ≤ K * r ^ k * r := h
    _ = K * r ^ (k + 1) := by ring

end PDE
