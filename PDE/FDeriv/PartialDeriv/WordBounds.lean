/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNorm

/-!
# Derivative bounds from bounds on the coordinate words

If every coordinate derivative word of length `k` of a function on `ℝ^n` has norm at most `η`
at a point, the coordinate norm sum of order `k` there is at most `n^k η`, and so is the norm of
the `k`-th Fréchet derivative when the function is `C^k` at the point. Consequently the `k`-th
Fréchet derivative tends to zero along a filter on an open set where the function is `C^k` as
soon as every word of length `k` does.

## Main results

* `iteratedCoordinateNormSum_le`: bounds `η` on the words of length `k` bound the coordinate norm
  sum of order `k` by `n^k η`.
* `norm_iteratedFDeriv_le_of_forall_word`: `‖Dᵏf(x)‖ ≤ n^k η` when `f` is `C^k` at `x`.
* `tendsto_iteratedFDeriv_of_forall_word`: `Dᵏf` tends to zero along `l` when every coordinate
  word of length `k` does.
-/

@[expose] public noncomputable section

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- Bounds on the words of length `k` bound the coordinate norm sum of order `k`. -/
theorem iteratedCoordinateNormSum_le (k : ℕ) {f : ℝ^n → F} {x : ℝ^n} {η : ℝ}
    (h : ∀ w : List (Fin n), w.length = k → ‖iteratedPartialDeriv w f x‖ ≤ η) :
    iteratedCoordinateNormSum k f x ≤ (n : ℝ) ^ k * η := by
  induction k generalizing f with
  | zero => simpa [iteratedCoordinateNormSum, iteratedPartialDeriv] using h [] rfl
  | succ k ih =>
    simp only [iteratedCoordinateNormSum]
    calc ∑ i : Fin n, iteratedCoordinateNormSum k (∂[i] f) x ≤ ∑ _i : Fin n, (n : ℝ) ^ k * η :=
          Finset.sum_le_sum fun i _ ↦ ih fun w hw ↦ by
            have := h (w ++ [i]) (by simp [hw])
            rwa [iteratedPartialDeriv_append_single] at this
      _ = (n : ℝ) ^ (k + 1) * η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
          ring

/-- **Derivative bounds from word bounds.** If `f` is `C^k` at `x` and every coordinate word of
length `k` has norm at most `η` at `x`, then `‖Dᵏf(x)‖ ≤ n^k η`. -/
theorem norm_iteratedFDeriv_le_of_forall_word (k : ℕ) {f : ℝ^n → F} {x : ℝ^n}
    (hf : ContDiffAt ℝ k f x) {η : ℝ}
    (h : ∀ w : List (Fin n), w.length = k → ‖iteratedPartialDeriv w f x‖ ≤ η) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ (n : ℝ) ^ k * η :=
  (norm_iteratedFDeriv_le_iteratedCoordinateNormSum k hf).trans (iteratedCoordinateNormSum_le k h)

open Filter in
open scoped Topology in
/-- **Fréchet derivatives tend to zero with their words.** If `f` is `C^k` on an open set `U`,
the filter `l` lives on `U`, and every coordinate word of length `k` of `f` tends to zero along
`l`, then so does the `k`-th Fréchet derivative. -/
theorem tendsto_iteratedFDeriv_of_forall_word (k : ℕ) {f : ℝ^n → F} {U : Set (ℝ^n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ k f U) {l : Filter (ℝ^n)} (hl : ∀ᶠ x in l, x ∈ U)
    (hw : ∀ w : List (Fin n), w.length = k → Tendsto (iteratedPartialDeriv w f) l (𝓝 0)) :
    Tendsto (iteratedFDeriv ℝ k f) l (𝓝 0) := by
  set η : ℝ^n → ℝ := fun x ↦ ∑ v : Fin k → Fin n, ‖iteratedPartialDeriv (List.ofFn v) f x‖
  have hη : Tendsto η l (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin n)) fun v _ ↦
      (hw (List.ofFn v) (by simp)).norm
    simpa [η] using this
  refine squeeze_zero_norm' ?_ (by simpa using hη.const_mul ((n : ℝ) ^ k))
  filter_upwards [hl] with x hx
  refine norm_iteratedFDeriv_le_of_forall_word k (hf.contDiffAt (hU.mem_nhds hx)) fun w hw ↦ ?_
  subst hw
  have h := Finset.single_le_sum (f := fun v : Fin w.length → Fin n ↦
    ‖iteratedPartialDeriv (List.ofFn v) f x‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ w.get)
  simpa [List.ofFn_get] using h

end PDE
