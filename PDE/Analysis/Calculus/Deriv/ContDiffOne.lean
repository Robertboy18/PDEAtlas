/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# `Cᵏ` from derivatives

A real function with a derivative `f'` at every point of an open set `U`, `f'` continuous on `U`,
is `C¹` on `U`. A chain `r 0, r 1, …, r n` in which each function has the next as derivative
everywhere and `r n` is `C¹` starts with a `C^{n+1}` function.

## Main results

* `contDiffOn_one_of_hasDerivAt`: a function with a derivative continuous on an open set `U` is
  `C¹` on `U`.
* `contDiff_of_hasDerivAt_chain`: the first function of such a chain is `C^{n+1}`.
-/

@[expose] public section

set_option linter.missingDocs true

namespace PDE

/-- A function with a derivative continuous on an open set is `C¹` there. -/
theorem contDiffOn_one_of_hasDerivAt {f f' : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ∀ x ∈ U, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' U) : ContDiffOn ℝ 1 f U := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun x hx ↦ (hf x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hf'.congr fun x hx ↦ (hf x hx).deriv

/-- A chain of functions each differentiating into the next, ending in a `C¹` function, starts
with a `C^{n+1}` function. -/
theorem contDiff_of_hasDerivAt_chain {n : ℕ} {r : ℕ → ℝ → ℝ}
    (hd : ∀ j < n, ∀ x, HasDerivAt (r j) (r (j + 1) x) x) (hn : ContDiff ℝ 1 (r n)) :
    ContDiff ℝ (n + 1 : ℕ) (r 0) := by
  induction n generalizing r with
  | zero => simpa using hn
  | succ n ih =>
    have h1 := ih (r := fun j ↦ r (j + 1)) (fun j hj x ↦ hd (j + 1) (by omega) x) hn
    have hderiv : deriv (r 0) = r 1 := funext fun x ↦ (hd 0 (by omega) x).deriv
    rw [show ((n + 1 + 1 : ℕ) : WithTop ℕ∞) = ((n + 1 : ℕ) : WithTop ℕ∞) + 1 by push_cast; ring]
    refine contDiff_succ_iff_deriv.mpr ⟨fun x ↦ (hd 0 (by omega) x).differentiableAt,
      by simp, ?_⟩
    rw [hderiv]
    exact h1

end PDE
