/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A smooth cutoff for the difference of weak solutions

The complement of a Mathlib bump is a nonnegative Lipschitz cutoff `χ`. It vanishes on
`[-a, a]` and equals one outside `(-2a, 2a)`. Composed with the difference of two weak
solutions it plays the role of the function `φ` in step 7 of the proof of Theorem 7 in Evans,
§3.3.3(b). Evans asks `φ` to be positive off the interval where it vanishes; we only use that
every zero of `χ` lies in `(-2a, 2a)`. The resulting bound `|u - v| < 2a` still tends to zero
with `a`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, step 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open Metric
open scoped ContDiff

/-- A smooth Lipschitz cutoff vanishes on `[-a,a]`; every zero lies in
`(-2a,2a)`. Both properties follow from the bump function. -/
theorem exists_smooth_difference_cutoff {a : ℝ} (ha : 0 < a) :
    ∃ (χ : ℝ → ℝ) (K : NNReal), ContDiff ℝ ∞ χ ∧ LipschitzWith K χ ∧ (∀ s, 0 ≤ χ s) ∧
      (∀ s, |s| ≤ a → χ s = 0) ∧ (∀ s, χ s = 0 → |s| < 2 * a) := by
  let ψ : ContDiffBump (0 : ℝ) :=
    { rIn := a
      rOut := 2 * a
      rIn_pos := ha
      rIn_lt_rOut := by linarith }
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ψ.hasCompactSupport
    (show ContDiff ℝ 1 ψ from ψ.contDiff) one_ne_zero
  refine ⟨fun s ↦ 1 - ψ s, 0 + K, contDiff_const.sub ψ.contDiff,
    (LipschitzWith.const 1).sub hK, fun s ↦ sub_nonneg.mpr ψ.le_one, ?_, ?_⟩
  · intro s hs
    change 1 - ψ s = 0
    have hψ : ψ s = 1 :=
      ψ.one_of_mem_closedBall (by simpa only [mem_closedBall, Real.dist_eq, sub_zero, ψ] using hs)
    rw [hψ, sub_self]
  · intro s hs
    change 1 - ψ s = 0 at hs
    by_contra h
    have hψ : ψ s = 0 :=
      ψ.zero_of_le_dist (by simpa only [Real.dist_eq, sub_zero, ψ] using le_of_not_gt h)
    rw [hψ, sub_zero] at hs
    exact one_ne_zero hs

end HamiltonJacobi.Weak
