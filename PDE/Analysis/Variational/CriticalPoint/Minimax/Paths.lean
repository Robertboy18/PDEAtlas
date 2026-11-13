/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Path

/-!
# Heights and minimax values of continuous paths

The height of a path is the supremum of its real energy values. For a continuous
energy this is an attained finite maximum, because the path parameter is the compact
unit interval. The minimax value is the infimum of these heights over Mathlib's
`Path` type. Its lower bound comes from the common initial endpoint, even when the
energy is unbounded below elsewhere. For paths from `0` to `v`, `pathMinimax I 0 v` is the
value `c = inf_{g ∈ Γ} max_{0 ≤ t ≤ 1} I[g(t)]` of Evans, §8.5.1, Theorem 2, whose set `Γ`
consists of the continuous paths from `0` to `v`.

## Main definitions

* `pathHeight`: the largest energy along a path.
* `pathMinimax`: the infimum of the heights of all paths between two points.

## Main results

* `le_pathHeight`, `exists_eq_pathHeight`: for continuous `I` the height is an attained
  maximum.
* `pathMinimax_le_pathHeight`, `le_pathMinimax`, `exists_pathHeight_lt`: the minimax value is
  at most every height, at least every common lower bound of the heights, and within any
  `ε > 0` of the height of some path.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(b), Theorem 2 (Mountain Pass Theorem), p. 505,
  and the definitions of `Γ` and `c` in it, p. 506. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Variational

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- The largest energy along a path, expressed as a real supremum. -/
def pathHeight (I : X → ℝ) (γ : Path x y) : ℝ :=
  sSup (range (fun t ↦ I (γ t)))

/-- The infimum of the heights of all continuous paths between the two endpoints. -/
def pathMinimax (I : X → ℝ) (x y : X) : ℝ :=
  sInf (range (pathHeight I : Path x y → ℝ))

/-- Every value along a path is bounded by its attained height. -/
theorem le_pathHeight {I : X → ℝ} (hI : Continuous I) (γ : Path x y)
    (t : unitInterval) : I (γ t) ≤ pathHeight I γ :=
  le_csSup (isCompact_range (hI.comp γ.continuous)).bddAbove (mem_range_self t)

/-- A uniform bound along a path bounds its height. -/
theorem pathHeight_le {I : X → ℝ} (γ : Path x y) {b : ℝ}
    (h : ∀ t, I (γ t) ≤ b) : pathHeight I γ ≤ b :=
  csSup_le (range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact h t)

/-- The maximum along each path is attained at some parameter. -/
theorem exists_eq_pathHeight {I : X → ℝ} (hI : Continuous I) (γ : Path x y) :
    ∃ t : unitInterval, I (γ t) = pathHeight I γ :=
  (isCompact_range (hI.comp γ.continuous)).sSup_mem (range_nonempty _)

/-- A common endpoint bounds the heights of all joining paths from below. -/
theorem bddBelow_range_pathHeight {I : X → ℝ} (hI : Continuous I) :
    BddBelow (range (pathHeight I : Path x y → ℝ)) := by
  refine ⟨I x, ?_⟩
  rintro _ ⟨γ, rfl⟩
  simpa only [γ.source] using le_pathHeight hI γ 0

/-- The minimax value is no greater than the height of any admissible path. -/
theorem pathMinimax_le_pathHeight {I : X → ℝ} (hI : Continuous I) (γ : Path x y) :
    pathMinimax I x y ≤ pathHeight I γ :=
  csInf_le (bddBelow_range_pathHeight hI) (mem_range_self γ)

/-- A uniform lower bound for an inhabited path family bounds its minimax value. -/
theorem le_pathMinimax {I : X → ℝ} (hne : Nonempty (Path x y)) {a : ℝ}
    (h : ∀ γ : Path x y, a ≤ pathHeight I γ) : a ≤ pathMinimax I x y := by
  obtain ⟨γ⟩ := hne
  exact le_csInf ⟨_, mem_range_self γ⟩ (by rintro _ ⟨γ', rfl⟩; exact h γ')

/-- An inhabited path family always has a path within any positive amount above
its minimax value; no minimizing path or minimax attainment is assumed. -/
theorem exists_pathHeight_lt {I : X → ℝ} (hne : Nonempty (Path x y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Path x y, pathHeight I γ < pathMinimax I x y + ε := by
  by_contra! h
  have hle := le_pathMinimax hne h
  linarith

end PDE.Analysis.Variational
