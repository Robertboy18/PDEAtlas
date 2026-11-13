/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.Deformation.Theorem
public import PDE.Analysis.Variational.CriticalPoint.Minimax.Paths

/-!
# Criticality of a path minimax value

When the minimax value lies strictly above both endpoint energies, a deformation
around a hypothetical noncritical value fixes both endpoints. An approximating path
is then lowered strictly below the infimum of all path heights, a contradiction.
Only the path family is assumed inhabited. No optimal path is needed.

This is the proof of the mountain pass theorem in Evans, §8.5.1, Theorem 2, (17)-(21), for
paths between arbitrary endpoints `x` and `y`. In place of his `c ≥ a > 0 = I[0] ≥ I[v]` we
assume only `I x < c` and `I y < c`, and the deformation band is at most half of each gap, as
his (18) takes `ε < a / 2`.

## Main results

* `PalaisSmale.exists_criticalPoint_pathMinimax`: under the hypotheses of the deformation
  theorem, if some path joins `x` to `y` and both `I x` and `I y` are below
  `pathMinimax I x y`, then some critical point has energy `pathMinimax I x y`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(b), the proof of Theorem 2 (Mountain Pass
  Theorem), (16)-(21), p. 506. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Metric Set

namespace PDE.Analysis.Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A path minimax value strictly above the endpoint energies is a critical
value under the raw Palais–Smale and bounded-ball gradient Lipschitz hypotheses. -/
theorem PalaisSmale.exists_criticalPoint_pathMinimax {I : H → ℝ} (hPS : PalaisSmale I)
    (hI : ContDiff ℝ 1 I)
    (hG : ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, LipschitzOnWith K (∇ I) (closedBall 0 R))
    {x y : H} (hpaths : Nonempty (Path x y))
    (hx : I x < pathMinimax I x y) (hy : I y < pathMinimax I x y) :
    ∃ u : H, I u = pathMinimax I x y ∧ ∇ I u = 0 := by
  by_contra! hnone
  let c := pathMinimax I x y
  obtain ⟨ε₀, hε₀, hdef⟩ := hPS.exists_deformation hI hG hnone
  let ε := min (ε₀ / 2) (min ((c - I x) / 2) ((c - I y) / 2))
  have hε : 0 < ε := lt_min (by linarith) (lt_min (by dsimp [c]; linarith)
    (by dsimp [c]; linarith))
  have hε₀' : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have hεx : ε ≤ |I x - c| := by
    have hle := (min_le_right (ε₀ / 2) _).trans
      (min_le_left ((c - I x) / 2) ((c - I y) / 2))
    have habs := neg_le_abs (I x - c)
    change ε ≤ (c - I x) / 2 at hle
    change I x < c at hx
    linarith
  have hεy : ε ≤ |I y - c| := by
    have hle := (min_le_right (ε₀ / 2) _).trans
      (min_le_right ((c - I x) / 2) ((c - I y) / 2))
    have habs := neg_le_abs (I y - c)
    change ε ≤ (c - I y) / 2 at hle
    change I y < c at hy
    linarith
  obtain ⟨δ, hδ, Φ, _, hfix, _, hdrop⟩ := hdef ε ⟨hε, hε₀'⟩
  obtain ⟨γ, hγ⟩ := exists_pathHeight_lt (I := I) hpaths hδ.1
  let γ' : Path x y := (γ.map (Φ.continuous_toFun 1)).cast
    (hfix x 1 hεx).symm (hfix y 1 hεy).symm
  have hheight : pathHeight I γ' ≤ c - δ := by
    apply pathHeight_le
    intro t
    dsimp [γ']
    rw [Path.map_coe, Function.comp_apply]
    exact hdrop (γ t) ((le_pathHeight hI.continuous γ t).trans hγ.le)
  have hlow := pathMinimax_le_pathHeight hI.continuous γ'
  change c ≤ pathHeight I γ' at hlow
  linarith [hδ.1]

end PDE.Analysis.Variational
