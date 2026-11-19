/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.Minimax.CriticalValue

/-!
# The mountain-pass theorem

A continuous path from the origin to a point outside a positive-radius sphere
must cross that sphere. A positive energy barrier therefore bounds every path's
height from below. The segment is an admissible path, and the deformation theorem
proves that the minimax value is a nonzero critical value.

The state space may be any complete real Hilbert space, and the energy need not be
bounded below. `PalaisSmale.mountain_pass` is the mountain pass theorem of Evans, §8.5.1,
Theorem 2: his class `C` is given by the hypotheses `hI` and `hG`, and his hypotheses
(i)-(iii) are `hzero`; `hr`, `ha` and `hbarrier`; and `hv` with `hIv`. Besides the critical
value we record his estimate (16), `c ≥ a`, and that the critical point is nonzero, since its
energy is at least `a > 0 = I 0`.

## Main results

* `le_pathHeight_of_sphere`: if a sphere separates the endpoints of a path, the height of the
  path is at least any lower bound of the energy on the sphere.
* `PalaisSmale.mountain_pass`: the minimax value over paths from `0` to `v` is at least `a`
  and is the energy of a nonzero critical point.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(b), Theorem 2 (Mountain Pass Theorem) and its
  proof, (16)-(21), pp. 505-506. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Metric Set

namespace PDE.Analysis.Variational

section Sphere

variable {E : Type*} [NormedAddCommGroup E]

/-- A sphere separating the endpoints of a path gives a lower bound for its energy
height. The crossing uses continuity of the path norm. -/
theorem le_pathHeight_of_sphere {I : E → ℝ} (hI : Continuous I) {x y : E}
    {r a : ℝ} (hx : ‖x‖ ≤ r) (hy : r ≤ ‖y‖)
    (hbarrier : ∀ u, ‖u‖ = r → a ≤ I u) (γ : Path x y) :
    a ≤ pathHeight I γ := by
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 γ.continuous.norm
    (show r ∈ Icc ‖γ 0‖ ‖γ 1‖ by simpa only [γ.source, γ.target] using ⟨hx, hy⟩)
  exact (hbarrier (γ t) ht).trans (le_pathHeight hI γ t)

end Sphere

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The raw mountain-pass theorem. The output is a nonzero critical point at the
defined path minimax value, which is at least the positive sphere barrier. -/
theorem PalaisSmale.mountain_pass {I : H → ℝ} (hPS : PalaisSmale I)
    (hI : ContDiff ℝ 1 I)
    (hG : ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, LipschitzOnWith K (∇ I) (closedBall 0 R))
    (hzero : I 0 = 0) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hbarrier : ∀ u, ‖u‖ = r → a ≤ I u)
    {v : H} (hv : r < ‖v‖) (hIv : I v ≤ 0) :
    a ≤ pathMinimax I 0 v ∧
      ∃ u : H, u ≠ 0 ∧ I u = pathMinimax I 0 v ∧ ∇ I u = 0 := by
  have hpaths : Nonempty (Path (0 : H) v) := ⟨Path.segment 0 v⟩
  have hc : a ≤ pathMinimax I 0 v := le_pathMinimax hpaths fun γ ↦
    le_pathHeight_of_sphere hI.continuous (by simpa using hr.le) hv.le hbarrier γ
  obtain ⟨u, huI, huG⟩ := hPS.exists_criticalPoint_pathMinimax hI hG hpaths
    (by rw [hzero]; exact ha.trans_le hc) (hIv.trans_lt (ha.trans_le hc))
  refine ⟨hc, u, ?_, huI, huG⟩
  intro hu
  rw [hu, hzero] at huI
  linarith

end PDE.Analysis.Variational
