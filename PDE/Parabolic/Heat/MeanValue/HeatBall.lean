/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Basic

/-!
# Heat balls and the Evans mean-value weight

For a spacetime pole `(x,t)` and `r > 0`, the heat ball is the superlevel set

`E(x,t;r) = {(y,s) | Γ(x-y,t-s) > r⁻ⁿ}`.

Evans (§2.3.2) defines `E(x,t;r)` by `s ≤ t` and `Γ(x-y,t-s) ≥ r⁻ⁿ`. We use the strict
superlevel set, which is open. Its closure is the set where `Γ(x-y,t-s) ≥ r⁻ⁿ` together with
the pole (`closure_heatBall_eq_insert_pole` in `MeanValue.Closure`).

The weight in Watson's heat-ball mean-value formula is
`|x-y|² / (t-s)²`.  Spacetime points use LeanPDE's canonical time-first
coordinate convention through `PDE.time` and `PDE.Common.spatialPart`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, definition of the heat ball.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (time SpaceTime)

noncomputable section

namespace HeatEquation

open PDE.Common

variable {n : ℕ}

/-- The Evans heat ball with pole `(x,t)` and radius parameter `r`.

The geometric lemmas assume positive spatial dimension and `r > 0` where
they need them. -/
def heatBall (x : ℝ^n) (t r : ℝ) : Set (SpaceTime n) :=
  {p | (r ^ n)⁻¹ <
    shiftedFundamentalSolutionHeat x (spatialPart p) t (time p)}

/-- The scalar weight in Watson's heat-ball mean-value formula. -/
def heatBallWeight (x : ℝ^n) (t : ℝ) (p : SpaceTime n) : ℝ :=
  ‖x - spatialPart p‖ ^ 2 / (t - time p) ^ 2

/-- Membership in a heat ball is exactly the defining heat-kernel inequality. -/
@[simp]
theorem mem_heatBall_iff {x : ℝ^n} {t r : ℝ} {p : SpaceTime n} :
    p ∈ heatBall x t r ↔
      (r ^ n)⁻¹ <
        shiftedFundamentalSolutionHeat x (spatialPart p) t (time p) :=
  Iff.rfl

/-- The heat-ball threshold is positive at positive radius. -/
theorem heatBall_threshold_pos {r : ℝ} (hr : 0 < r) :
    0 < (r ^ n)⁻¹ :=
  inv_pos.mpr (pow_pos hr n)

/-- Every point of a positive-radius heat ball lies strictly before its pole in time. -/
theorem time_lt_of_mem_heatBall {x : ℝ^n} {t r : ℝ}
    (hr : 0 < r) {p : SpaceTime n} (hp : p ∈ heatBall x t r) :
    time p < t := by
  by_contra hpt
  have hlag : t - time p ≤ 0 := sub_nonpos.mpr (le_of_not_gt hpt)
  have hthreshold : 0 < (r ^ n)⁻¹ := heatBall_threshold_pos hr
  rw [mem_heatBall_iff, shiftedFundamentalSolutionHeat,
    fundamentalSolutionHeat, ite_eq_left hlag] at hp
  linarith

/-- The backward time lag is positive throughout a positive-radius heat ball. -/
theorem timeLag_pos_of_mem_heatBall {x : ℝ^n} {t r : ℝ}
    (hr : 0 < r) {p : SpaceTime n} (hp : p ∈ heatBall x t r) :
    0 < t - time p :=
  sub_pos.mpr (time_lt_of_mem_heatBall hr hp)

/-- The Evans heat-ball weight is nonnegative. -/
theorem heatBallWeight_nonneg (x : ℝ^n) (t : ℝ) (p : SpaceTime n) :
    0 ≤ heatBallWeight x t p := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Away from the pole's spatial line, the heat-ball weight is positive. -/
theorem heatBallWeight_pos {x : ℝ^n} {t r : ℝ}
    (hr : 0 < r) {p : SpaceTime n} (hp : p ∈ heatBall x t r)
    (hspace : spatialPart p ≠ x) :
    0 < heatBallWeight x t p := by
  unfold heatBallWeight
  apply div_pos
  · exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hspace.symm))
  · exact sq_pos_of_pos (timeLag_pos_of_mem_heatBall hr hp)

end HeatEquation
