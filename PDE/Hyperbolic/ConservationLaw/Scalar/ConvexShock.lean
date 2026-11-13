/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy
public import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Analysis.Convex.Deriv

/-!
# Convex scalar fluxes and admissible shocks

For a scalar conservation law with convex flux, the Rankine–Hugoniot speed
is the secant slope of the flux between the two states. Monotonicity of slopes of a
convex function then places this speed between the endpoint characteristic speeds.
Strict convexity turns those inequalities into the scalar Lax shock
condition for every compressive jump. The same secant monotonicity gives the
intermediate-state chord inequalities used in Oleinik admissibility.

Throughout, `uR < uL` is the compressive (admissible) orientation and
`uL < uR` the expansive one; for a convex flux the two cases give opposite
inequalities between the shock speed and the endpoint characteristic speeds.
Differentiability of the flux is assumed only at the endpoints where `deriv`
is evaluated.

## Main results

* `rankineHugoniotSpeed_eq_slope`: the Rankine–Hugoniot speed is the secant
  slope `slope flux uR uL`.
* `deriv_right_le_rankineHugoniotSpeed`, `rankineHugoniotSpeed_le_deriv_left`:
  for a convex flux and `uR < uL`, `f'(uR) ≤ s ≤ f'(uL)`; the expansive case
  reverses both inequalities.
* `laxShock_rankineHugoniotSpeed`, `RankineHugoniot.laxShock_iff_right_lt_left`:
  for a strictly convex flux differentiable at the two states, a
  Rankine–Hugoniot jump satisfies the Lax inequalities `f'(uR) < s < f'(uL)`
  exactly when it is compressive.
* `RankineHugoniot.slope_right_le`, `RankineHugoniot.le_slope_left`: the chord
  inequalities `slope f uR k ≤ s ≤ slope f k uL` for every intermediate state
  `uR < k < uL`, which is the Oleinik form of admissibility for a convex flux.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (12) and (17)-(19).
  <https://doi.org/10.1090/gsm/019>
* O. A. Oleĭnik, *Discontinuous solutions of non-linear differential equations*, Amer. Math. Soc.
  Transl. (2) 26 (1963), 95-172 (Russian original 1957), for the chord form of the admissibility
  condition.
  <https://doi.org/10.1090/trans2/026/05>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The Rankine–Hugoniot speed is the secant slope between the right and
left states. -/
theorem rankineHugoniotSpeed_eq_slope (flux : ℝ → ℝ) (uL uR : ℝ) :
    rankineHugoniotSpeed flux uL uR = slope flux uR uL := by
  calc
    rankineHugoniotSpeed flux uL uR = slope flux uL uR := by
      rw [slope_def_field]
      rfl
    _ = slope flux uR uL := slope_comm _ _ _

/-- For a convex flux, the secant slope from the right state to an
intermediate state is at most the Rankine–Hugoniot speed. -/
theorem slope_right_le_rankineHugoniotSpeed {flux : ℝ → ℝ} {uL uR k : ℝ}
    (hconvex : ConvexOn ℝ Set.univ flux) (hright : uR < k) (hleft : k < uL) :
    slope flux uR k ≤ rankineHugoniotSpeed flux uL uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_def_field] using hconvex.secant_mono_aux2
      (Set.mem_univ uR) (Set.mem_univ uL) hright hleft

/-- For a convex flux, the Rankine–Hugoniot speed is at most the secant
slope from an intermediate state to the left state. -/
theorem rankineHugoniotSpeed_le_slope_left {flux : ℝ → ℝ} {uL uR k : ℝ}
    (hconvex : ConvexOn ℝ Set.univ flux) (hright : uR < k) (hleft : k < uL) :
    rankineHugoniotSpeed flux uL uR ≤ slope flux k uL := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_def_field] using hconvex.secant_mono_aux3
      (Set.mem_univ uR) (Set.mem_univ uL) hright hleft

/-- Strict convexity makes the right intermediate-state chord inequality
strict. -/
theorem slope_right_lt_rankineHugoniotSpeed {flux : ℝ → ℝ} {uL uR k : ℝ}
    (hconvex : StrictConvexOn ℝ Set.univ flux) (hright : uR < k) (hleft : k < uL) :
    slope flux uR k < rankineHugoniotSpeed flux uL uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_def_field] using hconvex.secant_strict_mono_aux2
      (Set.mem_univ uR) (Set.mem_univ uL) hright hleft

/-- Strict convexity makes the left intermediate-state chord inequality
strict. -/
theorem rankineHugoniotSpeed_lt_slope_left {flux : ℝ → ℝ} {uL uR k : ℝ}
    (hconvex : StrictConvexOn ℝ Set.univ flux) (hright : uR < k) (hleft : k < uL) :
    rankineHugoniotSpeed flux uL uR < slope flux k uL := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_def_field] using hconvex.secant_strict_mono_aux3
      (Set.mem_univ uR) (Set.mem_univ uL) hright hleft

/-- A Rankine–Hugoniot shock speed for a convex flux dominates every chord
slope from the right state to an intermediate state. -/
theorem RankineHugoniot.slope_right_le {flux : ℝ → ℝ} {uL uR k s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : ConvexOn ℝ Set.univ flux) (hright : uR < k)
    (hleft : k < uL) :
    slope flux uR k ≤ s := by
  rw [(rankineHugoniot_iff_speed_eq (hright.trans hleft).ne).1 hRH]
  exact slope_right_le_rankineHugoniotSpeed hconvex hright hleft

/-- A Rankine–Hugoniot shock speed for a convex flux lies below every chord
slope from an intermediate state to the left state. -/
theorem RankineHugoniot.le_slope_left {flux : ℝ → ℝ} {uL uR k s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : ConvexOn ℝ Set.univ flux) (hright : uR < k)
    (hleft : k < uL) :
    s ≤ slope flux k uL := by
  rw [(rankineHugoniot_iff_speed_eq (hright.trans hleft).ne).1 hRH]
  exact rankineHugoniotSpeed_le_slope_left hconvex hright hleft

/-- Strict convexity makes the right-state chord inequality strict for every
Rankine–Hugoniot shock speed. -/
theorem RankineHugoniot.slope_right_lt {flux : ℝ → ℝ} {uL uR k s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : StrictConvexOn ℝ Set.univ flux)
    (hright : uR < k) (hleft : k < uL) :
    slope flux uR k < s := by
  rw [(rankineHugoniot_iff_speed_eq (hright.trans hleft).ne).1 hRH]
  exact slope_right_lt_rankineHugoniotSpeed hconvex hright hleft

/-- Strict convexity makes the left-state chord inequality strict for every
Rankine–Hugoniot shock speed. -/
theorem RankineHugoniot.lt_slope_left {flux : ℝ → ℝ} {uL uR k s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : StrictConvexOn ℝ Set.univ flux)
    (hright : uR < k) (hleft : k < uL) :
    s < slope flux k uL := by
  rw [(rankineHugoniot_iff_speed_eq (hright.trans hleft).ne).1 hRH]
  exact rankineHugoniotSpeed_lt_slope_left hconvex hright hleft

/-- For a convex flux, the right-state characteristic speed is at most the
Rankine–Hugoniot speed of a compressive jump. -/
theorem deriv_right_le_rankineHugoniotSpeed {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uR < uL)
    (hdifferentiable : DifferentiableAt ℝ flux uR) :
    deriv flux uR ≤ rankineHugoniotSpeed flux uL uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  exact hconvex.deriv_le_slope (Set.mem_univ uR) (Set.mem_univ uL) hstate hdifferentiable

/-- For a convex flux, the Rankine–Hugoniot speed of a compressive jump is
at most the left-state characteristic speed. -/
theorem rankineHugoniotSpeed_le_deriv_left {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uR < uL)
    (hdifferentiable : DifferentiableAt ℝ flux uL) :
    rankineHugoniotSpeed flux uL uR ≤ deriv flux uL := by
  rw [rankineHugoniotSpeed_eq_slope]
  exact hconvex.slope_le_deriv (Set.mem_univ uR) (Set.mem_univ uL) hstate hdifferentiable

/-- For a convex flux, every Rankine–Hugoniot speed of a compressive jump
dominates the right-state characteristic speed. -/
theorem RankineHugoniot.deriv_right_le {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uR < uL)
    (hdifferentiable : DifferentiableAt ℝ flux uR) :
    deriv flux uR ≤ s := by
  rw [(rankineHugoniot_iff_speed_eq hstate.ne).1 hRH]
  exact deriv_right_le_rankineHugoniotSpeed hconvex hstate hdifferentiable

/-- For a convex flux, every Rankine–Hugoniot speed of a compressive jump
lies below the left-state characteristic speed. -/
theorem RankineHugoniot.le_deriv_left {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uR < uL)
    (hdifferentiable : DifferentiableAt ℝ flux uL) :
    s ≤ deriv flux uL := by
  rw [(rankineHugoniot_iff_speed_eq hstate.ne).1 hRH]
  exact rankineHugoniotSpeed_le_deriv_left hconvex hstate hdifferentiable

/-- For a convex flux, the left-state characteristic speed is at most the
Rankine–Hugoniot speed of an expansive jump. -/
theorem deriv_left_le_rankineHugoniotSpeed {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uL < uR)
    (hdifferentiable : DifferentiableAt ℝ flux uL) :
    deriv flux uL ≤ rankineHugoniotSpeed flux uL uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_comm] using hconvex.deriv_le_slope
      (Set.mem_univ uL) (Set.mem_univ uR) hstate hdifferentiable

/-- For a convex flux, the Rankine–Hugoniot speed of an expansive jump is
at most the right-state characteristic speed. -/
theorem rankineHugoniotSpeed_le_deriv_right {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uL < uR)
    (hdifferentiable : DifferentiableAt ℝ flux uR) :
    rankineHugoniotSpeed flux uL uR ≤ deriv flux uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_comm] using hconvex.slope_le_deriv
      (Set.mem_univ uL) (Set.mem_univ uR) hstate hdifferentiable

/-- Strict convexity places the Rankine–Hugoniot speed of an expansive
jump strictly above the left-state characteristic speed. -/
theorem deriv_left_lt_rankineHugoniotSpeed {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : StrictConvexOn ℝ Set.univ flux) (hstate : uL < uR)
    (hdifferentiable : DifferentiableAt ℝ flux uL) :
    deriv flux uL < rankineHugoniotSpeed flux uL uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_comm] using hconvex.deriv_lt_slope
      (Set.mem_univ uL) (Set.mem_univ uR) hstate hdifferentiable

/-- Strict convexity places the Rankine–Hugoniot speed of an expansive
jump strictly below the right-state characteristic speed. -/
theorem rankineHugoniotSpeed_lt_deriv_right {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : StrictConvexOn ℝ Set.univ flux) (hstate : uL < uR)
    (hdifferentiable : DifferentiableAt ℝ flux uR) :
    rankineHugoniotSpeed flux uL uR < deriv flux uR := by
  rw [rankineHugoniotSpeed_eq_slope]
  simpa only [slope_comm] using hconvex.slope_lt_deriv
      (Set.mem_univ uL) (Set.mem_univ uR) hstate hdifferentiable

/-- Every Rankine–Hugoniot speed of an expansive jump for a convex flux
lies above the left-state characteristic speed. -/
theorem RankineHugoniot.deriv_left_le {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uL < uR)
    (hdifferentiable : DifferentiableAt ℝ flux uL) :
    deriv flux uL ≤ s := by
  rw [(rankineHugoniot_iff_speed_eq hstate.ne').1 hRH]
  exact deriv_left_le_rankineHugoniotSpeed hconvex hstate hdifferentiable

/-- Every Rankine–Hugoniot speed of an expansive jump for a convex flux
lies below the right-state characteristic speed. -/
theorem RankineHugoniot.le_deriv_right {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : ConvexOn ℝ Set.univ flux) (hstate : uL < uR)
    (hdifferentiable : DifferentiableAt ℝ flux uR) :
    s ≤ deriv flux uR := by
  rw [(rankineHugoniot_iff_speed_eq hstate.ne').1 hRH]
  exact rankineHugoniotSpeed_le_deriv_right hconvex hstate hdifferentiable

/-- The Rankine–Hugoniot speed of a compressive jump for a strictly convex
flux satisfies the scalar Lax shock inequalities. -/
theorem laxShock_rankineHugoniotSpeed {flux : ℝ → ℝ} {uL uR : ℝ}
    (hconvex : StrictConvexOn ℝ Set.univ flux) (hstate : uR < uL)
    (hdifferentiableRight : DifferentiableAt ℝ flux uR)
    (hdifferentiableLeft : DifferentiableAt ℝ flux uL) :
    LaxShock (deriv flux) uL uR (rankineHugoniotSpeed flux uL uR) := by
  rw [rankineHugoniotSpeed_eq_slope]
  exact ⟨hconvex.deriv_lt_slope (Set.mem_univ uR) (Set.mem_univ uL) hstate hdifferentiableRight,
      hconvex.slope_lt_deriv (Set.mem_univ uR) (Set.mem_univ uL) hstate hdifferentiableLeft⟩

/-- Every Rankine–Hugoniot speed for a compressive jump of a strictly
convex flux satisfies the scalar Lax shock inequalities. -/
theorem RankineHugoniot.laxShock_of_strictConvex {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : StrictConvexOn ℝ Set.univ flux)
    (hstate : uR < uL) (hdifferentiableRight : DifferentiableAt ℝ flux uR)
    (hdifferentiableLeft : DifferentiableAt ℝ flux uL) :
    LaxShock (deriv flux) uL uR s := by
  have hs : s = rankineHugoniotSpeed flux uL uR := (rankineHugoniot_iff_speed_eq hstate.ne).1 hRH
  rw [hs]
  exact laxShock_rankineHugoniotSpeed hconvex hstate hdifferentiableRight hdifferentiableLeft

/-- An expansive Rankine–Hugoniot jump for a strictly convex flux cannot
satisfy the scalar Lax shock inequalities. -/
theorem RankineHugoniot.not_laxShock_of_strictConvex {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : StrictConvexOn ℝ Set.univ flux)
    (hstate : uL < uR) (hdifferentiableLeft : DifferentiableAt ℝ flux uL) :
    ¬ LaxShock (deriv flux) uL uR s := by
  intro hLax
  have hleft : deriv flux uL < rankineHugoniotSpeed flux uL uR := deriv_left_lt_rankineHugoniotSpeed
      hconvex hstate hdifferentiableLeft
  have hs : s = rankineHugoniotSpeed flux uL uR := (rankineHugoniot_iff_speed_eq hstate.ne').1 hRH
  rw [← hs] at hleft
  exact (not_lt_of_ge hLax.right.le) hleft

/-- For distinct states and a strictly convex differentiable flux, a
Rankine–Hugoniot jump is Lax-admissible exactly when it is compressive. -/
theorem RankineHugoniot.laxShock_iff_right_lt_left {flux : ℝ → ℝ} {uL uR s : ℝ}
    (hRH : RankineHugoniot flux uL uR s) (hconvex : StrictConvexOn ℝ Set.univ flux)
    (hstates : uR ≠ uL) (hdifferentiableRight : DifferentiableAt ℝ flux uR)
    (hdifferentiableLeft : DifferentiableAt ℝ flux uL) :
    LaxShock (deriv flux) uL uR s ↔ uR < uL := by
  constructor
  · intro hLax
    rcases lt_or_gt_of_ne hstates with hcompressive | expansive
    · exact hcompressive
    · exact False.elim <| hRH.not_laxShock_of_strictConvex
          hconvex expansive hdifferentiableLeft hLax
  · exact fun hcompressive ↦ hRH.laxShock_of_strictConvex
      hconvex hcompressive hdifferentiableRight hdifferentiableLeft

end PDE.Hyperbolic.ConservationLaw.Scalar
