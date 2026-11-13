/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.Similarity
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import PDE.FDeriv.Calculus

/-!
# Green kernel for the unit ball

The Dirichlet Green function of `-Δ` on the unit ball `B = B(0, 1) ⊆ ℝ^n` is obtained from the
fundamental solution `Φ` by inversion through the unit sphere. Writing `x* = x / ‖x‖²` for the
point dual to an interior point `x ≠ 0`, the corrector `y ↦ Φ(‖x‖ (y - x*))` is harmonic in `y`
on the ball and agrees with `Φ(y - x)` on the sphere `‖y‖ = 1`, so that

`G(x, y) = Φ(y - x) - Φ(‖x‖ (y - x*))`

vanishes for `‖y‖ = 1`. This is Evans's definition (41) of Green's function for the unit ball in
§2.2.4(c), with the corrector (39). We prove boundary vanishing and classical off-pole
harmonicity for `n ≥ 2`.

The definition `ballGreenFunction` covers every positive dimension: for `n = 2` it uses the
logarithmic kernel, for `n ≥ 3` the Newtonian kernel, and for `n = 1` the explicit Green function
`(1 - max x y)(1 + min x y) / 2` of `-d²/dx²` on `(-1, 1)`. At `x = 0` the reflected point `x*`
is not defined; for `n ≥ 3` the definition fills that in with the constant corrector `Φ(1)`, the
limit of `Φ(‖x‖ (y - x*))` as `x → 0`, and `invertPoint` sends `0` to `0`.

## Main results

* `invertPoint`: inversion `x ↦ x / ‖x‖²` through the unit sphere, extended by `0 ↦ 0`.
* `ballGreenFunction`: the Green function of the unit ball in every positive dimension.
* `ballGreenFunction_boundary`: for `n ≥ 2`, `‖x‖ < 1` and `‖y‖ = 1`, `G(x, y) = 0`.
* `ballGreenFunction_harmonic`: for `n ≥ 2`, `‖x‖ < 1`, `‖y‖ < 1` and `y ≠ x`,
  `Δ_y G(x, y) = 0` (classical Laplacian in the second argument).

## How it works

Evans checks the boundary values (40) of the corrector with the identity
`‖x‖² ‖y - x*‖² = ‖x - y‖²` for `‖y‖ = 1`, and the same identity, proved in the private
preliminaries, gives `ballGreenFunction_boundary`. For `ballGreenFunction_harmonic`, both terms of
`G(x, ·)` are the fundamental solution composed with a translation and a positive dilation, so
`PotentialTheory.laplacian_fundamentalSolution_smul_sub_eq_zero` applies to each of them away
from its pole; the image pole `x*` lies outside the unit ball, and for `x = 0` the corrector is
constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(c), the point dual to `x` and inversion through the
  unit sphere, the corrector (39) with its boundary values (40), p. 39, and Green's function for the
  unit ball (41), p. 40.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace GreenFunction

open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

/-- Inversion `x ↦ x / ‖x‖²` through the unit sphere, extended by `0 ↦ 0`. -/
noncomputable def invertPoint {n : ℕ}
    (x : ℝ^n) : ℝ^n :=
  if x = 0 then 0 else (1 / ‖x‖ ^ 2) • x

/-- Green's function for the unit ball.

For `n = 1`, this is the Dirichlet Green kernel for `-d²/dx²` on `(-1, 1)`.
For `n ≥ 2`, it is Evans's formula (41) in §2.2.4(c).
Boundary vanishing and classical harmonicity away from the pole are proved
below for `n ≥ 2`; the one-dimensional properties and the distributional
identity `-Δ_y G(x, ·) = δ_x` are not. -/
noncomputable def ballGreenFunction {n : ℕ} [Fact (0 < n)] (x y : ℝ^n) : ℝ :=
  -- Evans's (41): `G(x,y) = Φ(y-x) - Φ(|x|(y-x*))`, where `x* = x/|x|²` is the point dual to `x`.
  -- For `n ≥ 3`, one also needs the `x = 0` limit case, which is `Φ(y) - Φ(1)`.
  if _h2 : n = 2 then
    PotentialTheory.fundamentalSolution n (y - x) -
      PotentialTheory.fundamentalSolution n (‖x‖ • (y - invertPoint (n := n) x))
  else if _hn3 : 3 ≤ n then
    if _hx : x = 0 then
      PotentialTheory.fundamentalSolution n y -
        (1 / (((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n))
    else
      PotentialTheory.fundamentalSolution n (y - x) -
        PotentialTheory.fundamentalSolution n (‖x‖ • (y - invertPoint (n := n) x))
  else
    let i0 : Fin n := ⟨0, Fact.out⟩
    ((1 - max (x i0) (y i0)) * (1 + min (x i0) (y i0))) / 2

section BallProofs

open scoped BigOperators
open scoped InnerProductSpace

variable {n : ℕ}

private theorem invertPoint_eq_smul (x : ℝ^n) (hx : x ≠ 0) :
    invertPoint (n := n) x = (1 / (‖x‖ ^ 2)) • x := by
  simp [invertPoint, hx]

private theorem norm_invertPoint (x : ℝ^n) (hx : x ≠ 0) :
    ‖invertPoint (n := n) x‖ = 1 / ‖x‖ := by
  have := norm_ne_zero_iff.2 hx
  rw [invertPoint_eq_smul x hx, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp

private theorem one_lt_norm_invertPoint {x : ℝ^n} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    1 < ‖invertPoint (n := n) x‖ := by
  rw [norm_invertPoint x hx0]
  exact (one_lt_div (norm_pos_iff.2 hx0)).2 hx

private theorem norm_sub_eq_mul_norm_sub_invertPoint {x y : ℝ^n} (hx : x ≠ 0) (hy : ‖y‖ = 1) :
    ‖y - x‖ = ‖x‖ * ‖y - invertPoint (n := n) x‖ := by
  have := norm_ne_zero_iff.2 hx
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_sub_sq_real, norm_sub_sq_real,
    invertPoint_eq_smul x hx, real_inner_smul_right, norm_smul, Real.norm_of_nonneg (by positivity),
    hy]
  field_simp
  ring

private theorem unitBall_ne_invertPoint {x y : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) 1)
    (hx0 : x ≠ 0) (hy : y ∈ Metric.ball (0 : ℝ^n) 1) :
    y ≠ invertPoint (n := n) x := by
  rintro rfl
  exact lt_asymm (one_lt_norm_invertPoint (mem_ball_zero_iff.1 hx) hx0) (mem_ball_zero_iff.1 hy)

section PositiveDimension

variable [Fact (0 < n)]

/-- The unit-ball Green function vanishes in its second argument on the boundary sphere. -/
theorem ballGreenFunction_boundary
    (hn : 2 ≤ n) {x y : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) 1)
    (hy : y ∈ Metric.sphere (0 : ℝ^n) 1) :
    ballGreenFunction (n := n) x y = 0 := by
  have hy_norm : ‖y‖ = 1 := by simpa using hy
  by_cases hx0 : x = 0
  · subst hx0
    by_cases h2 : n = 2
    · subst h2
      simp [ballGreenFunction, fundamentalSolution_two, hy_norm]
    · simp [ballGreenFunction, h2, show 3 ≤ n by omega, fundamentalSolution_of_three_le
        (show 3 ≤ n by omega), hy_norm]
  have hΦ : fundamentalSolution n (y - x) = fundamentalSolution n (‖x‖ • (y - invertPoint x)) :=
    fundamentalSolution_eq_of_norm_eq <| by
      rw [norm_sub_eq_mul_norm_sub_invertPoint hx0 hy_norm, norm_smul,
        Real.norm_of_nonneg (norm_nonneg x)]
  by_cases h2 : n = 2
  · simp [ballGreenFunction, h2, hΦ]
  · simp [ballGreenFunction, h2, show 3 ≤ n by omega, hx0, hΦ]

/-- Away from its pole, the unit-ball Green function is harmonic in its second argument. -/
theorem ballGreenFunction_harmonic
    (hn : 2 ≤ n) {x y : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) 1)
    (hy : y ∈ Metric.ball (0 : ℝ^n) 1) (hxy : y ≠ x) :
    laplacian (n := n) (fun z ↦ ballGreenFunction (n := n) x z) y = 0 := by
  classical
  by_cases hx0 : x = 0
  · subst x
    by_cases h2 : n = 2
    · subst n
      simpa [ballGreenFunction] using laplacian_fundamentalSolution_eq_zero 2 y hxy
    · have hkernel : (fun z ↦ ballGreenFunction (n := n) 0 z) =
          fun z ↦ fundamentalSolution n z - 1 / (((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n) := by
        funext z
        simp [ballGreenFunction, h2, show 3 ≤ n by omega]
      rw [hkernel, PDE.laplacian_sub _ _ y ((contDiffAt_fundamentalSolution n y hxy).of_le
        (by norm_num)) contDiffAt_const, laplacian_fundamentalSolution_eq_zero n y hxy,
        PDE.laplacian_const, sub_self]
  · have hyinv := unitBall_ne_invertPoint hx hx0 hy
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hkernel : (fun z ↦ ballGreenFunction (n := n) x z) =
        fun z ↦ fundamentalSolution n (z - x) -
          fundamentalSolution n (‖x‖ • (z - invertPoint x)) := by
      funext z
      by_cases h2 : n = 2
      · simp [ballGreenFunction, h2]
      · simp [ballGreenFunction, h2, show 3 ≤ n by omega, hx0]
    have hfirst : ContDiffAt ℝ 2 (fun z ↦ fundamentalSolution n (z - x)) y := by
      simpa using
        (contDiffAt_fundamentalSolution_smul_sub n zero_lt_one x y hxy).of_le
          (by norm_num)
    have hsecond : ContDiffAt ℝ 2
        (fun z ↦ fundamentalSolution n (‖x‖ • (z - invertPoint x))) y :=
      (contDiffAt_fundamentalSolution_smul_sub n hxpos (invertPoint x) y hyinv).of_le
        (by norm_num)
    have hfirst_lap : laplacian (fun z ↦ fundamentalSolution n (z - x)) y = 0 := by
      simpa using laplacian_fundamentalSolution_smul_sub_eq_zero n zero_lt_one x y hxy
    rw [hkernel, PDE.laplacian_sub _ _ y hfirst hsecond, hfirst_lap,
      laplacian_fundamentalSolution_smul_sub_eq_zero n hxpos (invertPoint x) y hyinv,
      sub_self]

end PositiveDimension

end BallProofs

end GreenFunction
