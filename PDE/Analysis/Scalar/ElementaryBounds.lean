/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary real bounds

Small estimates used by several stability and certificate arguments.

* `geom_sum_Ico_le_two_mul`, `geom_sum_range_le_two`: for `0 ≤ δ ≤ 1/2`,
  `∑_{a ≤ n < b} δⁿ ≤ 2 δᵃ` and `∑_{n < b} δⁿ ≤ 2`.
* `abs_mul_sub_mul_le_of_le`: the error of a product of two approximations,
  `|a b - c d| ≤ e_a B + A e_b` when `|a - c| ≤ e_a`, `|b - d| ≤ e_b`, `|c| ≤ A` and `|b| ≤ B`.
* `abs_natCast_div_sub_le`: natural-number division is within one of the real quotient.
* `fderiv_coordinate`: if a Euclidean-valued function is differentiable at `x`, its coordinates
  are differentiated coordinatewise there, `D(fᵢ)(x) v = (Df(x) v)ᵢ`.
-/

@[expose] public section

namespace PDE.Analysis

/-- A geometric sum over `[a, b)` with ratio `0 ≤ δ ≤ 1/2` is at most `2 δᵃ`. -/
theorem geom_sum_Ico_le_two_mul {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, δ ^ n ≤ 2 * δ ^ a :=
  (geom_sum_Ico_le_of_lt_one h0 (by linarith)).trans <| by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg h0 a]

/-- A partial geometric sum with ratio `0 ≤ δ ≤ 1/2` is at most `2`. -/
theorem geom_sum_range_le_two {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) (b : ℕ) :
    ∑ n ∈ Finset.range b, δ ^ n ≤ 2 := by
  simpa only [Finset.range_eq_Ico, pow_zero, mul_one] using geom_sum_Ico_le_two_mul h0 h1 0 b

/-- The error of a product of two approximations: if `|a - c| ≤ e_a`, `|b - d| ≤ e_b`,
`|c| ≤ A` and `|b| ≤ B`, then `|a b - c d| ≤ e_a B + A e_b`. -/
theorem abs_mul_sub_mul_le_of_le {a b c d ea eb A B : ℝ} (ha : |a - c| ≤ ea)
    (hb : |b - d| ≤ eb) (hc : |c| ≤ A) (hd : |b| ≤ B) :
    |a * b - c * d| ≤ ea * B + A * eb := by
  have hea : 0 ≤ ea := le_trans (abs_nonneg _) ha
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hc
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |a - c| * |b| + |c| * |b - d| := by
      simpa only [abs_mul] using abs_add_le ((a - c) * b) (c * (b - d))
    _ ≤ ea * B + A * eb := add_le_add
      (mul_le_mul ha hd (abs_nonneg _) hea)
      (mul_le_mul hc hb (abs_nonneg _) hA)

/-- Natural-number division is within one of the real quotient:
`|⌊N / D⌋ - N / D| ≤ 1` for `D > 0`. -/
theorem abs_natCast_div_sub_le (N D : ℕ) (hD : 0 < D) :
    |((N / D : ℕ) : ℝ) - (N : ℝ) / D| ≤ 1 := by
  have h := Nat.abs_floor_sub_le (show (0 : ℝ) ≤ (N : ℝ) / D from
    div_nonneg (Nat.cast_nonneg N) (Nat.cast_pos.mpr hD).le)
  rwa [Nat.floor_div_eq_div] at h

/-- If `f` is differentiable at `x`, taking a Euclidean coordinate commutes with differentiation
at `x`. -/
theorem fderiv_coordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    [Finite ι] {f : E → EuclideanSpace ℝ ι} {x : E} (hf : DifferentiableAt ℝ f x) (i : ι)
    (v : E) : fderiv ℝ (fun y ↦ f y i) x v = (fderiv ℝ f x v) i := by
  have := Fintype.ofFinite ι
  have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f x) i).comp x hf.hasFDerivAt
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h.fderiv

end PDE.Analysis
