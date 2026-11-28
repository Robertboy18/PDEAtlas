/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates.Integral
public import PDE.Analysis.Calculus.SymbolDecay.Far
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Harmonic functions near infinity: a bound on the function bounds every derivative

If a function is harmonic outside a ball and is `O(‖x‖ ^ d)` there, each derivative gains one
power of decay, as for a homogeneous function: the `k`th derivative is `O(‖x‖ ^ (d - k))`. This
turns a bound on a Newtonian potential into bounds on all its derivatives
(`PoissonEquation.hasSymbolDecay_fundamentalSolutionConvolution`). The statement is for scalar
functions, as `IsHarmonicPDE` is.

## Main results

* `LaplacianEquation.IsHarmonicPDE.hasSymbolDecay`: a function on `ℝⁿ` that is smooth off the
  origin, harmonic outside a ball and bounded there by `C ‖x‖ ^ d` has symbol decay of order `d`.

## How it works

Around a far point `x` the ball of radius `‖x‖ / 2` stays in the region where `u` is harmonic,
and every point of it has norm between `‖x‖ / 2` and `2 ‖x‖`. The interior estimate
(`IsHarmonicPDE.norm_iteratedFDeriv_le_integral_abs_of_closedBall`) bounds `Dᵏu(x)` by
`r^{-n-k}` times the integral of `|u|` over the ball of radius `r`. With `r = ‖x‖ / 2` the
integral is at most a multiple of `‖x‖ ^ (d + n)`, which gives `‖Dᵏu(x)‖ ≤ C ‖x‖ ^ (d - k)`, and
`PDE.Analysis.HasSymbolDecay.of_bound_far` turns these bounds far out into symbol decay.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 7 (Estimates on derivatives), (18)-(19),
  p. 29.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Metric PDE.Analysis
open scoped ContDiff

namespace LaplacianEquation

/-- A function on `ℝⁿ` that is smooth off the origin, harmonic outside the ball of radius `R`
and bounded there by `C ‖x‖ ^ d` has symbol decay of order `d`: its `k`th derivative is
`O(‖x‖ ^ (d - k))`. The proof applies the interior derivative estimate on the ball of radius
`‖x‖ / 2` around `x`. -/
theorem IsHarmonicPDE.hasSymbolDecay {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {R C : ℝ} {d : ℤ}
    (hu : IsHarmonicPDE n u {x | R < ‖x‖}) (hsmooth : ContDiffOn ℝ ∞ u {0}ᶜ)
    (hbound : ∀ x, R < ‖x‖ → |u x| ≤ C * ‖x‖ ^ d) : HasSymbolDecay d u := by
  refine HasSymbolDecay.of_bound_far hsmooth (ρ := 2 * |R| + 2) fun k ↦ ?_
  have hc := (interiorDerivativeConstant_pos n k).le
  refine ⟨interiorDerivativeConstant n k * unitBallVolume n * (|C| * 2 ^ d.natAbs) * 2 ^ k,
    fun x hx ↦ ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith [abs_nonneg R]
  have hrpos : 0 < ‖x‖ / 2 := half_pos hxpos
  -- Every point of the ball of radius `‖x‖ / 2` has norm between `‖x‖ / 2` and `2 ‖x‖`.
  have hnorm : ∀ y ∈ closedBall x (‖x‖ / 2), ‖x‖ / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * ‖x‖ := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
      calc ‖x‖ = ‖y - (y - x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y‖ + ‖y - x‖ := norm_sub_le _ _
    have h2 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    exact ⟨by linarith, by linarith⟩
  have hball : closedBall x (‖x‖ / 2) ⊆ {y | R < ‖y‖} := fun y hy ↦ by
    have h := (hnorm y hy).1
    change R < ‖y‖
    linarith [le_abs_self R]
  have hest := hu.norm_iteratedFDeriv_le_integral_abs_of_closedBall (k := k) hrpos hball
  -- On the ball, `|u|` is at most a fixed multiple of `‖x‖ ^ d`.
  have hpt : ∀ y ∈ ball x (‖x‖ / 2), |u y| ≤ |C| * 2 ^ d.natAbs * ‖x‖ ^ d := by
    intro y hy
    obtain ⟨h1, h2⟩ := hnorm y (ball_subset_closedBall hy)
    have hy0 : 0 ≤ ‖y‖ ^ d := zpow_nonneg (norm_nonneg _) _
    calc |u y| ≤ C * ‖y‖ ^ d := hbound y (hball (ball_subset_closedBall hy))
      _ ≤ |C| * ‖y‖ ^ d := mul_le_mul_of_nonneg_right (le_abs_self C) hy0
      _ ≤ |C| * (2 ^ d.natAbs * ‖x‖ ^ d) :=
          mul_le_mul_of_nonneg_left (zpow_le_two_pow_natAbs_mul hxpos h1 h2 d) (abs_nonneg C)
      _ = |C| * 2 ^ d.natAbs * ‖x‖ ^ d := by ring
  have hvol : volume.real (ball x (‖x‖ / 2)) = unitBallVolume n * (‖x‖ / 2) ^ n := by
    rw [measureReal_def, Measure.addHaar_ball_center]
    exact ballVolume_eq_unitBallVolume_mul_pow n _ hrpos.le
  have hcont : ContinuousOn u (closedBall x (‖x‖ / 2)) :=
    (hu.contDiffOn.mono hball).continuousOn
  have hint : ∫ y in ball x (‖x‖ / 2), |u y| ≤
      |C| * 2 ^ d.natAbs * ‖x‖ ^ d * (unitBallVolume n * (‖x‖ / 2) ^ n) := by
    calc ∫ y in ball x (‖x‖ / 2), |u y|
        ≤ ∫ _ in ball x (‖x‖ / 2), |C| * 2 ^ d.natAbs * ‖x‖ ^ d :=
          setIntegral_mono_on
            ((hcont.integrableOn_compact (isCompact_closedBall x _)).mono_set
              ball_subset_closedBall).abs
            (integrableOn_const (measure_ball_lt_top (μ := volume)).ne) measurableSet_ball hpt
      _ = |C| * 2 ^ d.natAbs * ‖x‖ ^ d * (unitBallVolume n * (‖x‖ / 2) ^ n) := by
          rw [setIntegral_const, hvol, smul_eq_mul, mul_comm]
  calc ‖iteratedFDeriv ℝ k u x‖
      ≤ interiorDerivativeConstant n k / (‖x‖ / 2) ^ (n + k) *
          ∫ y in ball x (‖x‖ / 2), |u y| := hest
    _ ≤ interiorDerivativeConstant n k / (‖x‖ / 2) ^ (n + k) *
          (|C| * 2 ^ d.natAbs * ‖x‖ ^ d * (unitBallVolume n * (‖x‖ / 2) ^ n)) :=
        mul_le_mul_of_nonneg_left hint (div_nonneg hc (pow_nonneg hrpos.le _))
    _ = interiorDerivativeConstant n k * unitBallVolume n * (|C| * 2 ^ d.natAbs) * 2 ^ k *
          ‖x‖ ^ (d - k) := by
        rw [zpow_sub₀ hxpos.ne', zpow_natCast, pow_add]
        simp only [div_pow]
        field_simp

end LaplacianEquation
