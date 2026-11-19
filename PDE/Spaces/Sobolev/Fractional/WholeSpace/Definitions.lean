/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import PDE.Common.Euclidean

/-!
# Whole-space fractional Sobolev spaces

We use Mathlib's `BesselPotentialSpace` directly. Its notation `H^{s}(ℝ^n)` denotes
complex-valued distributions whose Bessel potential of order `s` belongs to `L²`.
The `toLp` field gives that representative; `toLpₗᵢ` identifies the space isometrically
with `L²`. The norm, inner product, and completeness instances all come from Mathlib.

Mathlib uses the Fourier multiplier `(1 + ‖ξ‖²) ^ (s / 2)`. With its Fourier convention,
this is `(1 - (2π)⁻² Δ) ^ (s / 2)`. Exact comparisons with derivative norms must retain
the factors of `2π`; the integer-order bridge does so explicitly.

The indicator of the unit ball shows that `L²(ℝ^n; ℂ)` and `H^s(ℝ^n)` are nontrivial. The
real subspace, the bounded differential operators, and domain restrictions are in
`Fractional.WholeSpace.Real`, `Fractional.WholeSpace.OperatorBounds` and
`Fractional.Domain.Restriction`.
-/

@[expose] public section

open MeasureTheory
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- The indicator of the unit ball: a concrete nonzero element of `L²(ℝ^n)`. -/
noncomputable def indicatorUnitBall (n : ℕ) : Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  MeasureTheory.indicatorConstLp 2
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : ℝ^n) 1))
    (measure_ball_lt_top (x := (0 : ℝ^n)) (r := 1)).ne (1 : ℂ)

/-- The indicator of the unit ball has positive `L²` norm, namely `vol(B(0,1))^{1/2}`, because
balls in `ℝ^n` have positive finite Lebesgue measure. -/
theorem norm_indicatorUnitBall_pos (n : ℕ) : 0 < ‖indicatorUnitBall n‖ := by
  rw [indicatorUnitBall,
    MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hpos : (0 : ℝ≥0∞) < volume (Metric.ball (0 : ℝ^n) 1) :=
    Metric.measure_ball_pos (volume : Measure (ℝ^n)) (0 : ℝ^n) one_pos
  have hball : (0 : ℝ) < (volume : Measure (ℝ^n)).real (Metric.ball (0 : ℝ^n) 1) := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ball_lt_top (x := (0 : ℝ^n)) (r := 1)).ne
  rw [norm_one, one_mul]
  exact Real.rpow_pos_of_pos hball _

/-- `L²(ℝ^n; ℂ)` is not the zero space, witnessed by the indicator of the unit ball. -/
instance instNontrivialComplexLp (n : ℕ) : Nontrivial (Lp ℂ 2 (volume : Measure (ℝ^n))) :=
  ⟨⟨indicatorUnitBall n, 0, fun h ↦ by
    have := norm_indicatorUnitBall_pos n
    rw [h, norm_zero] at this
    exact absurd this (lt_irrefl 0)⟩⟩

/-- `H^s(ℝ^n; ℂ)` is not the zero space. -/
instance instNontrivialHs : Nontrivial (H^{s}(ℝ^n)) :=
  (BesselPotentialSpace.toLpₗᵢ (ℝ^n) ℂ s 2).toEquiv.nontrivial

end SobolevSpace.Fractional
