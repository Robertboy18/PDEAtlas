/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import PDE.Analysis.Geometry.EuclideanBall
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The mass of the sphere measure of polar coordinates

Polar coordinates write the volume of a finite-dimensional real inner product space as a
measure on the unit sphere times a measure on the radius (`MeasureTheory.Measure.toSphere`).
Which number is the mass of the sphere measure? The sphere measure gives the whole sphere `n`
times the volume of the unit ball, `n` the dimension, and for the volume of an inner product
space the unit ball has the volume of the unit ball of `ℝⁿ`. So the mass is the area
`unitSphereArea n = n ω_n` of the unit sphere of `ℝⁿ`, in every nontrivial space of dimension
`n` and not only in `ℝⁿ`. The plane, `MeasureTheory.toSphere_univ_two`, is the case `n = 2`.
The statement is for nontrivial spaces (in dimension zero both sides are zero) and for the
volume; other additive Haar measures differ from it by a constant factor.

## Main results

* `toSphere_univ_eq_ofReal_unitSphereArea`: `volume.toSphere univ = unitSphereArea n`, as an
  element of `[0, ∞]`, for every nontrivial finite-dimensional real inner product space of
  dimension `n`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Module

namespace PDE.Analysis

/-- The area of the unit sphere of a nontrivial finite-dimensional real inner product space, as
the total mass of the sphere measure of polar coordinates:
`volume.toSphere univ = unitSphereArea n`, where `n` is the dimension. -/
theorem toSphere_univ_eq_ofReal_unitSphereArea {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    (volume : Measure E).toSphere univ = ENNReal.ofReal (unitSphereArea (finrank ℝ E)) := by
  have : Fact (0 < finrank ℝ E) := ⟨finrank_pos⟩
  rw [Measure.toSphere_apply_univ, InnerProductSpace.volume_ball, unitSphereArea_eq,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]
  rfl

end PDE.Analysis
