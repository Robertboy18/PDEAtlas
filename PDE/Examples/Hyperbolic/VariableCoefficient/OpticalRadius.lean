/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Topology.Instances.Real.Lemmas
import CAS.ExactTactic

/-!
# A bounded optical radius for an unbounded wave speed

The coefficient `a(x) = (1 + x²)²` is smooth and has ellipticity lower bound one.
Its optical radius `q(x) = |arctan x|` solves `a(x) q'(x)² = 1` away from zero,
but the sublevel at `π / 2` is the whole real line (`not_isCompact_radius_sublevel`), so
compactness of optical sublevels does not follow from smoothness, the lower bound and
the eikonal equation. `IncomingWave` uses this radius.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace PDE.Examples.VariableCoefficient.OpticalRadius

/-- A smooth coefficient with an unbounded characteristic speed. -/
def coefficient (x : ℝ) : ℝ := (1 + x ^ 2) ^ 2

/-- The optical radius `|arctan x|`, which stays below `π/2`. -/
def radius (x : ℝ) : ℝ := |Real.arctan x|

/-- The coefficient is smooth. -/
theorem contDiff_coefficient : ContDiff ℝ ∞ coefficient := by
  unfold coefficient
  fun_prop

/-- `1 ≤ a x` for every `x`. -/
theorem one_le_coefficient (x : ℝ) : 1 ≤ coefficient x := by
  dsimp [coefficient]
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

/-- The optical radius is continuous. -/
theorem continuous_radius : Continuous radius := by
  unfold radius
  fun_prop

/-- The origin has optical radius zero. -/
@[simp] theorem radius_zero : radius 0 = 0 := by
  simp [radius]

/-- No other point has optical radius zero. -/
theorem radius_pos {x : ℝ} (hx : x ≠ 0) : 0 < radius x :=
  abs_pos.mpr (mt Real.arctan_eq_zero_iff.mp hx)

/-- The optical radius is smooth away from the origin. -/
theorem contDiffAt_radius {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radius x :=
  Real.contDiff_arctan.contDiffAt.abs (mt Real.arctan_eq_zero_iff.mp hx)

/-- The derivative satisfies the one-dimensional eikonal equation. -/
theorem coefficient_mul_deriv_radius_sq {x : ℝ} (hx : x ≠ 0) :
    coefficient x * deriv radius x ^ 2 = 1 := by
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  rcases hx.lt_or_gt with hx | hx
  · have hd := (hasDerivAt_abs_neg (Real.arctan_lt_zero.mpr hx)).comp x
      (Real.hasDerivAt_arctan x)
    rw [show deriv radius x = -1 * (1 / (1 + x ^ 2)) from hd.deriv]
    dsimp [coefficient]
    cas using hden
  · have hd := (hasDerivAt_abs_pos (Real.arctan_pos.mpr hx)).comp x
      (Real.hasDerivAt_arctan x)
    rw [show deriv radius x = 1 * (1 / (1 + x ^ 2)) from hd.deriv]
    dsimp [coefficient]
    cas using hden

/-- `q x < π/2` for every `x`. -/
theorem radius_lt_pi_div_two (x : ℝ) : radius x < Real.pi / 2 :=
  abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan x, Real.arctan_lt_pi_div_two x⟩

/-- This closed optical sublevel is unbounded. -/
theorem radius_sublevel_eq_univ :
    {x : ℝ | radius x ≤ Real.pi / 2} = Set.univ := by
  ext x
  simp [(radius_lt_pi_div_two x).le]

/-- The sublevel `{q ≤ π/2}` is not compact. -/
theorem not_isCompact_radius_sublevel :
    ¬ IsCompact {x : ℝ | radius x ≤ Real.pi / 2} := by
  rw [radius_sublevel_eq_univ]
  exact noncompact_univ ℝ

end PDE.Examples.VariableCoefficient.OpticalRadius
