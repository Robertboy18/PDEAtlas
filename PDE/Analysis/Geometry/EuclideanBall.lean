/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import CAS.ExactTactic

/-!
# Euclidean ball and sphere measures

The real-valued volume of a Euclidean ball and the surface area induced by
`Measure.toSphere`. The unit ball in `ℝ^n` has volume
`unitBallVolume n = π^(n/2) / Γ(n/2 + 1)`, which is Evans's `α(n)`, and the normalization

`unitSphereArea n = n * unitBallVolume n`

is the normalization of the sphere measure in polar coordinates; it is Evans's `nα(n)`. Both
constants enter, for instance, the fundamental solution of Laplace's equation.

## Main results

* `ballVolume_eq_unitBallVolume_mul_pow`: a ball of radius `r ≥ 0` has volume
  `unitBallVolume n * r ^ n`, from Mathlib's `EuclideanSpace.volume_ball`.
* `unitSphereArea_eq`: the unit sphere has area `n * unitBallVolume n`, from Mathlib's
  `Measure.toSphere_real_apply_univ`.
* `unitBallVolume_one` to `unitBallVolume_five` and `unitSphereArea_two` to
  `unitSphereArea_four`: the values in low dimensions.

## Implementation notes

`sphereArea n r = |r| ^ (n - 1) * unitSphereArea n` is the radial factor of polar coordinates.
`unitSphereArea_two` is proved by the `cas` tactic of SymLean.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix A.2, (xiii), p. 699, and §2.2.1, the
  fundamental solution (6), p. 22. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE.Analysis

/-- The volume of the unit ball in `ℝ^n`. -/
def unitBallVolume (n : ℕ) : ℝ :=
  (√Real.pi) ^ n / Real.Gamma ((n : ℝ) / 2 + 1)

/-- The unit ball has strictly positive volume in every dimension. -/
theorem unitBallVolume_pos (n : ℕ) :
    0 < unitBallVolume n := by
  unfold unitBallVolume
  apply div_pos
  · exact pow_pos (Real.sqrt_pos.2 Real.pi_pos) n
  · apply Real.Gamma_pos_of_pos
    positivity

/-- The one-dimensional unit ball has length two. -/
theorem unitBallVolume_one :
    unitBallVolume 1 = 2 := by
  rw [unitBallVolume]
  norm_num only [Nat.cast_one, pow_one]
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num]
  rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  have hsqrt : √Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp [hsqrt]

/-- The planar unit ball has area `π`. -/
theorem unitBallVolume_two :
    unitBallVolume 2 = Real.pi := by
  rw [unitBallVolume]
  norm_num [Real.Gamma_nat_eq_factorial, Real.sq_sqrt Real.pi_nonneg]

/-- The half-integer Gamma value `Γ(3/2) = √π / 2`. -/
theorem Gamma_three_div_two : Real.Gamma (3 / 2) = √Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  ring

/-- The half-integer Gamma value `Γ(5/2) = 3√π / 4`. -/
theorem Gamma_five_div_two : Real.Gamma (5 / 2) = 3 * √Real.pi / 4 := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0), Gamma_three_div_two]
  ring

/-- The half-integer Gamma value `Γ(7/2) = 15√π / 8`. -/
theorem Gamma_seven_div_two : Real.Gamma (7 / 2) = 15 * √Real.pi / 8 := by
  rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (5 / 2 : ℝ) ≠ 0), Gamma_five_div_two]
  ring

/-- The three-dimensional unit ball has volume `4π / 3`. -/
theorem unitBallVolume_three : unitBallVolume 3 = 4 * Real.pi / 3 := by
  have hsqrt : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [unitBallVolume, show ((3 : ℕ) : ℝ) / 2 + 1 = 5 / 2 by norm_num, Gamma_five_div_two,
    pow_succ, Real.sq_sqrt Real.pi_nonneg]
  field_simp

/-- The four-dimensional unit ball has volume `π² / 2`. -/
theorem unitBallVolume_four : unitBallVolume 4 = Real.pi ^ 2 / 2 := by
  rw [unitBallVolume, show ((4 : ℕ) : ℝ) / 2 + 1 = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial, show √Real.pi ^ 4 = (√Real.pi ^ 2) ^ 2 by ring,
    Real.sq_sqrt Real.pi_nonneg]
  norm_num [Nat.factorial]

/-- The five-dimensional unit ball has volume `8π² / 15`. -/
theorem unitBallVolume_five : unitBallVolume 5 = 8 * Real.pi ^ 2 / 15 := by
  have hsqrt : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [unitBallVolume, show ((5 : ℕ) : ℝ) / 2 + 1 = 7 / 2 by norm_num, Gamma_seven_div_two,
    show √Real.pi ^ 5 = (√Real.pi ^ 2) ^ 2 * √Real.pi by ring,
    Real.sq_sqrt Real.pi_nonneg]
  field_simp

/-- The real-valued volume of the open ball of radius `r` in `ℝ^n`. -/
def ballVolume (n : ℕ) (r : ℝ) : ℝ :=
  (volume (Metric.ball (0 : ℝ^n) r)).toReal

/-- A nonnegative-radius ball has volume `unitBallVolume n * r ^ n`. -/
theorem ballVolume_eq_unitBallVolume_mul_pow
    (n : ℕ) [Fact (0 < n)] (r : ℝ) (hr : 0 ≤ r) :
    ballVolume n r = unitBallVolume n * r ^ n := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hunitBallVolume : 0 ≤ unitBallVolume n :=
    (unitBallVolume_pos n).le
  have hvolume :
      volume (Metric.ball (0 : ℝ^n) r) =
        ENNReal.ofReal r ^ n * ENNReal.ofReal (unitBallVolume n) := by
    simpa [unitBallVolume] using
      (EuclideanSpace.volume_ball (Fin n) (0 : ℝ^n) r)
  rw [ballVolume, hvolume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal hunitBallVolume, mul_comm]

/-- The real-valued area of the unit sphere in `ℝ^n`. -/
def unitSphereArea (n : ℕ) : ℝ :=
  ((volume : Measure (ℝ^n)).toSphere Set.univ).toReal

/-- The unit sphere has area `n` times the volume of the unit ball. -/
theorem unitSphereArea_eq (n : ℕ) [Fact (0 < n)] :
    unitSphereArea n = (n : ℝ) * unitBallVolume n := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  rw [unitSphereArea]
  change (volume : Measure (ℝ^n)).toSphere.real Set.univ =
    (n : ℝ) * unitBallVolume n
  rw [Measure.toSphere_real_apply_univ]
  have hvol :
      (volume : Measure (ℝ^n)).real (Metric.ball (0 : ℝ^n) 1) =
        unitBallVolume n := by
    simpa [ballVolume, MeasureTheory.measureReal_def] using
      (ballVolume_eq_unitBallVolume_mul_pow n 1 zero_le_one)
  simp [hvol]

/-- The unit circle has length `2π`. -/
theorem unitSphereArea_two : unitSphereArea 2 = 2 * Real.pi := by
  cas

/-- The unit sphere in `ℝ^3` has area `4π`. -/
theorem unitSphereArea_three : unitSphereArea 3 = 4 * Real.pi := by
  have : Fact (0 < 3) := ⟨by norm_num⟩
  rw [unitSphereArea_eq, unitBallVolume_three]
  ring

/-- The unit sphere in `ℝ^4` has area `2π²`. -/
theorem unitSphereArea_four : unitSphereArea 4 = 2 * Real.pi ^ 2 := by
  have : Fact (0 < 4) := ⟨by norm_num⟩
  rw [unitSphereArea_eq, unitBallVolume_four]
  ring

/-- The radial surface-Jacobian factor at signed radius `r` in `ℝ^n`.
For positive `r`, this is the area of the Euclidean sphere of radius `r`. -/
def sphereArea (n : ℕ) (r : ℝ) : ℝ :=
  |r| ^ (n - 1) * unitSphereArea n

/-- A positive-radius Euclidean ball has nonzero volume. -/
theorem ballVolume_ne_zero {n : ℕ} [Fact (0 < n)] (r : ℝ) (hr : 0 < r) :
    ballVolume n r ≠ 0 := by
  rw [ballVolume_eq_unitBallVolume_mul_pow n r hr.le]
  exact mul_ne_zero
    (ne_of_gt (unitBallVolume_pos n))
    (pow_ne_zero n hr.ne')

/-- The unit sphere has strictly positive area in every positive dimension. -/
theorem unitSphereArea_pos {n : ℕ} [Fact (0 < n)] :
    0 < unitSphereArea n := by
  rw [unitSphereArea_eq]
  exact mul_pos (by exact_mod_cast (Fact.out : 0 < n))
    (unitBallVolume_pos n)

/-- A positive-radius Euclidean sphere has nonzero area. -/
theorem sphereArea_ne_zero {n : ℕ} [Fact (0 < n)] (r : ℝ) (hr : 0 < r) :
    sphereArea n r ≠ 0 := by
  exact ne_of_gt <| by
    rw [sphereArea]
    exact mul_pos (pow_pos (abs_pos.mpr hr.ne') _) unitSphereArea_pos

/-- A positive-radius Euclidean sphere has strictly positive area. -/
theorem sphereArea_pos {n : ℕ} [Fact (0 < n)] (r : ℝ) (hr : 0 < r) :
    0 < sphereArea n r := by
  rw [sphereArea]
  exact mul_pos (pow_pos (abs_pos.mpr hr.ne') _) unitSphereArea_pos

end PDE.Analysis
