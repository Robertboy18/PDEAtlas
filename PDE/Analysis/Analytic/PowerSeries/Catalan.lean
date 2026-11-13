/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Catalan
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Catalan series and formal quadratic roots

Mathlib's Catalan generating series gives the root with zero constant term of
`v = a + b * v²`. The zero constant term selects this branch uniquely.
-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The formal quadratic root selected by its zero constant term. -/
def quadraticRoot (a b : MvPowerSeries σ R) : MvPowerSeries σ R :=
  a * (PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries).subst (b * a)

/-- The selected quadratic root has zero constant term when the source term does. -/
theorem constantCoeff_quadraticRoot (a b : MvPowerSeries σ R)
    (ha : constantCoeff a = 0) : constantCoeff (quadraticRoot a b) = 0 := by
  simp [quadraticRoot, ha]

/-- Substituting in the native Catalan identity solves the formal quadratic equation. -/
theorem quadraticRoot_eq (a b : MvPowerSeries σ R) (ha : constantCoeff a = 0) :
    quadraticRoot a b = a + b * quadraticRoot a b ^ 2 := by
  let c := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
  have hc : c ^ 2 * PowerSeries.X + 1 = c := by
    simpa [c] using congrArg (PowerSeries.map (Nat.castRingHom R))
      PowerSeries.catalanSeries_sq_mul_X_add_one
  have hab : PowerSeries.HasSubst (b * a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [ha])
  let z := PowerSeries.substAlgHom (R := R) hab c
  have hz : z ^ 2 * (b * a) + 1 = z := by
    simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.substAlgHom_X, z] using
      congrArg (PowerSeries.substAlgHom (R := R) hab) hc
  have hv : quadraticRoot a b = a * z := by
    simp only [quadraticRoot, z, PowerSeries.coe_substAlgHom, c]
  rw [hv]
  calc
    a * z = a * (z ^ 2 * (b * a) + 1) := congrArg (a * ·) hz.symm
    _ = a + b * (a * z) ^ 2 := by ring

/-- The formal quadratic equation has at most one root with zero constant term. -/
theorem quadraticRoot_unique (a b u : MvPowerSeries σ R)
    (ha : constantCoeff a = 0) (hu₀ : constantCoeff u = 0)
    (hu : u = a + b * u ^ 2) : u = quadraticRoot a b := by
  let v := quadraticRoot a b
  have hv : v = a + b * v ^ 2 := quadraticRoot_eq a b ha
  have hv₀ : constantCoeff v = 0 := constantCoeff_quadraticRoot a b ha
  have hunit : IsUnit (1 - b * (u + v)) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [hu₀, hv₀]
  apply sub_eq_zero.mp
  apply hunit.mul_left_eq_zero.mp
  calc
    (u - v) * (1 - b * (u + v)) =
        (u - (a + b * u ^ 2)) - (v - (a + b * v ^ 2)) := by ring
    _ = 0 := by rw [← hu, ← hv, sub_self, sub_self, sub_self]

end MvPowerSeries
