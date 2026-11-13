/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.QuadraticEnergy
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Stationarity of quadratic energies along admissible lines

A minimum along a complete affine line forces the linear coefficient of the
energy on that line to vanish. In a constrained problem it suffices that the
chosen direction preserves the constraint.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exact quadratic expansion along an affine line. -/
theorem energy_add_smul
    (B : V →L[ℝ] V →L[ℝ] ℝ) (ell : StrongDual ℝ V)
    (hB : ∀ v w, B v w = B w v) (u v : V) (t : ℝ) :
    energy B ell (u + t • v) =
      energy B ell u + t * (B u v - ell v) + t ^ 2 / 2 * B v v := by
  simp only [energy, map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hB v u]
  ring

/-- Minimization along an admissible line gives the weak equation in its
direction. This is the unconstrained first-variation calculation used after
checking that a direction lies in a linear constraint kernel. -/
theorem stationary_of_energy_minimizes_line
    (B : V →L[ℝ] V →L[ℝ] ℝ) (ell : StrongDual ℝ V)
    (hB : ∀ v w, B v w = B w v) (u v : V)
    (hmin : ∀ t : ℝ, energy B ell u ≤ energy B ell (u + t • v)) :
    B u v = ell v := by
  let q (t : ℝ) := energy B ell u + t * (B u v - ell v) + t ^ 2 / 2 * B v v
  have hq : IsLocalMin q 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [q, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
      energy_add_smul B ell hB u v t] using hmin t
  have hd : HasDerivAt q (B u v - ell v) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (energy B ell u)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (B u v - ell v))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2 |>.mul_const (B v v))
    change HasDerivAt q _ 0 at h
    simpa using h
  exact sub_eq_zero.mp (hq.hasDerivAt_eq_zero hd)

end PDE.Analysis.Variational
