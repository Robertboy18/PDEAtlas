/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Analysis.TrilinearForm
import PDE.Analysis.Evolution.Core.EnergyBarrier
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Galerkin.Gelfand.Energy
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Energy estimates for quadratic Gelfand Galerkin equations

Skew-symmetry of a continuous trilinear form removes its quadratic term when
the projected equation is tested against the Galerkin state. The usual
dimension-independent pivot and coercive estimates therefore pass unchanged
from the linear equation to the quadratic one.

For nondissipative equations, a bound on the combined forcing, linear and
quadratic energy pairing on a pivot-energy ball gives an affine energy envelope.
The strict margin prevents the trajectory from leaving that ball.
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Affine energy envelope on a pivot-energy ball. Suppose
`ℓ(t)(v) - A(t)(v, v) - N(t)(v, v, v) ≤ K` for every `v ∈ S` with `½ ‖ι v‖²_H ≤ R`, and
`½ ‖ι u(a)‖²_H + K (b - a) < R`. Then a solution of the quadratic Galerkin equation satisfies
`½ ‖ι u(t)‖²_H ≤ ½ ‖ι u(a)‖²_H + K (t - a)` on `[a, b]`. Neither coercivity nor skew symmetry
is needed. -/
theorem gelfandGalerkin_quadratic_energy_bound_of_pairing_on_sublevel
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {a b K R : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hpair : ∀ t ∈ Set.Icc a b, ∀ v : S,
      (1 / 2 : ℝ) * ‖T.inclusion (v : V)‖ ^ 2 ≤ R →
        ell t (v : V) - A t (v : V) (v : V) -
          N t (v : V) (v : V) (v : V) ≤ K)
    (heq : ∀ t ∈ Set.Icc a b, ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          A t (u t : V) (v : V) +
          N t (u t : V) (u t : V) (v : V) =
        ell t (v : V))
    (hmargin : (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
      K * (b - a) < R) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 + K * (t - a) := by
  apply le_affine_of_hasDerivWithinAt_le_on_sublevel hab hK
    (g := fun t ↦
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (u t : V)))
  · intro t ht
    exact hasDerivWithinAt_half_norm_sq
      ((T.inclusion.comp S.subtypeL).hasFDerivAt.comp_hasDerivWithinAt t (hu t ht))
  · intro t ht henergy
    linarith [hpair t ht (u t) henergy, heq t ht (u t)]
  · exact hmargin

/--
Pivot-energy estimate for the quadratic Galerkin equation when `N(t)` is skew in its last two
arguments: the trilinear term drops out of the state test, and the linear bound
`½ ‖ι u(t)‖²_H ≤ ½ ‖ι u(a)‖²_H + M² (t - a) / (2C)` follows.
-/
theorem gelfandGalerkin_quadratic_energy_bound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ A t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hskew : ∀ t ∈ Set.Icc a b, (N t).IsSkewInLastTwo)
    (heq : ∀ t ∈ Set.Icc a b, ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          A t (u t : V) (v : V) +
          N t (u t : V) (u t : V) (v : V) =
        ell t (v : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  apply gelfandGalerkin_energy_bound_of_test_state
    T S A hab ell u du hC hM hu hcoercive hell
  intro t ht
  have hself := heq t ht (u t)
  rw [(hskew t ht).energy_eq_zero] at hself
  simpa using hself

/--
Integrated coercive estimate for the quadratic Galerkin equation when `N(t)` is skew in its
last two arguments and `A`, `ℓ` are continuous:
`½ ‖ι u(t)‖²_H + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖ι u(a)‖²_H + M² (t - a) / (2C)`.
-/
theorem gelfandGalerkin_quadratic_integrated_energy_bound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    {a b : ℝ}
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hA_cont : ContinuousOn A (Set.Icc a b))
    (hell_cont : ContinuousOn ell (Set.Icc a b))
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ A t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hskew : ∀ t ∈ Set.Icc a b, (N t).IsSkewInLastTwo)
    (heq : ∀ t ∈ Set.Icc a b, ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          A t (u t : V) (v : V) +
          N t (u t : V) (u t : V) (v : V) =
        ell t (v : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 +
          (C / 2) * ∫ s in a..t, ‖(u s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  apply gelfandGalerkin_integrated_energy_bound_of_test_state
    T S A ell u du hC hM hu hA_cont hell_cont hcoercive hell
  intro t ht
  have hself := heq t ht (u t)
  rw [(hskew t ht).energy_eq_zero] at hself
  simpa using hself

end PDE.Analysis.Evolution
