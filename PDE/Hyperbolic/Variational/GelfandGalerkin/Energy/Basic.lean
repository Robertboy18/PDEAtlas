/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import PDE.Analysis.Evolution.Core.EnergyIdentity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Pointwise Gelfand Galerkin wave energy

The Evans energy uses the pivot norm of the Galerkin velocity and the
symmetric principal spatial form.  We prove its exact pointwise
derivative and a dimension-independent estimate for forcing, lower-order,
and coefficient-derivative work terms.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 2, equations (20)-(27).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Evans's finite-dimensional wave energy on a Gelfand trial space:

`Eₘ(t) = 1/2 ‖J pₘ(t)‖_H² + 1/2 A(t)(qₘ(t),qₘ(t))`.

Here `J : V ↪ H` is the pivot inclusion and `A` is the symmetric principal
part of the spatial form.  The lower-order form is intentionally absent
from the energy; it appears as a work/error term in the derivative identity.
This is the energy used in Evans, §7.2.2; the mass-inverted coefficient ODE
has a different inherited inner-product energy.
-/
def gelfandWaveEnergy
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (q p : ℝ → S) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖T.inclusion (p t : V)‖ ^ 2 +
    (1 / 2 : ℝ) * A t (q t : V) (q t : V)

/--
Pointwise Evans energy identity for a finite-dimensional Gelfand Galerkin
trajectory.

The full spatial form is split as `A + R`.  Symmetry is required only of the
principal form `A`; `R` contributes the lower-order term
`-R(t)(q(t),p(t))`.  The coefficient derivative contributes
`1/2 Adot(t)(q(t),q(t))`.  Keeping both terms is essential for the
nonautonomous, lower-order equation treated in Evans, §7.2.2.
-/
theorem hasDerivAt_gelfandWaveEnergy (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (A R : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V) {Adot : V →L[ℝ] StrongDual ℝ V}
    {q p : ℝ → S} {d : S} {t : ℝ} (hA : HasDerivAt A Adot t) (hq : HasDerivAt q (p t) t)
    (hp : HasDerivAt p d t)
    (hprojected : ∀ v : S, inner ℝ (T.inclusion (d : V)) (T.inclusion (v : V)) +
      (A t + R t) (q t : V) (v : V) = ell t (v : V))
    (hA_symmetric : ∀ x y : V, A t x y = A t y x) :
    HasDerivAt (gelfandWaveEnergy T S A q p)
      (ell t (p t : V) - R t (q t : V) (p t : V) + (1 / 2 : ℝ) * Adot (q t : V) (q t : V)) t := by
  let J : S →L[ℝ] H := T.inclusion.comp S.subtypeL
  have hqV : HasDerivAt (fun s ↦ (q s : V)) (p t : V) t := by
    simpa only [Function.comp_def] using! S.subtypeL.hasFDerivAt.comp_hasDerivAt t hq
  have hprojectedVelocity := hprojected (p t)
  simp only [add_apply] at hprojectedVelocity
  have hcoefficient : inner ℝ (J d) (J (p t)) + (1 / 2 : ℝ) *
        ((Adot (q t : V) + A t (p t : V)) (q t : V) + A t (q t : V) (p t : V)) =
      ell t (p t : V) - R t (q t : V) (p t : V) + (1 / 2 : ℝ) * Adot (q t : V) (q t : V) := by
    change inner ℝ (T.inclusion (d : V)) (T.inclusion (p t : V)) + (1 / 2 : ℝ) *
        ((Adot (q t : V) + A t (p t : V)) (q t : V) + A t (q t : V) (p t : V)) = _
    rw [add_apply, hA_symmetric (p t : V) (q t : V)]
    linarith
  simpa only [gelfandWaveEnergy, J, Function.comp_apply, hcoefficient] using!
    (PDE.Analysis.Evolution.hasDerivAt_half_norm_sq (J.hasFDerivAt.comp_hasDerivAt t hp)).add
      (((hA.clm_apply hqV).clm_apply hqV).const_mul (1 / 2 : ℝ))

/--
Evans's pointwise estimate for the three wave-energy work terms.

Assume

* `A(q,q) ≥ c ‖q‖²_V`,
* `|R(q,p)| ≤ L_R ‖q‖_V ‖Jp‖_H`, and
* `Adot(q,q) ≤ L_A ‖q‖²_V`,

with `c > 0` and `L_A ≥ 0`.  For pivot forcing
`ell = T.pivotToDual f`, Cauchy-Schwarz and Young's inequality give

`ell(p) - R(q,p) + Adot(q,q)/2`
`  ≤ [2 + (L_R² + L_A)/c] E(q,p) + ‖f‖²_H/2`.

This is the dimension-independent differential inequality used in Evans's
wave-equation Galerkin estimate.  The lower-order form is measured in
`V × H`, because the kinetic energy controls only the pivot norm of the
velocity.
-/
theorem gelfandWaveEnergyWork_le (T : GelfandTriple (V := V) (H := H))
    (A R Adot : V →L[ℝ] StrongDual ℝ V) (q p : V) (f : H) (c LR LA : ℝ) (hc : 0 < c) (hLA : 0 ≤ LA)
    (hcoercive : c * ‖q‖ ^ 2 ≤ A q q) (hRbound : |R q p| ≤ LR * ‖q‖ * ‖T.inclusion p‖)
    (hAdot : Adot q q ≤ LA * ‖q‖ ^ 2) :
    T.pivotToDual f p - R q p + (1 / 2 : ℝ) * Adot q q ≤ (2 + (LR ^ 2 + LA) / c) *
      ((1 / 2 : ℝ) * ‖T.inclusion p‖ ^ 2 + (1 / 2 : ℝ) * A q q) + (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  have hk : 0 ≤ (LR ^ 2 + LA) / c := by positivity
  have hkc : (LR ^ 2 + LA) / c * c = LR ^ 2 + LA := div_mul_cancel₀ _ hc.ne'
  have hA0 : 0 ≤ A q q := (by positivity : 0 ≤ c * ‖q‖ ^ 2).trans hcoercive
  have hf : T.pivotToDual f p ≤ ‖f‖ * ‖T.inclusion p‖ :=
    (le_abs_self _).trans ((abs_real_inner_le_norm f (T.inclusion p)).trans_eq rfl)
  nlinarith [(neg_le_abs (R q p)).trans hRbound, mul_le_mul_of_nonneg_left hcoercive hk,
    congrArg (· * ‖q‖ ^ 2) hkc, sq_nonneg (‖f‖ - ‖T.inclusion p‖),
    sq_nonneg (LR * ‖q‖ - ‖T.inclusion p‖), mul_nonneg hk (sq_nonneg ‖T.inclusion p‖)]

end Hyperbolic.Variational
