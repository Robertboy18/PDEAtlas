/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered

/-!
# One-component fluxes

A flux on `ℝ^1` whose Jacobian at `q` is multiplication by a scalar `s` is
strictly hyperbolic at `q`, and its only canonical characteristic speed is `s`.
The standard basis vector is the eigenbasis, and a one-element speed list is
trivially strictly increasing. The scalar, Burgers, cubic and exponential flux
examples all use these two facts.
-/

@[expose] public section

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.OneComponent

open PDE.Common PDE.Hyperbolic.ConservationLaw.System

private theorem strictMono_const (s : ℝ) : StrictMono (fun _ : Fin 1 ↦ s) := by
  intro i j hij
  exact (not_lt_of_ge (Subsingleton.elim j i).le hij).elim

/-- A one-component flux with scalar Jacobian `s` is strictly hyperbolic. -/
theorem isStrictlyHyperbolicAt_of_fderiv_eq_smul
    {flux : ℝ^1 → ℝ^1} {q : ℝ^1} {s : ℝ}
    (hdiff : DifferentiableAt ℝ flux q) (hD : ∀ v, fderiv ℝ flux q v = s • v) :
    IsStrictlyHyperbolicAt flux q :=
  ⟨hdiff, (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis, fun _ ↦ s,
    (strictMono_const s).injective, fun k ↦
      ⟨Module.End.mem_eigenspace_iff.mpr (hD _),
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.ne_zero k⟩⟩

/-- The canonical characteristic speed of a one-component flux with scalar
Jacobian `s` is `s`. -/
theorem characteristicSpeed_eq_of_fderiv_eq_smul
    {flux : ℝ^1 → ℝ^1} {q : ℝ^1} {s : ℝ}
    (hD : ∀ v, fderiv ℝ flux q v = s • v)
    (k : Fin 1) :
    characteristicSpeed flux k q = s :=
  congrFun (characteristicSpeed_eq_of_eigenbasis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis (strictMono_const s)
    (fun _ ↦ hD _)) k

end PDE.Examples.Hyperbolic.ConservationLaw.System.OneComponent
