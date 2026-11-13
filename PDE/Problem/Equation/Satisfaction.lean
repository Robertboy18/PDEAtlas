/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Set.Operations
public import PDE.Problem.Equation.Basic

/-!
# Satisfaction of residual problems

`SatisfiesPDEProblem` imposes Mathlib's `Set.EqOn` on each stored equation.
Interior equations and side conditions are imposed in the same way; the two
lists are kept apart only so that each can be built and projected separately.
Regularity and trace convergence, if needed, come from the operators and the
solution class.

Compare Evans, §1.1, p. 2: one solves the PDE (1) by finding all `u` verifying (1), possibly
only among functions satisfying auxiliary boundary conditions. Here the side conditions are
equations of the same kind as the interior ones.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §1.1, p. 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

universe uE uF

variable {E : Type uE} {F : Type uF}

namespace PDE

/-- A field satisfies a problem when it satisfies every stored equation. -/
def SatisfiesPDEProblem (pde : PDEProblem E F) (u : E → F) : Prop :=
  ∀ eqn ∈ pde.eqns ++ pde.sideConditions, Set.EqOn (eqn.operator u) eqn.rhs eqn.domain

/-- A field satisfying a problem satisfies each of its interior equations. -/
theorem SatisfiesPDEProblem.eqn
    {pde : PDEProblem E F} {u : E → F}
    (hu : SatisfiesPDEProblem pde u)
    {eqn : PDEEquation E F} (heqn : eqn ∈ pde.eqns)
    {x : E} (hx : x ∈ eqn.domain) :
    eqn.operator u x = eqn.rhs x :=
  hu eqn (List.mem_append_left _ heqn) hx

/-- A field satisfying a problem satisfies each of its side conditions. -/
theorem SatisfiesPDEProblem.side_condition
    {pde : PDEProblem E F} {u : E → F}
    (hu : SatisfiesPDEProblem pde u)
    {eqn : PDEEquation E F} (heqn : eqn ∈ pde.sideConditions)
    {x : E} (hx : x ∈ eqn.domain) :
    eqn.operator u x = eqn.rhs x :=
  hu eqn (List.mem_append_right _ heqn) hx

/-- A field satisfies a problem if it satisfies the interior equations and the side
conditions. -/
theorem SatisfiesPDEProblem.mk
    {pde : PDEProblem E F} {u : E → F}
    (heqns : ∀ eqn ∈ pde.eqns,
      Set.EqOn (eqn.operator u) eqn.rhs eqn.domain)
    (hside : ∀ eqn ∈ pde.sideConditions,
      Set.EqOn (eqn.operator u) eqn.rhs eqn.domain) :
    SatisfiesPDEProblem pde u :=
  List.forall_mem_append.mpr ⟨heqns, hside⟩

/-- Satisfaction splits into the interior equations and designated side conditions. -/
theorem satisfiesPDEProblem_iff_eqns_side_conditions
    {pde : PDEProblem E F} {u : E → F} :
    SatisfiesPDEProblem pde u ↔
      (∀ eqn ∈ pde.eqns,
        Set.EqOn (eqn.operator u) eqn.rhs eqn.domain) ∧
        (∀ eqn ∈ pde.sideConditions,
          Set.EqOn (eqn.operator u) eqn.rhs eqn.domain) :=
  List.forall_mem_append

end PDE
