/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Defs.Basic
public import PDE.Problem.Equation.Satisfaction

/-!
# Well-posed families of PDE problems

We define Hadamard well-posedness for a family of `PDEProblem`s as a single proposition that
combines existence, uniqueness, and continuous dependence. These are the conditions (i)-(iii) of
the informal definition in Evans, §1.3.1.

The solution type `Sol` is separate from the function type on which the residual equations are
tested. It may carry a Sobolev, Hölder, energy, quotient, or classical topology, and `realize`
interprets its elements as fields. The admissible class may depend on the datum to express
compatibility conditions or datum-dependent domains.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §1.3.1, p. 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Problem

universe uData uSol uE uF

variable {E : Type uE} {F : Type uF}

/-- Hadamard well-posedness of a family `P` in the admissible classes `𝒮`.

The first witness is the solution operator. Its values must be admissible and solve the
corresponding residual problem, it must depend continuously on the data, and all admissible
solutions must be unique in `Sol`. Equality in `Sol` should therefore encode the intended
representative or quotient convention. -/
def WellPosed (Data : Type uData) (Sol : Type uSol)
    [TopologicalSpace Data] [TopologicalSpace Sol]
    (P : Data → PDEProblem E F) (realize : Sol → E → F)
    (𝒮 : Data → Set Sol) : Prop :=
  ∃ solution : Data → Sol,
    Continuous solution ∧
      (∀ d, solution d ∈ 𝒮 d ∧
        SatisfiesPDEProblem (P d) (realize (solution d))) ∧
      ∀ d u v, u ∈ 𝒮 d → v ∈ 𝒮 d →
        SatisfiesPDEProblem (P d) (realize u) →
        SatisfiesPDEProblem (P d) (realize v) → u = v

namespace WellPosed

variable {Data : Type uData} {Sol : Type uSol}
variable [TopologicalSpace Data] [TopologicalSpace Sol]
variable {P : Data → PDEProblem E F} {realize : Sol → E → F}
variable {𝒮 : Data → Set Sol}

/-- A well-posed family has an admissible solution for every datum. -/
theorem exists_solution (h : WellPosed Data Sol P realize 𝒮) (d : Data) :
    ∃ u, u ∈ 𝒮 d ∧ SatisfiesPDEProblem (P d) (realize u) := by
  rcases h with ⟨solution, _, hsolution, _⟩
  exact ⟨solution d, (hsolution d).1, (hsolution d).2⟩

/-- Admissible solutions of a well-posed problem are unique. -/
theorem unique (h : WellPosed Data Sol P realize 𝒮) {d : Data} {u v : Sol}
    (hu_mem : u ∈ 𝒮 d) (hv_mem : v ∈ 𝒮 d)
    (hu : SatisfiesPDEProblem (P d) (realize u))
    (hv : SatisfiesPDEProblem (P d) (realize v)) :
    u = v := by
  rcases h with ⟨_, _, _, hunique⟩
  exact hunique d u v hu_mem hv_mem hu hv

end WellPosed

end PDE.Problem
