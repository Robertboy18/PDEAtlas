/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Problem.Equation.Satisfaction
public import PDE.FDeriv.Operators

/-!
# The Poisson problem on the unit ball

We state the homogeneous Dirichlet problem, `-Δu = f` in the open unit ball and `u = 0` on the
unit sphere, as a `PDEProblem` (`unitBallDirichletProblem`). The record contains only the
interior and boundary equations; regularity, existence, and uniqueness are separate statements.

The sign and boundary conventions are those of Evans's boundary-value problems (29) in §2.2.4 and
(46) in §2.2.5, in the case `U = B(0, 1)` and `g = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the boundary-value problem (29), p. 34; §2.2.5(a),
  the boundary-value problem (46), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian PDEEquation PDEProblem SatisfiesPDEProblem)

noncomputable section

namespace PoissonEquation

variable {n : ℕ}

/-- The homogeneous Dirichlet problem: `-Δu = f` in the open unit ball and `u = 0` on the unit
sphere. -/
noncomputable def unitBallDirichletProblem (f : ℝ^n → ℝ) :
    PDEProblem (ℝ^n) ℝ :=
  { eqns := [
      { Output := ℝ
        operator := fun u x ↦ -laplacian u x
        rhs := f
        domain := Metric.ball (0 : ℝ^n) 1 }
    ]
    sideConditions := [
      { Output := ℝ
        operator := fun u x ↦ u x
        rhs := fun _ ↦ 0
        domain := Metric.sphere (0 : ℝ^n) 1 }
    ] }

/-- A function satisfying `unitBallDirichletProblem f` satisfies `-Δu = f` in the open unit
ball. -/
theorem unitBallDirichletProblem.interior_eq
    {f u : ℝ^n → ℝ}
    (hu : SatisfiesPDEProblem (unitBallDirichletProblem f) u)
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) 1) :
    -laplacian u x = f x := by
  let eqn : PDEEquation (ℝ^n) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ -laplacian u x
      rhs := f
      domain := Metric.ball (0 : ℝ^n) 1 }
  have heqn : eqn ∈ (unitBallDirichletProblem f).eqns := by
    simp [eqn, unitBallDirichletProblem]
  have h := PDE.SatisfiesPDEProblem.eqn
    (pde := unitBallDirichletProblem f) (u := u) hu heqn hx
  simpa [eqn] using h

/-- A function satisfying `unitBallDirichletProblem f` vanishes on the unit sphere. -/
theorem unitBallDirichletProblem.boundary_eq
    {f u : ℝ^n → ℝ}
    (hu : SatisfiesPDEProblem (unitBallDirichletProblem f) u)
    {x : ℝ^n} (hx : x ∈ Metric.sphere (0 : ℝ^n) 1) :
    u x = 0 := by
  let eqn : PDEEquation (ℝ^n) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ u x
      rhs := fun _ ↦ 0
      domain := Metric.sphere (0 : ℝ^n) 1 }
  have heqn : eqn ∈ (unitBallDirichletProblem f).sideConditions := by
    simp [eqn, unitBallDirichletProblem]
  have h := PDE.SatisfiesPDEProblem.side_condition
    (pde := unitBallDirichletProblem f) (u := u) hu heqn hx
  simpa [eqn] using h

/-- A function with `-Δu = f` in the open unit ball and `u = 0` on the unit sphere satisfies
`unitBallDirichletProblem f`. -/
theorem unitBallDirichletProblem.of_interior_boundary
    {f u : ℝ^n → ℝ}
    (hinterior : ∀ x ∈ Metric.ball (0 : ℝ^n) 1, -laplacian u x = f x)
    (hboundary : ∀ x ∈ Metric.sphere (0 : ℝ^n) 1, u x = 0) :
    SatisfiesPDEProblem (unitBallDirichletProblem f) u := by
  refine PDE.SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn x hx
    simp only [unitBallDirichletProblem, List.mem_singleton] at heqn
    subst eqn
    simpa using hinterior x hx
  · intro eqn heqn x hx
    simp only [unitBallDirichletProblem, List.mem_singleton] at heqn
    subst eqn
    simpa using hboundary x hx

/-- The bundled unit-ball Dirichlet problem is exactly its interior and boundary equations. -/
theorem unitBallDirichletProblem_iff
    {f u : ℝ^n → ℝ} :
    SatisfiesPDEProblem (unitBallDirichletProblem f) u ↔
      (∀ x ∈ Metric.ball (0 : ℝ^n) 1, -laplacian u x = f x) ∧
        (∀ x ∈ Metric.sphere (0 : ℝ^n) 1, u x = 0) := by
  constructor
  · intro hu
    exact ⟨fun _ hx ↦ unitBallDirichletProblem.interior_eq hu hx,
      fun _ hx ↦ unitBallDirichletProblem.boundary_eq hu hx⟩
  · rintro ⟨hinterior, hboundary⟩
    exact unitBallDirichletProblem.of_interior_boundary hinterior hboundary

end PoissonEquation
