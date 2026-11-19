/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Equation
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Heat residuals with assigned initial values

The forced heat equation on `{t > 0}` with an assigned value `u(0, x) = g(x)` on the slice
`{t = 0}`, as a `PDEProblem`, and the homogeneous problem as its case `f = 0`. These are Evans's
problems (18) in §2.3.1(c) and (8) in §2.3.1(b). For each we prove the projections to the two
clauses, the converse constructor, the `iff` characterization, and superposition.

The initial condition is an equation on the slice, not a limit as `t ↓ 0`, and no regularity is
imposed. Convergence from positive time is proved for the heat-kernel solution in
`PDE.Parabolic.Heat.ApproximateIdentity`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), (8), p. 47, and §2.3.1(c), (17)-(18), p. 51.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (PDEEquation PDEProblem SatisfiesPDEProblem)

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-- Forced heat residual with an assigned initial-slice value.

The equation `u_t - Δu = f` holds on `{t > 0}` and `u(0,x) = g(x)` holds on `{t = 0}`. Nothing
links the two: there is no continuity at `t = 0` and no convergence to `g` as `t ↓ 0`. -/
noncomputable def forcedHeatResidualAssignedInitialValueProblem
    (f : ℝ^(n + 1) → ℝ)
    (g : ℝ^n → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  { eqns := [
      { Output := ℝ
        operator := heatOperator (n := n)
        rhs := f
        domain := {x : ℝ^(n + 1) | 0 < x 0}
      }
    ],
    sideConditions := [
      { Output := ℝ
        operator := fun u x ↦ u x
        rhs := fun x ↦ g (spatialPartCLM n x)
        domain := {x : ℝ^(n + 1) | x 0 = 0}
      }
    ]
  }

/-- Projection from the bundled nonhomogeneous heat IVP to the positive-time residual
`u_t - Δu = f`. -/
theorem forcedHeatResidualAssignedInitialValueProblem.residual_eq
    {f : ℝ^(n + 1) → ℝ}
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedHeatResidualAssignedInitialValueProblem (n := n) f g) u)
    {x : ℝ^(n + 1)} (hx : 0 < x 0) :
    heatOperator (n := n) u x = f x := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := heatOperator (n := n)
      rhs := f
      domain := {x : ℝ^(n + 1) | 0 < x 0} }
  have heqn : eqn ∈ (forcedHeatResidualAssignedInitialValueProblem (n := n) f g).eqns := by
    simp [eqn, forcedHeatResidualAssignedInitialValueProblem]
  have h :=
    PDE.SatisfiesPDEProblem.eqn
      (pde := forcedHeatResidualAssignedInitialValueProblem (n := n) f g) (u := u)
      hu heqn hx
  simpa [eqn] using h

/-- Projection from the bundled nonhomogeneous heat IVP to the time-zero initial condition. -/
theorem forcedHeatResidualAssignedInitialValueProblem.initial_eq
    {f : ℝ^(n + 1) → ℝ}
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedHeatResidualAssignedInitialValueProblem (n := n) f g) u)
    {x : ℝ^(n + 1)} (hx : x 0 = 0) :
    u x = g (spatialPartCLM n x) := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ u x
      rhs := fun x ↦ g (spatialPartCLM n x)
      domain := {x : ℝ^(n + 1) | x 0 = 0} }
  have heqn :
      eqn ∈ (forcedHeatResidualAssignedInitialValueProblem (n := n) f g).sideConditions := by
    simp [eqn, forcedHeatResidualAssignedInitialValueProblem]
  have h :=
    PDE.SatisfiesPDEProblem.side_condition
      (pde := forcedHeatResidualAssignedInitialValueProblem (n := n) f g) (u := u)
      hu heqn hx
  simpa [eqn] using h

/-- Constructor for the bundled nonhomogeneous heat IVP from its pointwise residual and
initial-condition clauses. -/
theorem forcedHeatResidualAssignedInitialValueProblem.of_residual_initial
    {f : ℝ^(n + 1) → ℝ}
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x : ℝ^(n + 1), 0 < x 0 →
      heatOperator (n := n) u x = f x)
    (hinit : ∀ x : ℝ^(n + 1), x 0 = 0 → u x = g (spatialPartCLM n x)) :
    SatisfiesPDEProblem (forcedHeatResidualAssignedInitialValueProblem (n := n) f g) u := by
  refine PDE.SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn x hx
    simp only [forcedHeatResidualAssignedInitialValueProblem, List.mem_singleton] at heqn
    subst heqn
    simpa using hres x hx
  · intro eqn heqn x hx
    simp only [forcedHeatResidualAssignedInitialValueProblem, List.mem_singleton] at heqn
    subst heqn
    simpa using hinit x hx

/-- The bundled nonhomogeneous heat IVP is exactly its positive-time residual and time-zero
initial condition. -/
theorem forcedHeatResidualAssignedInitialValueProblem_iff
    {f : ℝ^(n + 1) → ℝ}
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (forcedHeatResidualAssignedInitialValueProblem (n := n) f g) u ↔
      (∀ x : ℝ^(n + 1), 0 < x 0 →
        heatOperator (n := n) u x = f x) ∧
        (∀ x : ℝ^(n + 1), x 0 = 0 →
          u x = g (spatialPartCLM n x)) := by
  constructor
  · intro hu
    exact ⟨fun x hx ↦
      forcedHeatResidualAssignedInitialValueProblem.residual_eq (n := n) hu hx,
      fun x hx ↦ forcedHeatResidualAssignedInitialValueProblem.initial_eq (n := n) hu hx⟩
  · intro h
    exact forcedHeatResidualAssignedInitialValueProblem.of_residual_initial (n := n) h.1 h.2

/--
Superposition for the nonhomogeneous heat Cauchy problem.

If `u_t - Δu = f` with initial data `g₁` and `v_t - Δv = h` with initial data `g₂`, then
`(u + v)_t - Δ(u + v) = f + h` with initial data `g₁ + g₂`. Evans's (17) in §2.3.1(c) is the
case `f = 0`, `g₂ = 0`, with `u` and `v` the solutions of his Theorems 1 and 2.
-/
theorem forcedHeatResidualAssignedInitialValueProblem_add
    {f h : ℝ^(n + 1) → ℝ}
    {g₁ g₂ : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) f g₁) u)
    (hv : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) h g₂) v)
    (hdu : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ u x)
    (hdv : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ v x)
    (hspaceu : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n)
        (fun x ↦ f x + h x) (fun x ↦ g₁ x + g₂ x))
      (fun x ↦ u x + v x) := by
  refine forcedHeatResidualAssignedInitialValueProblem.of_residual_initial (n := n) ?hres ?hinit
  · intro x hx
    calc
      heatOperator (n := n) (fun y ↦ u y + v y) x =
          heatOperator (n := n) u x + heatOperator (n := n) v x :=
        heatOperator_add (n := n) (hdu x hx) (hdv x hx)
          (hspaceu x hx) (hspacev x hx)
      _ = f x + h x := by
        rw [forcedHeatResidualAssignedInitialValueProblem.residual_eq (n := n) hu hx,
          forcedHeatResidualAssignedInitialValueProblem.residual_eq (n := n) hv hx]
  · intro x hx
    have hu_init :=
      forcedHeatResidualAssignedInitialValueProblem.initial_eq (n := n) hu hx
    have hv_init :=
      forcedHeatResidualAssignedInitialValueProblem.initial_eq (n := n) hv hx
    simp [hu_init, hv_init]

/--
Scalar multiplication for the nonhomogeneous heat Cauchy problem.

If `u_t - Δu = f` with initial data `g`, then `(c * u)_t - Δ(c * u) = c * f` with
initial data `c * g`.
-/
theorem forcedHeatResidualAssignedInitialValueProblem_const_mul
    (c : ℝ)
    {f : ℝ^(n + 1) → ℝ}
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) f g) u) :
    SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n)
        (fun x ↦ c * f x) (fun x ↦ c * g x))
      (fun x ↦ c * u x) := by
  refine forcedHeatResidualAssignedInitialValueProblem.of_residual_initial (n := n) ?hres ?hinit
  · intro x hx
    calc
      heatOperator (n := n) (fun y ↦ c * u y) x =
          c * heatOperator (n := n) u x :=
        heatOperator_const_mul (n := n) c
      _ = c * f x := by
        rw [forcedHeatResidualAssignedInitialValueProblem.residual_eq (n := n) hu hx]
  · intro x hx
    have hu_init :=
      forcedHeatResidualAssignedInitialValueProblem.initial_eq (n := n) hu hx
    simp [hu_init]

/-- Subtraction for the nonhomogeneous heat Cauchy problem. -/
theorem forcedHeatResidualAssignedInitialValueProblem_sub
    {f h : ℝ^(n + 1) → ℝ}
    {g₁ g₂ : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) f g₁) u)
    (hv : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) h g₂) v)
    (hdu : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ u x)
    (hdv : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ v x)
    (hspaceu : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n)
        (fun x ↦ f x - h x) (fun x ↦ g₁ x - g₂ x))
      (fun x ↦ u x - v x) := by
  have hnegv :
      SatisfiesPDEProblem
        (forcedHeatResidualAssignedInitialValueProblem (n := n)
          (fun x ↦ (-1 : ℝ) * h x) (fun x ↦ (-1 : ℝ) * g₂ x))
        (fun x ↦ (-1 : ℝ) * v x) :=
    forcedHeatResidualAssignedInitialValueProblem_const_mul (n := n) (-1) hv
  have hadd := forcedHeatResidualAssignedInitialValueProblem_add (n := n) hu hnegv hdu
    (fun x hx ↦ (hdv x hx).const_mul (-1)) hspaceu
    (fun x hx ↦ contDiffAt_const.mul (hspacev x hx))
  simpa [sub_eq_add_neg] using hadd

/-- Linear combinations for the nonhomogeneous heat Cauchy problem. -/
theorem forcedHeatResidualAssignedInitialValueProblem_linear_combination
    (a b : ℝ)
    {f h : ℝ^(n + 1) → ℝ}
    {g₁ g₂ : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) f g₁) u)
    (hv : SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) h g₂) v)
    (hdu : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ u x)
    (hdv : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ v x)
    (hspaceu : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n)
        (fun x ↦ a * f x + b * h x) (fun x ↦ a * g₁ x + b * g₂ x))
      (fun x ↦ a * u x + b * v x) := by
  have hau := forcedHeatResidualAssignedInitialValueProblem_const_mul
    (n := n) a hu
  have hbv := forcedHeatResidualAssignedInitialValueProblem_const_mul
    (n := n) b hv
  exact forcedHeatResidualAssignedInitialValueProblem_add (n := n) hau hbv
    (fun x hx ↦ (hdu x hx).const_mul a)
    (fun x hx ↦ (hdv x hx).const_mul b)
    (fun x hx ↦ contDiffAt_const.mul (hspaceu x hx))
    (fun x hx ↦ contDiffAt_const.mul (hspacev x hx))

/-- Homogeneous heat residual with the assigned initial-slice value `u(0,x)=g(x)`: the forced
problem with `f = 0`. The equation `u_t - Δu = 0` holds on `{t > 0}` and `u = g` holds on
`{t = 0}`. -/
noncomputable def heatResidualAssignedInitialValueProblem (g : ℝ^n → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  forcedHeatResidualAssignedInitialValueProblem (fun _ ↦ 0) g

/-- Projection from the bundled heat IVP to the positive-time residual
`u_t - Δu = 0`. -/
theorem heatResidualAssignedInitialValueProblem.residual_eq
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g) u)
    {x : ℝ^(n + 1)} (hx : 0 < x 0) :
    heatOperator (n := n) u x = 0 :=
  forcedHeatResidualAssignedInitialValueProblem.residual_eq (n := n) hu hx

/-- Projection from the bundled heat IVP to the time-zero initial condition. -/
theorem heatResidualAssignedInitialValueProblem.initial_eq
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g) u)
    {x : ℝ^(n + 1)} (hx : x 0 = 0) :
    u x = g (spatialPartCLM n x) :=
  forcedHeatResidualAssignedInitialValueProblem.initial_eq (n := n) hu hx

/-- Build the bundled heat IVP from its residual and initial-condition clauses. -/
theorem heatResidualAssignedInitialValueProblem.of_residual_initial
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x : ℝ^(n + 1), 0 < x 0 →
      heatOperator (n := n) u x = 0)
    (hinit : ∀ x : ℝ^(n + 1), x 0 = 0 → u x = g (spatialPartCLM n x)) :
    SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g) u :=
  forcedHeatResidualAssignedInitialValueProblem.of_residual_initial (n := n) hres hinit

/-- The bundled homogeneous heat IVP is exactly its positive-time residual and time-zero
initial condition. -/
theorem heatResidualAssignedInitialValueProblem_iff
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g) u ↔
      (∀ x : ℝ^(n + 1), 0 < x 0 →
        heatOperator (n := n) u x = 0) ∧
        (∀ x : ℝ^(n + 1), x 0 = 0 →
          u x = g (spatialPartCLM n x)) :=
  forcedHeatResidualAssignedInitialValueProblem_iff (n := n)

/--
Superposition for the homogeneous heat residual with assigned initial values.

If `u` and `v` solve the problem with initial values `g₁` and `g₂`, then `u + v` solves it with
initial value `g₁ + g₂`. The regularity hypotheses on `{t > 0}` are what the sum rules for the
time derivative and the spatial Laplacian need.
-/
theorem heatResidualAssignedInitialValueProblem_add
    {g₁ g₂ : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g₁) u)
    (hv : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g₂) v)
    (hdu : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ u x)
    (hdv : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ v x)
    (hspaceu : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (heatResidualAssignedInitialValueProblem (n := n) (fun x ↦ g₁ x + g₂ x))
      (fun x ↦ u x + v x) := by
  simpa only [heatResidualAssignedInitialValueProblem, add_zero] using
    forcedHeatResidualAssignedInitialValueProblem_add (n := n) hu hv hdu hdv hspaceu hspacev

/--
Scalar multiplication for the homogeneous heat residual with an assigned initial value.

If `u` solves the problem with initial value `g`, then `c * u` solves it with initial value
`c * g`. No regularity is needed.
-/
theorem heatResidualAssignedInitialValueProblem_const_mul
    (c : ℝ)
    {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g) u) :
    SatisfiesPDEProblem
      (heatResidualAssignedInitialValueProblem (n := n) (fun x ↦ c * g x))
      (fun x ↦ c * u x) := by
  simpa only [heatResidualAssignedInitialValueProblem, mul_zero] using
    forcedHeatResidualAssignedInitialValueProblem_const_mul (n := n) c hu

/-- Subtraction for the homogeneous heat Cauchy problem. -/
theorem heatResidualAssignedInitialValueProblem_sub
    {g₁ g₂ : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g₁) u)
    (hv : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g₂) v)
    (hdu : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ u x)
    (hdv : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ v x)
    (hspaceu : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (heatResidualAssignedInitialValueProblem (n := n) (fun x ↦ g₁ x - g₂ x))
      (fun x ↦ u x - v x) := by
  simpa only [heatResidualAssignedInitialValueProblem, sub_self] using
    forcedHeatResidualAssignedInitialValueProblem_sub (n := n) hu hv hdu hdv hspaceu hspacev

/-- Linear combinations for the homogeneous heat Cauchy problem. -/
theorem heatResidualAssignedInitialValueProblem_linear_combination
    (a b : ℝ)
    {g₁ g₂ : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g₁) u)
    (hv : SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g₂) v)
    (hdu : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ u x)
    (hdv : ∀ x : ℝ^(n + 1), 0 < x 0 → DifferentiableAt ℝ v x)
    (hspaceu : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x : ℝ^(n + 1), 0 < x 0 →
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (heatResidualAssignedInitialValueProblem (n := n) (fun x ↦ a * g₁ x + b * g₂ x))
      (fun x ↦ a * u x + b * v x) := by
  simpa only [heatResidualAssignedInitialValueProblem, mul_zero, add_zero] using
    forcedHeatResidualAssignedInitialValueProblem_linear_combination (n := n) a b
      hu hv hdu hdv hspaceu hspacev

end HeatEquation
