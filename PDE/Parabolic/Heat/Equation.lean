/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Problem.Equation.Satisfaction
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Heat equation operators and domain equations

The heat operator `u ↦ uₜ - Δₓu` on Euclidean spacetime `ℝ^(n+1)`, with coordinate `0` playing
the role of time and the remaining `n` coordinates the role of space, together with the bundled
homogeneous equation `uₜ - Δu = 0` and forced equation `uₜ - Δu = f` on an arbitrary spacetime
set `U`. Both equations are `PDEProblem`s with a single interior equation and no side
conditions. Initial-value conditions are added in
`PDE.Parabolic.Heat.InitialValueProblem`.

The derivatives are the total Fréchet-derivative operators of `PDE.FDeriv`: `(∂[0] u) p`
is `fderiv ℝ u p` applied to the time basis vector and `laplacian` is the sum of the pure second
coordinate derivatives of the spatial slice `x ↦ u(p 0, x)`. Because `fderiv` is defined
everywhere, `heatOperator u` makes sense for any `u`, and satisfying the bundled equation means
only that the residual vanishes pointwise on `U`. Regularity is a hypothesis of the theorems
that need it. For instance `heatEquation_add` asks for `DifferentiableAt ℝ u x` and
`ContDiffAt ℝ 2` of the spatial slice at each `x ∈ U`, while `heatEquation_const_mul` asks for
nothing (see the implementation notes).

## Main results

* `heatOperator`, `heatEquation`, `nonhomogeneousHeatEquation`: the operator and the two
  bundled equations.
* `heatEquation_iff`, `nonhomogeneousHeatEquation_iff`: satisfying the bundled problem is the
  same as the pointwise residual identity on `U`.
* `heatOperator_add`, `heatOperator_const_mul`: linearity of the operator, the first under the
  differentiability needed for the sum rules of `fderiv` and `laplacian`.
* `nonhomogeneousHeatEquation_add`, `nonhomogeneousHeatEquation_const_mul`,
  `nonhomogeneousHeatEquation_sub`, `nonhomogeneousHeatEquation_linear_combination`:
  superposition for the forced equation, with forcings combining the same way.
* `heatEquation_add`, `heatEquation_const_mul`, `heatEquation_sub`,
  `heatEquation_linear_combination`: the same statements for the homogeneous equation, which
  is the forced one with `f = 0`.
* `heatEquation_const`: constants solve the homogeneous equation on any domain.

## Implementation notes

Scalar multiplication commutes with `fderiv` without any hypothesis, so
`heatOperator_const_mul` and the `_const_mul` superposition lemmas need no regularity. Sums
do not: `fderiv (u + v)` is `fderiv u + fderiv v` only where both are differentiable, so the
additive lemmas carry a spacetime differentiability hypothesis for the time derivative and a
`ContDiffAt ℝ 2` hypothesis on the spatial slices for the Laplacian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3, equations (1) and (2).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian PDEEquation PDEProblem SatisfiesPDEProblem)

namespace HeatEquation

/-- The heat operator `uₜ - Δu` with separate space and time arguments.
`heatParabolicOperator_eq_heatOperator` relates it to the spacetime residual. -/
noncomputable def heatParabolicOperator {n : ℕ}
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) : ℝ :=
  deriv (u x) t - laplacian (fun y ↦ u y t) x


open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-- The classical heat operator `uₜ - Δₓu` on Euclidean spacetime.

Coordinate `0` is time and the remaining coordinates are space. The homogeneous, forced, and
initial-value problems in this directory all use this residual. It is defined for every `u`. -/
noncomputable def heatOperator
    (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  (∂[0] u) p -
    laplacian (fun x ↦ u (timeSpaceCons (n := n) (p 0) x)) (spatialPartCLM n p)

/-- The separate-variable and spacetime heat operators agree at a point of joint
differentiability. No second-order regularity is needed, since both operators take the
Laplacian of the same spatial slice. -/
theorem heatParabolicOperator_eq_heatOperator
    (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t : ℝ)
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    heatParabolicOperator (fun y s ↦ u (timeSpaceCons s y)) x t =
      heatOperator u (timeSpaceCons t x) := by
  simp only [heatParabolicOperator, heatOperator,
    PDE.partialDeriv_timeSpaceCons_eq_deriv u x t hu,
    timeSpaceCons_zero, spatialPartCLM_timeSpaceCons]

/-- The spacetime heat operator preserves sums at points where the derivative rules apply. -/
theorem heatOperator_add
    {u v : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hdu : DifferentiableAt ℝ u p) (hdv : DifferentiableAt ℝ v p)
    (hspaceu : ContDiffAt ℝ 2
      (fun x ↦ u (timeSpaceCons (n := n) (p 0) x)) (spatialPartCLM n p))
    (hspacev : ContDiffAt ℝ 2
      (fun x ↦ v (timeSpaceCons (n := n) (p 0) x)) (spatialPartCLM n p)) :
    heatOperator (n := n) (fun q ↦ u q + v q) p =
      heatOperator (n := n) u p + heatOperator (n := n) v p := by
  rw [heatOperator, heatOperator, heatOperator]
  rw [PDE.partialDeriv_add hdu hdv]
  rw [PDE.laplacian_add
    (fun x ↦ u (timeSpaceCons (n := n) (p 0) x))
    (fun x ↦ v (timeSpaceCons (n := n) (p 0) x))
    (spatialPartCLM n p) hspaceu hspacev]
  ring

/-- The spacetime heat operator commutes with multiplication by a real constant. -/
theorem heatOperator_const_mul
    (c : ℝ) {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)} :
    heatOperator (n := n) (fun q ↦ c * u q) p = c * heatOperator (n := n) u p := by
  have htime :
      (∂[0] (fun q ↦ c * u q)) p =
        c * (∂[0] u) p := by
    simpa [smul_eq_mul] using
      (PDE.partialDeriv_const_smul (n := n + 1) (E := ℝ) c
        (i := (0 : Fin (n + 1))) (f := u) (x := p))
  have hspace :
      laplacian (fun x ↦ c * u (timeSpaceCons (n := n) (p 0) x))
          (spatialPartCLM n p) =
        c * laplacian (fun x ↦ u (timeSpaceCons (n := n) (p 0) x))
          (spatialPartCLM n p) :=
    PDE.laplacian_const_smul (n := n) c
      (fun x ↦ u (timeSpaceCons (n := n) (p 0) x))
      (spatialPartCLM n p)
  rw [heatOperator, heatOperator, htime, hspace]
  ring

/-- The forced heat equation `u_t - Δu = f` on `U`, as a `PDEProblem`. It records only the
pointwise residual equation, with no regularity of `u`. -/
noncomputable def nonhomogeneousHeatEquation
    (U : Set (ℝ^(n + 1)))
    (f : ℝ^(n + 1) → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  { eqns := [
      { Output := ℝ
        operator := heatOperator (n := n)
        rhs := f
        domain := U
      }
    ],
    sideConditions := []
  }

/-- Projection from the bundled nonhomogeneous heat equation to the pointwise residual
`u_t - Δu = f` on `U`. -/
theorem nonhomogeneousHeatEquation.residual_eq
    {U : Set (ℝ^(n + 1))}
    {f u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u)
    {x : ℝ^(n + 1)} (hx : x ∈ U) :
    heatOperator (n := n) u x = f x := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := heatOperator (n := n)
      rhs := f
      domain := U }
  have heqn : eqn ∈ (nonhomogeneousHeatEquation (n := n) U f).eqns := by
    simp [eqn, nonhomogeneousHeatEquation]
  have h :=
    PDE.SatisfiesPDEProblem.eqn
      (pde := nonhomogeneousHeatEquation (n := n) U f) (u := u)
      hu heqn hx
  simpa [eqn] using h

/-- Constructor for the bundled nonhomogeneous heat equation from the pointwise residual. -/
theorem nonhomogeneousHeatEquation.of_residual
    {U : Set (ℝ^(n + 1))}
    {f u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x ∈ U, heatOperator (n := n) u x = f x) :
    SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u := by
  refine PDE.SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn x hx
    simp only [nonhomogeneousHeatEquation, List.mem_singleton] at heqn
    subst heqn
    simpa using hres x hx
  · intro eqn heqn
    simp [nonhomogeneousHeatEquation] at heqn

/-- The bundled nonhomogeneous heat equation is exactly its pointwise residual equation on `U`. -/
theorem nonhomogeneousHeatEquation_iff
    {U : Set (ℝ^(n + 1))}
    {f u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u ↔
      ∀ x ∈ U, heatOperator (n := n) u x = f x := by
  constructor
  · intro hu x hx
    exact nonhomogeneousHeatEquation.residual_eq (n := n) hu hx
  · intro hres
    exact nonhomogeneousHeatEquation.of_residual (n := n) hres

/--
Linearity/superposition for the nonhomogeneous heat equation.

If `u` solves `uₜ - Δu = f` and `v` solves `vₜ - Δv = g`, then `u + v` solves
the equation with forcing `f + g`. The differentiability hypotheses on `U` are what the
sum rules for `fderiv` and `laplacian` need.
-/
theorem nonhomogeneousHeatEquation_add
    {U : Set (ℝ^(n + 1))}
    {f g u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U g) v)
    (hdu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (hspaceu : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U (fun x ↦ f x + g x))
      (fun x ↦ u x + v x) := by
  refine nonhomogeneousHeatEquation.of_residual (n := n) ?_
  intro x hx
  calc
    heatOperator (n := n) (fun y ↦ u y + v y) x =
        heatOperator (n := n) u x + heatOperator (n := n) v x :=
      heatOperator_add (n := n) (hdu x hx) (hdv x hx)
        (hspaceu x hx) (hspacev x hx)
    _ = f x + g x := by
      rw [nonhomogeneousHeatEquation.residual_eq (n := n) hu hx,
        nonhomogeneousHeatEquation.residual_eq (n := n) hv hx]

/--
Scalar multiplication for the nonhomogeneous heat equation.

If `uₜ - Δu = f`, then `(c u)ₜ - Δ(c u) = c f`. No regularity is needed.
-/
theorem nonhomogeneousHeatEquation_const_mul
    {U : Set (ℝ^(n + 1))}
    (c : ℝ)
    {f u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u) :
    SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U (fun x ↦ c * f x))
      (fun x ↦ c * u x) := by
  refine nonhomogeneousHeatEquation.of_residual (n := n) ?_
  intro x hx
  calc
      heatOperator (n := n) (fun y ↦ c * u y) x =
        c * heatOperator (n := n) u x :=
      heatOperator_const_mul (n := n) c
    _ = c * f x := by
      rw [nonhomogeneousHeatEquation.residual_eq (n := n) hu hx]

/--
Subtraction for the nonhomogeneous heat equation.

If `uₜ - Δu = f` and `vₜ - Δv = g`, then `(u-v)ₜ - Δ(u-v) = f-g`.
-/
theorem nonhomogeneousHeatEquation_sub
    {U : Set (ℝ^(n + 1))}
    {f g u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U g) v)
    (hdu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (hspaceu : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U (fun x ↦ f x - g x))
      (fun x ↦ u x - v x) := by
  have hnegv :
      SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U (fun x ↦ (-1 : ℝ) * g x))
        (fun x ↦ (-1 : ℝ) * v x) :=
    nonhomogeneousHeatEquation_const_mul (n := n) (U := U) (-1) hv
  have hadd := nonhomogeneousHeatEquation_add (n := n) (U := U) hu hnegv hdu
    (fun x hx ↦ (hdv x hx).const_mul (-1)) hspaceu
    (fun x hx ↦ contDiffAt_const.mul (hspacev x hx))
  simpa [sub_eq_add_neg] using hadd

/--
Linear combinations for the nonhomogeneous heat equation.

Solutions for forcings `f` and `g` combine to a solution for `a f + b g` (Evans's linearity
principle).
-/
theorem nonhomogeneousHeatEquation_linear_combination
    {U : Set (ℝ^(n + 1))}
    (a b : ℝ)
    {f g u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousHeatEquation (n := n) U g) v)
    (hdu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (hspaceu : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem
      (nonhomogeneousHeatEquation (n := n) U (fun x ↦ a * f x + b * g x))
      (fun x ↦ a * u x + b * v x) := by
  have hau := nonhomogeneousHeatEquation_const_mul (n := n) (U := U) a hu
  have hbv := nonhomogeneousHeatEquation_const_mul (n := n) (U := U) b hv
  exact nonhomogeneousHeatEquation_add (n := n) (U := U) hau hbv
    (fun x hx ↦ (hdu x hx).const_mul a)
    (fun x hx ↦ (hdv x hx).const_mul b)
    (fun x hx ↦ contDiffAt_const.mul (hspaceu x hx))
    (fun x hx ↦ contDiffAt_const.mul (hspacev x hx))

/-- The homogeneous heat equation `u_t - Δu = 0` on the spacetime domain `U`, as a
`PDEProblem`: the forced equation with zero forcing. -/
noncomputable def heatEquation (U : Set (ℝ^(n + 1))) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  nonhomogeneousHeatEquation (n := n) U fun _ ↦ 0

/-- Projection from the bundled homogeneous heat equation to the pointwise residual
`u_t - Δu = 0` on `U`. -/
theorem heatEquation.residual_eq
    {U : Set (ℝ^(n + 1))}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatEquation (n := n) U) u)
    {x : ℝ^(n + 1)} (hx : x ∈ U) :
    heatOperator (n := n) u x = 0 :=
  nonhomogeneousHeatEquation.residual_eq (n := n) hu hx

/-- Constructor for the bundled homogeneous heat equation from the pointwise residual. -/
theorem heatEquation.of_residual
    {U : Set (ℝ^(n + 1))}
    {u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x ∈ U, heatOperator (n := n) u x = 0) :
    SatisfiesPDEProblem (heatEquation (n := n) U) u :=
  nonhomogeneousHeatEquation.of_residual (n := n) hres

/-- The bundled homogeneous heat equation is exactly its pointwise residual equation on `U`. -/
theorem heatEquation_iff
    {U : Set (ℝ^(n + 1))}
    {u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (heatEquation (n := n) U) u ↔
      ∀ x ∈ U, heatOperator (n := n) u x = 0 :=
  nonhomogeneousHeatEquation_iff (n := n)

/-- Constant spacetime functions solve the homogeneous heat equation on every domain. -/
theorem heatEquation_const
    (U : Set (ℝ^(n + 1))) (c : ℝ) :
    SatisfiesPDEProblem (heatEquation (n := n) U)
      (fun _ : ℝ^(n + 1) ↦ c) := by
  refine heatEquation.of_residual (n := n) ?_
  intro x _hx
  simp [heatOperator, PDE.partialDeriv_const, PDE.laplacian_const]

/--
Linearity/superposition for the homogeneous heat equation.

Sums of solutions of `uₜ - Δu = 0` are solutions, given the differentiability needed for the
sum rules (Evans's linearity principle).
-/
theorem heatEquation_add
    {U : Set (ℝ^(n + 1))}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatEquation (n := n) U) u)
    (hv : SatisfiesPDEProblem (heatEquation (n := n) U) v)
    (hdu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (hspaceu : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem (heatEquation (n := n) U) (fun x ↦ u x + v x) := by
  simpa only [heatEquation, add_zero] using
    nonhomogeneousHeatEquation_add (n := n) hu hv hdu hdv hspaceu hspacev

/--
Scalar multiplication for the homogeneous heat equation.

If `uₜ - Δu = 0`, then `(c u)ₜ - Δ(c u) = 0`.
-/
theorem heatEquation_const_mul
    {U : Set (ℝ^(n + 1))}
    (c : ℝ)
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatEquation (n := n) U) u) :
    SatisfiesPDEProblem (heatEquation (n := n) U) (fun x ↦ c * u x) := by
  simpa only [heatEquation, mul_zero] using nonhomogeneousHeatEquation_const_mul (n := n) c hu

/-- The difference of two sufficiently regular homogeneous heat solutions is again a solution. -/
theorem heatEquation_sub
    {U : Set (ℝ^(n + 1))}
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatEquation (n := n) U) u)
    (hv : SatisfiesPDEProblem (heatEquation (n := n) U) v)
    (hdu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (hspaceu : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem (heatEquation (n := n) U) (fun x ↦ u x - v x) := by
  simpa only [heatEquation, sub_self] using
    nonhomogeneousHeatEquation_sub (n := n) hu hv hdu hdv hspaceu hspacev

/-- Linear combinations of sufficiently regular homogeneous heat solutions are again solutions. -/
theorem heatEquation_linear_combination
    {U : Set (ℝ^(n + 1))}
    (a b : ℝ)
    {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (heatEquation (n := n) U) u)
    (hv : SatisfiesPDEProblem (heatEquation (n := n) U) v)
    (hdu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (hspaceu : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x))
    (hspacev : ∀ x ∈ U,
      ContDiffAt ℝ 2 (fun y ↦ v (timeSpaceCons (n := n) (x 0) y)) (spatialPartCLM n x)) :
    SatisfiesPDEProblem (heatEquation (n := n) U) (fun x ↦ a * u x + b * v x) := by
  simpa only [heatEquation, mul_zero, add_zero] using
    nonhomogeneousHeatEquation_linear_combination (n := n) a b hu hv hdu hdv hspaceu hspacev

end HeatEquation
