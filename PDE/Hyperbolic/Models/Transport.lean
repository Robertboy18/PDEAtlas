/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.Gradient.Basic
public import PDE.Problem.Equation.Satisfaction
public import PDE.FDeriv.Operators

/-!
# Transport equation with initial data

Transport equation `uₜ + b · ∇u = f` with initial data. The homogeneous
equation is represented by the zero source rather than a second problem type.

The `PDEProblem` below states the pointwise residual equation and the initial
slice, while differentiability of candidate solutions is supplied in theorems such as
`transportOperator_transportFunction_eq_zero`.

The method of characteristics for constant velocity `b` (Evans, §2.1.1)
says that `u` is constant along the lines `s ↦ (s, x + s b)`, so the
homogeneous problem is solved by Evans's formula (3), `u(t, x) = g(x - t b)`. We define
the operator and the problem and verify that candidate; the forced problem
and uniqueness are in `PDE.Hyperbolic.Models.ForcedTransport`.

## Main definitions and results

* `transportOperator`: the total expression `∂ₜ u + b · ∇ₓ u`, defined as the
  Fréchet derivative in the spacetime direction `(1, b)`.
* `transportIVP`: the residual-and-initial-data `PDEProblem`, with the algebra
  of superposition (`transportIVP_add`, `transportIVP_const_mul`, and so on).
* `transportInner`, `transportFunction`: the characteristic foot `x - t b` and
  the candidate `g(x - t b)`.
* `transportFunction_satisfiesPDEProblem`: the candidate solves the
  homogeneous IVP when `g` is differentiable.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.1.1, equations (1)-(3).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv advectiveDerivative PDEEquation PDEProblem SatisfiesPDEProblem
  spatialGradient)

namespace TransportEquation

open PDE.Common

variable {n : ℕ}

/-- Positive-time domain of the transport equation.

The differential equation is imposed only in the interior `t > 0`; the
assigned initial value is stored separately on `t = 0`. -/
def transportDomain (n : ℕ) : Set (ℝ^(n + 1)) :=
  {x | 0 < x 0}  -- x₀ represents time t

/-- The slice `t = 0` on which the initial trace is imposed. -/
def initialDomain (n : ℕ) : Set (ℝ^(n + 1)) :=
  {x | x 0 = 0}  -- x₀ represents time t

/-- Constant-velocity transport operator `∂ₜ + b · ∇ₓ`.

The codomain is arbitrary, so this single operator applies to scalar densities,
vector-valued unknowns, and systems.  It is expressed as the Fréchet derivative
in the spacetime direction `(1, b)`; `transportOperator_eq` gives the familiar
coordinate formula.  Like `fderiv`, this is a total expression and represents a
classical derivative only under the regularity hypotheses of the surrounding
theorem. -/
noncomputable def transportOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ℝ^n) (u : ℝ^(n + 1) → E) (p : ℝ^(n + 1)) : E :=
  advectiveDerivative (fun _ ↦ PDE.Common.timeSpaceCons 1 b) u p

/-- Coordinate expansion of the constant-velocity transport operator. -/
theorem transportOperator_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ^n)
    (u : ℝ^(n + 1) → E) (p : ℝ^(n + 1)) :
    transportOperator b u p = (∂[0] u) p + ∑ i : Fin n, b i • (∂[i.succ] u) p := by
  rw [transportOperator, advectiveDerivative,
    PDE.fderiv_apply_eq_sum_smul_partialDeriv, Fin.sum_univ_succ]
  simp

/-- Scalar coordinate form `uₜ + b · ∇ₓu` of `transportOperator`. -/
theorem transportOperator_eq_timeDeriv_add_dot_spatialGradient
    (b : ℝ^n) (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) :
    transportOperator b u p = (∂[0] u) p + ∑ i : Fin n, b i * spatialGradient u p i := by
  rw [transportOperator_eq]
  apply congrArg ((∂[0] u) p + ·)
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  simp only [PDE.spatialGradient_apply, smul_eq_mul]

/-- The transport operator preserves addition at points where both summands are differentiable. -/
theorem transportOperator_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ^n)
    {u v : ℝ^(n + 1) → E} {p : ℝ^(n + 1)} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    transportOperator b (fun q ↦ u q + v q) p =
      transportOperator b u p + transportOperator b v p := by
  unfold transportOperator advectiveDerivative
  rw [fderiv_fun_add hu hv]
  simp

/-- The transport operator commutes with constant scalar multiplication at differentiability
points. -/
theorem transportOperator_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (b : ℝ^n) {u : ℝ^(n + 1) → E} {p : ℝ^(n + 1)} (hu : DifferentiableAt ℝ u p) :
    transportOperator b (fun q ↦ c • u q) p = c • transportOperator b u p := by
  unfold transportOperator advectiveDerivative
  rw [fderiv_fun_const_smul hu c]
  simp

/-- The totalized transport operator commutes with pointwise negation. -/
@[simp]
theorem transportOperator_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ^n)
    (u : ℝ^(n + 1) → E) (p : ℝ^(n + 1)) :
    transportOperator b (fun q ↦ -u q) p = -transportOperator b u p := by
  simp [transportOperator, advectiveDerivative]

/-- The transport operator preserves subtraction at points where both terms are differentiable. -/
theorem transportOperator_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ^n)
    {u v : ℝ^(n + 1) → E} {p : ℝ^(n + 1)} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    transportOperator b (fun q ↦ u q - v q) p =
      transportOperator b u p - transportOperator b v p := by
  unfold transportOperator advectiveDerivative
  rw [fderiv_fun_sub hu hv]
  simp

/-- Initial-value problem for the constant-velocity transport equation with source `f`.

This bundles the residual `u_t + b·∇u = f` and the initial condition
`u(0,x)=g(x)`.  Homogeneous transport is the specialization `f = 0`.  The
problem record by itself says nothing about existence, uniqueness, or regularity. -/
noncomputable def transportIVP (b : ℝ^n)
    (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ where
  eqns := [{
    Output := ℝ
    operator := transportOperator b
    rhs := f
    domain := transportDomain n
  }]
  sideConditions := [{
    Output := ℝ
    operator := id
    rhs := g ∘ spatialPartCLM n
    domain := initialDomain n
  }]

/-- Projection from the bundled transport IVP to its residual equation. -/
theorem transportIVP.residual_eq {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP (n := n) b f g) u) {x : ℝ^(n + 1)}
    (hx : x ∈ transportDomain n) :
    transportOperator b u x = f x := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := transportOperator b
      rhs := f
      domain := transportDomain n }
  have heqn : eqn ∈ (transportIVP (n := n) b f g).eqns := by
    simp [eqn, transportIVP]
  have h := PDE.SatisfiesPDEProblem.eqn (pde := transportIVP (n := n) b f g) (u := u) hu heqn hx
  simpa [eqn] using h

/-- Projection from the bundled transport IVP to its assigned initial-value equation. -/
theorem transportIVP.initial_eq {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP (n := n) b f g) u) {x : ℝ^(n + 1)}
    (hx : x ∈ initialDomain n) :
    u x = g (spatialPartCLM n x) := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := id
      rhs := g ∘ spatialPartCLM n
      domain := initialDomain n }
  have heqn : eqn ∈ (transportIVP (n := n) b f g).sideConditions := by
    simp [eqn, transportIVP]
  have h := PDE.SatisfiesPDEProblem.side_condition
      (pde := transportIVP (n := n) b f g) (u := u) hu heqn hx
  simpa [eqn, Function.comp_apply] using h

/-- Constructor for the bundled transport IVP from its residual and assigned
initial-value clauses. -/
theorem transportIVP.of_residual_initial {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x : ℝ^(n + 1), x ∈ transportDomain n → transportOperator b u x = f x)
    (hinit : ∀ x : ℝ^(n + 1), x ∈ initialDomain n → u x = g (spatialPartCLM n x)) :
    SatisfiesPDEProblem (transportIVP (n := n) b f g) u := by
  refine PDE.SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn x hx
    simp only [transportIVP, List.mem_singleton] at heqn
    subst heqn
    simpa using hres x hx
  · intro eqn heqn x hx
    simp only [transportIVP, List.mem_singleton] at heqn
    subst heqn
    simpa [Function.comp_apply] using hinit x hx

/-- The bundled transport IVP is exactly its residual and assigned initial-value clauses. -/
theorem transportIVP_iff {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (transportIVP (n := n) b f g) u ↔ (∀ x : ℝ^(n + 1), x ∈ transportDomain n →
      transportOperator b u x = f x) ∧
      (∀ x : ℝ^(n + 1), x ∈ initialDomain n → u x = g (spatialPartCLM n x)) := by
  constructor
  · exact fun hu ↦ ⟨fun x hx ↦ transportIVP.residual_eq (n := n) hu hx,
      fun x hx ↦ transportIVP.initial_eq (n := n) hu hx⟩
  · exact fun h ↦ transportIVP.of_residual_initial (n := n) h.1 h.2

/-- The zero field satisfies the homogeneous residual and assigned initial value. -/
theorem transportIVP_zero (b : ℝ^n) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun _ : ℝ^(n + 1) ↦ 0) (fun _ : ℝ^n ↦ 0))
      (fun _ : ℝ^(n + 1) ↦ 0) := by
  refine transportIVP.of_residual_initial (n := n) ?_ ?_
  · intro x hx
    simp [transportOperator, advectiveDerivative]
  · intro x hx
    simp

/-- Superposition for the constant-velocity transport IVP.

The velocity field is fixed; the sources, assigned initial values, and residual witnesses add. The
differentiability hypotheses are exactly what is needed to justify differentiating `u + v` with the
total-`fderiv` partial derivatives. -/
theorem transportIVP_add {b : ℝ^n} {f₁ f₂ : ℝ^(n + 1) → ℝ} {g₁ g₂ : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP (n := n) b f₁ g₁) u)
    (hv : SatisfiesPDEProblem (transportIVP (n := n) b f₂ g₂) v)
    (hdu : ∀ x ∈ transportDomain n, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ transportDomain n, DifferentiableAt ℝ v x) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun x ↦ f₁ x + f₂ x) (fun x ↦ g₁ x + g₂ x))
      (fun x ↦ u x + v x) := by
  refine transportIVP.of_residual_initial (n := n) ?_ ?_
  · intro x hx
    have hures := transportIVP.residual_eq (n := n) hu hx
    have hvres := transportIVP.residual_eq (n := n) hv hx
    rw [transportOperator_add b (hdu x hx) (hdv x hx), hures, hvres]
  · intro x hx
    have huinit := transportIVP.initial_eq (n := n) hu hx
    have hvinit := transportIVP.initial_eq (n := n) hv hx
    simp [huinit, hvinit]

/-- Scalar multiplication for the constant-velocity transport IVP. -/
theorem transportIVP_const_mul (c : ℝ) {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hu : SatisfiesPDEProblem (transportIVP (n := n) b f g) u)
    (hdu : ∀ x ∈ transportDomain n, DifferentiableAt ℝ u x) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun x ↦ c * f x) (fun x ↦ c * g x))
      (fun x ↦ c * u x) := by
  refine transportIVP.of_residual_initial (n := n) ?_ ?_
  · intro x hx
    have hures := transportIVP.residual_eq (n := n) hu hx
    have hop :
        transportOperator b (fun y ↦ c * u y) x = c * transportOperator b u x := by
      simpa [smul_eq_mul] using transportOperator_const_smul c b (hdu x hx)
    rw [hop, hures]
  · intro x hx
    have huinit := transportIVP.initial_eq (n := n) hu hx
    simp [huinit]

/-- Negation for the constant-velocity transport IVP. -/
theorem transportIVP_neg {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP (n := n) b f g) u) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun x ↦ -f x) (fun x ↦ -g x)) (fun x ↦ -u x) := by
  refine transportIVP.of_residual_initial (n := n) ?_ ?_
  · intro x hx
    have hures := transportIVP.residual_eq (n := n) hu hx
    rw [transportOperator_neg, hures]
  · intro x hx
    have huinit := transportIVP.initial_eq (n := n) hu hx
    simp [huinit]

/-- Difference of two residual witnesses for the constant-velocity transport IVP.

The differentiability hypotheses justify differentiating `u - v` with the total-`fderiv`
partial derivatives. -/
theorem transportIVP_sub {b : ℝ^n} {f₁ f₂ : ℝ^(n + 1) → ℝ} {g₁ g₂ : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP (n := n) b f₁ g₁) u)
    (hv : SatisfiesPDEProblem (transportIVP (n := n) b f₂ g₂) v)
    (hdu : ∀ x ∈ transportDomain n, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ transportDomain n, DifferentiableAt ℝ v x) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun x ↦ f₁ x - f₂ x) (fun x ↦ g₁ x - g₂ x))
      (fun x ↦ u x - v x) := by
  refine transportIVP.of_residual_initial (n := n) ?_ ?_
  · intro x hx
    have hures := transportIVP.residual_eq (n := n) hu hx
    have hvres := transportIVP.residual_eq (n := n) hv hx
    rw [transportOperator_sub b (hdu x hx) (hdv x hx), hures, hvres]
  · intro x hx
    have huinit := transportIVP.initial_eq (n := n) hu hx
    have hvinit := transportIVP.initial_eq (n := n) hv hx
    simp [huinit, hvinit]

/-- Linear combinations of two residual witnesses for the constant-velocity transport IVP.

This states superposition and scalar multiplication in the form usually used in energy and
stability arguments. -/
theorem transportIVP_linear_combination (c₁ c₂ : ℝ) {b : ℝ^n} {f₁ f₂ : ℝ^(n + 1) → ℝ}
    {g₁ g₂ : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP (n := n) b f₁ g₁) u)
    (hv : SatisfiesPDEProblem (transportIVP (n := n) b f₂ g₂) v)
    (hdu : ∀ x ∈ transportDomain n, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ transportDomain n, DifferentiableAt ℝ v x) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun x ↦ c₁ * f₁ x + c₂ * f₂ x)
      (fun x ↦ c₁ * g₁ x + c₂ * g₂ x)) (fun x ↦ c₁ * u x + c₂ * v x) := by
  have hcu := transportIVP_const_mul (n := n) c₁ hu hdu
  have hcv := transportIVP_const_mul (n := n) c₂ hv hdv
  exact transportIVP_add (n := n) hcu hcv
    (fun x hx ↦ by
      have hfun : (fun x ↦ c₁ * u x) = c₁ • u := by
        funext y
        simp [smul_eq_mul]
      rw [hfun]
      exact (hdu x hx).const_smul c₁)
    (fun x hx ↦ by
      have hfun : (fun x ↦ c₂ * v x) = c₂ • v := by
        funext y
        simp [smul_eq_mul]
      rw [hfun]
      exact (hdv x hx).const_smul c₂)

/-- Difference of two witnesses with equal source and initial value satisfies the homogeneous IVP.

This is the algebraic reduction used in uniqueness arguments; a uniqueness theorem must supply
the analytic hypotheses needed to compare the two candidate fields. -/
theorem transportIVP_difference_same_initial_homogeneous {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hu : SatisfiesPDEProblem (transportIVP (n := n) b f g) u)
    (hv : SatisfiesPDEProblem (transportIVP (n := n) b f g) v)
    (hdu : ∀ x ∈ transportDomain n, DifferentiableAt ℝ u x)
    (hdv : ∀ x ∈ transportDomain n, DifferentiableAt ℝ v x) :
    SatisfiesPDEProblem (transportIVP (n := n) b (fun _ : ℝ^(n + 1) ↦ 0) (fun _ : ℝ^n ↦ 0))
      (fun x ↦ u x - v x) := by
  simpa using transportIVP_sub (n := n) hu hv hdu hdv

/-- `transportInner` as a continuous linear map. -/
noncomputable def transportInnerCLM (b : ℝ^n) :
    ℝ^(n + 1) →L[ℝ] ℝ^n :=
  spatialPartCLM n -
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) b).comp
      (EuclideanSpace.proj (0 : Fin (n + 1)))

/-- The inner function for `transportFunction`: maps `(t,x)` to `x - t • b`. -/
noncomputable def transportInner (b : ℝ^n) :
    ℝ^(n + 1) → ℝ^n :=
  transportInnerCLM (n := n) b

/-- Method-of-characteristics candidate `u(t,x) = g(x - t•b)`.

`transportOperator_transportFunction_eq_zero` proves the pointwise transport equation when `g` is
differentiable. -/
noncomputable def transportFunction (b : ℝ^n)
    (g : ℝ^n → ℝ) :
    ℝ^(n + 1) → ℝ :=
  fun x ↦ g (transportInner (n := n) b x)

/-- Coordinates of the characteristic foot: `(x - t b)ᵢ = xᵢ - t bᵢ`. -/
theorem transportInner_apply (b : ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    transportInner (n := n) b x i = x i.succ - x 0 * b i := by
  simp [transportInner, transportInnerCLM, spatialPartCLM_apply, sub_eq_add_neg, smul_eq_mul]

/-- Translation at velocity `b` differentiates the initial profile in direction `-b`. -/
theorem transportFunction_time_deriv (b : ℝ^n) (g : ℝ^n → ℝ) (hg : ∀ x, DifferentiableAt ℝ g x)
    (x : ℝ^(n + 1)) :
    (∂[0] (transportFunction b g)) x = -∑ i, (b i) * (∂[i] g) (transportInner b x) := by
  classical
  unfold transportFunction partialDeriv
  have hgAt : DifferentiableAt ℝ g (transportInner b x) := hg (transportInner b x)
  have hInner : DifferentiableAt ℝ (transportInner b) x :=
    (transportInnerCLM (n := n) b).differentiableAt
  have hchain := congrArg (fun L ↦ L (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)))
      (fderiv_comp x hgAt hInner)
  have hInner_e0 : fderiv ℝ (transportInner b) x (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) =
        -b := by
    have hfderiv : fderiv ℝ (transportInner b) x = transportInnerCLM (n := n) b := by
      simp [transportInner]
    have happly := congrArg (fun L ↦ L (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) hfderiv
    have hmap : transportInnerCLM (n := n) b (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) =
          -b := by
      ext i
      simp [transportInnerCLM, sub_eq_add_neg]
    exact happly.trans hmap
  have hchain' : (fderiv ℝ (g ∘ transportInner b) x)
          (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = (fderiv ℝ g (transportInner b x))
          ((fderiv ℝ (transportInner b) x)
            (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) := by
    simpa [ContinuousLinearMap.comp_apply, Function.comp] using hchain
  have hstep : (fderiv ℝ (g ∘ transportInner b) x)
          (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) =
        (fderiv ℝ g (transportInner b x)) (-b) := by
    have h := hchain'
    rwa [hInner_e0] at h
  have hneg : (fderiv ℝ g (transportInner b x)) (-b) =
        -∑ i : Fin n, (b i) * (∂[i] g) (transportInner b x) := by
    classical
    have hb : (-b) =
        ∑ i : Fin n, ((-b) i) • EuclideanSpace.single i (1 : ℝ) := by
      simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (-b) |>.symm
    calc
      (fderiv ℝ g (transportInner b x)) (-b) = (fderiv ℝ g (transportInner b x))
            (∑ i : Fin n, ((-b) i) • EuclideanSpace.single i (1 : ℝ)) := by
            simpa using congrArg (fun v ↦ (fderiv ℝ g (transportInner b x)) v) hb
      _ = ∑ i : Fin n, (fderiv ℝ g (transportInner b x))
            (((-b) i) • EuclideanSpace.single i (1 : ℝ)) := by
            exact (map_sum (fderiv ℝ g (transportInner b x))
                (fun i : Fin n ↦ ((-b) i) • EuclideanSpace.single i (1 : ℝ)) Finset.univ)
      _ = ∑ i : Fin n, ((-b) i) * (fderiv ℝ g (transportInner b x))
            (EuclideanSpace.single i (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [smul_eq_mul]
      _ = -∑ i : Fin n, (b i) * (fderiv ℝ g (transportInner b x))
            (EuclideanSpace.single i (1 : ℝ)) := by
            simp [Finset.sum_neg_distrib, neg_mul]
      _ = -∑ i : Fin n, (b i) * (∂[i] g) (transportInner b x) := by
            simp [partialDeriv]
  change (fderiv ℝ (g ∘ transportInner b) x) (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) =
      -∑ i, b i * (∂[i] g) (transportInner b x)
  exact hstep.trans hneg

/-- Spatial differentiation commutes with translation by `-t b`. -/
theorem transportFunction_spatial_deriv (b : ℝ^n) (g : ℝ^n → ℝ) (hg : ∀ x, DifferentiableAt ℝ g x)
    (x : ℝ^(n + 1)) (i : Fin n) :
  spatialGradient (transportFunction b g) x i = (∂[i] g) (transportInner b x) := by
  classical
  have hgAt : DifferentiableAt ℝ g (transportInner b x) := hg (transportInner b x)
  have hInner : DifferentiableAt ℝ (transportInner b) x :=
    (transportInnerCLM (n := n) b).differentiableAt
  have hchain := congrArg (fun L ↦ L (EuclideanSpace.single i.succ (1 : ℝ)))
      (fderiv_comp x hgAt hInner)
  have hInner_esucc : fderiv ℝ (transportInner b) x (EuclideanSpace.single i.succ (1 : ℝ)) =
        EuclideanSpace.single i (1 : ℝ) := by
    have hfderiv : fderiv ℝ (transportInner b) x = transportInnerCLM (n := n) b := by
      simp [transportInner]
    have happly := congrArg (fun L ↦ L (EuclideanSpace.single i.succ (1 : ℝ))) hfderiv
    have hmap : transportInnerCLM (n := n) b (EuclideanSpace.single i.succ (1 : ℝ)) =
          EuclideanSpace.single i (1 : ℝ) := by
      ext j
      have h0 : (0 : Fin (n + 1)) ≠ i.succ := by
        simp [eq_comm]
      by_cases hj : j = i
      · subst hj
        simp [transportInnerCLM, sub_eq_add_neg, h0]
      · simp [transportInnerCLM, sub_eq_add_neg, h0, hj]
    exact happly.trans hmap
  have hstep : (∂[i.succ] (transportFunction b g)) x =
        (fderiv ℝ g (transportInner b x)) (EuclideanSpace.single i (1 : ℝ)) := by
    have hchain' : (fderiv ℝ (g ∘ transportInner b) x) (EuclideanSpace.single i.succ (1 : ℝ)) =
          (fderiv ℝ g (transportInner b x)) ((fderiv ℝ (transportInner b) x)
              (EuclideanSpace.single i.succ (1 : ℝ))) := by
      simpa [ContinuousLinearMap.comp_apply, Function.comp] using hchain
    have hchain'' : (fderiv ℝ (g ∘ transportInner b) x) (EuclideanSpace.single i.succ (1 : ℝ)) =
          (fderiv ℝ g (transportInner b x)) (EuclideanSpace.single i (1 : ℝ)) := by
      have h := hchain'
      rwa [hInner_esucc] at h
    unfold transportFunction partialDeriv
    change (fderiv ℝ (g ∘ transportInner b) x) (EuclideanSpace.single i.succ (1 : ℝ)) =
        (fderiv ℝ g (transportInner b x)) (EuclideanSpace.single i (1 : ℝ))
    exact hchain''
  have : (fderiv ℝ g (transportInner b x)) (EuclideanSpace.single i (1 : ℝ)) =
      (∂[i] g) (transportInner b x) := by
    rfl
  simp [hstep, this]

/-- Main theorem: `transportFunction` satisfies the pointwise transport residual. -/
theorem transportOperator_transportFunction_eq_zero (b : ℝ^n) (g : ℝ^n → ℝ)
    (hg : ∀ x, DifferentiableAt ℝ g x) (x : ℝ^(n + 1)) :
    transportOperator b (transportFunction b g) x = 0 := by
  rw [transportOperator_eq_timeDeriv_add_dot_spatialGradient]
  rw [transportFunction_time_deriv b g hg x]
  have h_sum : ∑ i, b i * spatialGradient (transportFunction b g) x i =
    ∑ i, b i * (∂[i] g) (transportInner b x) := by
    congr 1
    ext i
    rw [transportFunction_spatial_deriv b g hg x i]
  rw [h_sum]
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  simp only [neg_add_cancel]
  rw [Finset.sum_const_zero]

/-- The transport profile satisfies the prescribed initial condition. -/
theorem transportFunction_initial (b : ℝ^n) (g : ℝ^n → ℝ) (x : ℝ^(n + 1)) (hx : x 0 = 0) :
  transportFunction b g x = g (spatialPartCLM n x) := by
  unfold transportFunction transportInner transportInnerCLM
  simp [hx, sub_eq_add_neg]

/-- `transportFunction` satisfies the bundled transport residual and initial condition. -/
theorem transportFunction_satisfiesPDEProblem (b : ℝ^n) (g : ℝ^n → ℝ)
    (hg : ∀ x, DifferentiableAt ℝ g x) :
    SatisfiesPDEProblem (transportIVP b (fun _ : ℝ^(n + 1) ↦ 0) g) (transportFunction b g) := by
  refine transportIVP.of_residual_initial ?_ ?_
  · exact fun x _hx ↦ transportOperator_transportFunction_eq_zero b g hg x
  · exact fun x hx ↦ transportFunction_initial b g x hx


end TransportEquation
