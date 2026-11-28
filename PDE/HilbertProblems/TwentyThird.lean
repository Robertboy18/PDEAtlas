/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.Comparison
public import PDE.CalculusOfVariations.SlopeField.Closed
public import PDE.CalculusOfVariations.SlopeField.HamiltonJacobi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Hilbert's 23rd problem: further development of the methods of the calculus of variations

## Motivation

Hilbert's last problem is not one question. He asks for more work on the calculus of variations
and adds "a short justification" in which he develops two theorems. For the integral
`J = ∫ F(y_x, y; x) dx` and the integral `J* = ∫ {F + (y_x - p) F_p} dx`, with `F` and `F_p`
taken at the slope `p`, he asks (Newson's translation, p. 473):

> Now we inquire how p is to be chosen as function of x, y in order that the value of this
> integral J* shall be independent of the path of integration, i. e., of the choice of the
> function y of the variable x.

and, for a double integral and `J* = ∫ {F + (z_x - p) F_p + (z_y - q) F_q} dω`, he asks (p. 476)

> how p and q are to be taken as functions of x, y and z in order that the value of this
> integral may be independent of the choice of the surface passing through the given closed
> twisted curve, i. e., of the choice of the function z of the variables x and y.

This file states his answers for the simple integral, on a convex region and for curves along
which the integrals exist, and proves them from the general theory of slope fields. For the
double integral it states them for a field that is given by a family of extremal surfaces.

## The idea

Hilbert writes `J* = ∫ {A y_x - B} dx` with `A = F_p` and `B = p F_p - F`, functions of `x` and
`y` alone. So `J*` is the integral of the 1-form `A dy - B dx` over the graph of `y`, and it is
independent of the path when this form is closed: `∂A/∂x + ∂B/∂y = 0`. This is his equation
(1*), a first-order partial differential equation for `p`. On a convex region a closed form is
the differential of a function `S`, and then `J*` is `S` at the right endpoint minus `S` at the
left endpoint.

Along a curve `y_x = p(x, y)` of the field the integrand of `J*` is `F`, so `J*` there is `J`.
This gives his formula (3), and subtracting `J*` from `J` along any other curve gives
Weierstrass's formula (4), `J(y) - J(ȳ) = ∫ E(y_x, p) dx`, where `E` is the excess of `F` over
its tangent at the slope `p`. If `E ≥ 0`, the curve of the field is a minimum, without any
bound on the slopes of the competing curve.

Equation (1*) at a point says that the curve of the field through the point satisfies the
Euler–Lagrange equation (1) there. We write `y₀` for Hilbert's `ȳ`, and a curve is a function
that is continuous on `[a, b]` and differentiable off a countable set, so corners are allowed.
Wherever an integral along a curve occurs, the theorem assumes that its integrand is interval
integrable; this is meant when a statement below says "a curve" or "any curve".

For the double integral Hilbert's slopes `p`, `q` are functions of `x`, `y`, `z`. He says that
the Euler–Lagrange equation (I) and the equations for `p` and `q` "stand toward one another in
a relation exactly analogous to that" of (1) and (1*), and he compares with "an integral
surface" `z̄_x = p`, `z̄_y = q` of the field; in that relation these surfaces solve (I). Here
the field is given by these surfaces: a family `z = Z t` of solutions of (I), one for each
value of a parameter `t`. The surfaces that are compared are the parameter graphs
`z(x) = Z (θ x) x` of a `C¹` function `θ` with values in the parameter interval, and the slopes
used at the point `(x, z(x))` are the derivatives of the member `Z (θ x)` at `x`. Two such
surfaces pass through the same boundary curve when their parameters agree on the boundary, and
then `J*` has the same value along both. Agreement of the parameters is what is assumed: two
parameter graphs through one boundary curve whose parameters differ there are not compared.
If the surfaces of the family do not meet over the boundary, surfaces through one boundary
curve have parameters that agree there, and this is Hilbert's statement for them.
The surface has the boundary curve of `z̄ = Z 0` when `θ` vanishes on the boundary. Then `J*`,
taken along the surface, is `J(z̄)`, and Hilbert's formula (IV) follows as formula (4) did.

The number of variables and the number of unknown functions are arbitrary, but the family has
one real parameter. No field condition is assumed: the family need not cover a region simply,
so it need not define single-valued slope functions of the point, and a surface in the region
need not be a parameter graph. For more than one unknown function a family with one parameter
sweeps out a thin set, and the derivatives of a parameter graph differ from the slopes of the
field by a matrix of rank at most one.

## Main results

All of these are for all integrands `F`, all slope functions `p` and all regions with the
stated properties; `isSlopeFunction_central` is one example.

* `independence` : if `p` solves (1*) on a convex open region, `J*` takes the same value on any
  two curves in the region with the same endpoints. Rests on
  `SlopeField.exists_isEikonal_of_convex`, `SlopeField.isClosedAt_iff_deriv` and
  `SlopeField.IsEikonal.invariantIntegral_eq_of_endpoints`.
* `fieldEquation_iff_eulerLagrange` : (1*) holds at a point exactly when the curve of the field
  through it satisfies (1) there. Rests on `SlopeField.isClosedAt_iff_hasDerivAt_deriv`.
* `hilbertIntegral_eq_integral` : formula (3). Rests on the same theorems as `independence` and
  on `SlopeField.invariantIntegral_eq_integral_of_field`.
* `weierstrass_formula` : formula (4). Rests on
  `SlopeField.IsEikonal.integral_sub_integral_eq_integral_weierstrassExcess`.
* `integral_le_of_weierstrassE_nonneg` : Weierstrass's condition `E ≥ 0` on the region makes the
  curve of the field a minimum among all curves in the region with its endpoints. Rests on
  `SlopeField.IsEikonal.integral_le_of_weierstrassExcess_nonneg`.
* `weierstrass_formula_of_isClosedAt` : formula (4) for "two or more required functions", with
  values in any real normed space, for a field whose form is closed on a convex open region.
* `exists_eikonal_hamiltonJacobi` : for a slope function solving (1*) there is a function `S`,
  differentiable on the region with differential `A dy - B dx`, with
  `J* = S(b, y(b)) - S(a, y(a))` on every curve, and `S` solves
  `S_x + sup_q (S_y q - F(q, y; x)) = 0` where `F` is convex in `y_x`. This is the solution of
  the "generalization of the Jacobi-Hamilton equation" that Hilbert attributes to Kneser. Rests
  on `SlopeField.IsEikonal.hamiltonJacobi`.
* `isSlopeFunction_central` : the lines through the origin, `p = y / x` on the half plane
  `x > 0`, for `F = y_x² / 2`, are an instance of `IsSlopeFunction`. This is a field of the
  kind Weierstrass used, of curves through a fixed point.
  `PDE.Examples.CentralField.integral_kinetic_line_le` applies the general theorem to these
  lines and a competing curve.
* `multipleIntegral_independence` (all families of extremal surfaces in the sense of
  `ExtremalFamily.IsExtremalFamily`, all pairs of parameters in the sense of
  `ExtremalFamily.IsGraphParameter` that agree on the boundary): the integral `J*` has the
  same value along the surfaces `z = Z (θ x) x` and `z' = Z (θ' x) x`. Rests on
  `ExtremalFamily.integral_invariant_eq_of_eqOn_frontier`. The integrand of `J*` is
  integrable (`integrableOn_fieldIntegrand`).
* `multipleIntegral_independence_of_injOn` (all such families whose surfaces do not meet over
  the boundary, all pairs of parameters): `J*` has the same value along two surfaces
  `z = Z (θ x) x` with the same boundary values.
* `multipleIntegral_eq_lagrangianAction` (all such families, all parameters that vanish on the
  boundary): `J*` along the surface `z = Z (θ x) x` is `J(Z 0)`. This is Hilbert's formula for
  the double integral that precedes (IV). Rests on
  `ExtremalFamily.integral_invariant_parameter_graph`.
* `multipleIntegral_weierstrass_formula` (same scope): formula (IV),
  `J(z) - J(z̄) = ∫ E dω`. Rests on
  `ExtremalFamily.lagrangianAction_parameter_graph_sub_eq_integral_graphExcess`.
* `multipleIntegral_le_of_fieldE_nonneg` (same scope): Weierstrass's condition `E ≥ 0` on the
  field makes the surface `z̄` of the field a minimum among the surfaces `z = Z (θ x) x` with
  `θ = 0` on the boundary. Rests on
  `ExtremalFamily.lagrangianAction_le_parameter_graph_of_graphExcess_nonneg`. The condition
  holds for all integrands that are convex in the derivatives (`fieldE_nonneg_of_convexOn`).

## Relations

* `hilbertIntegral_eq_invariantIntegral` identifies `J*` with
  `SlopeField.invariantIntegral`, and `fieldEquation_iff_isClosedAt` identifies (1*) with
  closedness of the form of the field. Every theorem here for the simple integral is derived
  from the general theory through these two.
* For more than one unknown function, (1*) alone is not enough: the derivative of `F_p` in `y`
  must also be symmetric (`SlopeField.isClosedAt_iff`). For one unknown this is automatic.
* For the multiple integral, `integral_fieldIntegrand` identifies `J*` with the invariant
  integral of a family of extremals, and `graphExcess_eq_fieldE` identifies Hilbert's `E` with
  `ExtremalFamily.graphExcess`. `fieldDensity_eq_fieldIntegrand_add_fieldE` is the identity
  "`F` is the integrand of `J*` plus `E`" behind formula (IV). In the general theory the
  formula that precedes (IV) is the independence theorem for `θ` and the parameter `0`
  (`ExtremalFamily.integral_invariant_parameter_graph`).
* The `E` of the simple integral and the `E` of the multiple integral are one definition of
  the general theory, `SlopeField.weierstrassExcess` (`weierstrassE_eq`, `fieldE_eq`).
* The comparison theorem `ExtremalFamily.lagrangianAction_le_parameter_graph_of_closureJets`
  of the library (convex integrands) is formula (IV) with `ExtremalFamily.graphExcess_nonneg`,
  and is proved from it.
* `PDE.Examples.PlaneFamily.isExtremalFamily_plane` and
  `PDE.Examples.PlaneFamily.isGraphParameter_bump` are instances of the premises: the parallel
  planes `z = t + x` for Dirichlet's integral on the disk.

## What stays open

* Regions that are not convex. With an eikonal as a premise,
  `SlopeField.IsEikonal.invariantIntegral_eq_of_endpoints` needs no assumption on the region.
* Jacobi's condition, the construction of a field around a given extremal, strict minimality
  under `E > 0`, and necessity of the conditions. Hilbert says the developments lead to "the
  answer to the question: How far this condition of Jacobi's in conjunction with Weierstrass's
  condition E > 0 is necessary and sufficient for the occurrence of a minimum". Only
  sufficiency is proved here.
* For the double integral, the description of the field by slope functions `p`, `q` of
  `x`, `y`, `z`: Hilbert's first-order equation for them, the condition (I*), and that a field
  of this kind is given by a family of surfaces. Surfaces that are not of the form
  `z = Z (θ x) x` are not compared, and no theorem turns a surface of the region into a
  parameter.

## References

* D. Hilbert, *Mathematical problems*, translated by M. W. Newson, Bull. Amer. Math. Soc. 8
  (1902), 437-479, problem 23 on pp. 472-478. <https://doi.org/10.1090/S0002-9904-1902-00923-3>
  Online: <https://mathcs.clarku.edu/~djoyce/hilbert/problems.html>. In the printed text the
  expanded form of (1*) reads `(p_x + p p_y) F_pp + p F_py + F_px - F_y = 0`; the online copy
  prints `p p_x`.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.CalculusOfVariations PDE.CalculusOfVariations.SlopeField

namespace PDE.HilbertProblems.TwentyThird

section SimpleIntegral

/-- Hilbert's `A = F_p`, the derivative of `F(y_x, y; x)` in `y_x` at `y_x = p(x, y)`. In Lean
`F (x, y) q` is Hilbert's `F(q, y; x)`. -/
def fieldA (F : ℝ × ℝ → ℝ → ℝ) (p : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  deriv (F z) (p z)

/-- Hilbert's `B = p F_p - F`, with `F` and `F_p` at `y_x = p(x, y)`. -/
def fieldB (F : ℝ × ℝ → ℝ → ℝ) (p : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  p z * deriv (F z) (p z) - F z (p z)

/-- Hilbert's integral `J* = ∫_a^b {F + (y_x - p) F_p} dx`, with `F` and `F_p` at
`y_x = p(x, y)`, along the curve `y` with derivative `y'`. -/
def hilbertIntegral (F : ℝ × ℝ → ℝ → ℝ) (p : ℝ × ℝ → ℝ) (a b : ℝ) (y y' : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, F (x, y x) (p (x, y x)) +
    (y' x - p (x, y x)) * deriv (F (x, y x)) (p (x, y x))

/-- Weierstrass's expression `E(y_x, p) = F(y_x) - F(p) - (y_x - p) F_p(p)` at the point `z`. -/
def weierstrassE (F : ℝ × ℝ → ℝ → ℝ) (z : ℝ × ℝ) (yx p : ℝ) : ℝ :=
  F z yx - F z p - (yx - p) * deriv (F z) p

/-- Hilbert's equation (1*) for the slope function `p` at the point `z = (x, y)`:
`∂F_p/∂x + ∂(p F_p - F)/∂y = 0`. -/
def FieldEquation (F : ℝ × ℝ → ℝ → ℝ) (p : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : Prop :=
  deriv (fun x ↦ fieldA F p (x, z.2)) z.1 + deriv (fun y ↦ fieldB F p (z.1, y)) z.2 = 0

/-- A slope function for `F` on the region `D`: the region is convex and open, `F` is
differentiable in `y_x` at the slope of the field, Hilbert's `A` and `B` are differentiable on
the region, and `p` solves equation (1*) there.

The field `differentiableAt` makes `fieldA` the derivative `F_p`: Lean's `deriv` is `0` where a
function has no derivative. The proofs of the independence theorem and of Weierstrass's formula
do not use it; the Hamilton–Jacobi equation does. -/
structure IsSlopeFunction (F : ℝ × ℝ → ℝ → ℝ) (p : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : Prop where
  /-- The region is convex. -/
  convex : Convex ℝ D
  /-- The region is open. -/
  isOpen : IsOpen D
  /-- `F` is differentiable in `y_x` at the slope of the field. -/
  differentiableAt : ∀ z ∈ D, DifferentiableAt ℝ (F z) (p z)
  /-- `A = F_p` is differentiable on the region. -/
  differentiableOn_fieldA : DifferentiableOn ℝ (fieldA F p) D
  /-- `B = p F_p - F` is differentiable on the region. -/
  differentiableOn_fieldB : DifferentiableOn ℝ (fieldB F p) D
  /-- The slope function solves equation (1*) on the region. -/
  fieldEquation : ∀ z ∈ D, FieldEquation F p z

variable {F : ℝ × ℝ → ℝ → ℝ} {p : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)} {a b : ℝ}
  {y y' y₀ y₀' : ℝ → ℝ}

/-- The integrand of `J*` is the form of the slope field on the velocity of the graph. -/
theorem beltramiForm_one_eq (z : ℝ × ℝ) (q : ℝ) :
    beltramiForm F p z (1, q) = F z (p z) + (q - p z) * deriv (F z) (p z) := by
  rw [beltramiForm_one, momentum_apply_real]

/-- Hilbert's integral `J*` is the invariant integral of the slope field `p`. -/
theorem hilbertIntegral_eq_invariantIntegral :
    hilbertIntegral F p a b y y' = invariantIntegral F p a b y y' := by
  unfold hilbertIntegral invariantIntegral
  simp only [beltramiForm_one_eq]

/-- "The integral `J*` has the form `∫ {A y_x - B} dx`, where `A` and `B` do not contain
`y_x`." -/
theorem hilbertIntegral_eq_integral_sub :
    hilbertIntegral F p a b y y' =
      ∫ x in a..b, fieldA F p (x, y x) * y' x - fieldB F p (x, y x) := by
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  simp only [fieldA, fieldB]
  ring

/-- Weierstrass's expression is the excess of the general theory. -/
theorem weierstrassE_eq (z : ℝ × ℝ) (yx q : ℝ) :
    weierstrassE F z yx q = weierstrassExcess (F z) q yx := by
  rw [weierstrassE, weierstrassExcess, fderiv_eq_smul_deriv, smul_eq_mul]

/-- Equation (1*) at a point is closedness of the form of the slope field there. -/
theorem fieldEquation_iff_isClosedAt {z : ℝ × ℝ} (hA : DifferentiableAt ℝ (fieldA F p) z)
    (hB : DifferentiableAt ℝ (fieldB F p) z) : FieldEquation F p z ↔ IsClosedAt F p z :=
  (isClosedAt_iff_deriv hA hB).symm

/-- A slope function on a convex open region has an eikonal: a function `S` whose differential
is `A dy - B dx`. -/
theorem IsSlopeFunction.exists_isEikonal (hp : IsSlopeFunction F p D) :
    ∃ S, IsEikonal F p D S := by
  have hA (z : ℝ × ℝ) (hz : z ∈ D) : DifferentiableAt ℝ (fieldA F p) z :=
    hp.differentiableOn_fieldA.differentiableAt (hp.isOpen.mem_nhds hz)
  have hB (z : ℝ × ℝ) (hz : z ∈ D) : DifferentiableAt ℝ (fieldB F p) z :=
    hp.differentiableOn_fieldB.differentiableAt (hp.isOpen.mem_nhds hz)
  have hB' (z : ℝ × ℝ) (hz : z ∈ D) : DifferentiableAt ℝ (energy F p) z := by
    rw [show energy F p = fieldB F p from funext energy_eq_real]
    exact hB z hz
  refine exists_isEikonal_of_convex hp.convex hp.isOpen (fun z hz ↦ ?_) fun z hz ↦ ?_
  · exact (differentiableAt_beltramiForm (differentiableAt_momentum_real (hA z hz))
      (hB' z hz)).differentiableWithinAt
  · exact (fieldEquation_iff_isClosedAt (hA z hz) (hB z hz)).mp (hp.fieldEquation z hz)

/-- Hilbert's independence theorem for the simple integral. If the slope function `p` solves
equation (1*) on a convex open region, the integral `J*` has the same value on any two curves
in the region with the same endpoints, along which its integrand is interval integrable.
Equation (1*) makes the form `A dy - B dx` closed, the Poincaré lemma gives a function `S`
with this differential, and `J*` is the difference of the values of `S` at the endpoints. -/
theorem independence (hp : IsSlopeFunction F p D) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hint : IntervalIntegrable (fun x ↦ F (x, y x) (p (x, y x)) +
      (y' x - p (x, y x)) * deriv (F (x, y x)) (p (x, y x))) volume a b)
    (hint₀ : IntervalIntegrable (fun x ↦ F (x, y₀ x) (p (x, y₀ x)) +
      (y₀' x - p (x, y₀ x)) * deriv (F (x, y₀ x)) (p (x, y₀ x))) volume a b)
    (ha : y a = y₀ a) (hb : y b = y₀ b) :
    hilbertIntegral F p a b y y' = hilbertIntegral F p a b y₀ y₀' := by
  obtain ⟨S, hS⟩ := hp.exists_isEikonal
  simp only [← beltramiForm_one_eq] at hint hint₀
  rw [hilbertIntegral_eq_invariantIntegral, hilbertIntegral_eq_invariantIntegral]
  exact hS.invariantIntegral_eq_of_endpoints hab hy hy₀ hint hint₀ ha hb

/-- The relation between equations (1) and (1*). Let `y₀` solve `y_x = p(x, y)` near `x₀`. Then
`p` solves (1*) at the point `(x₀, y₀(x₀))` exactly when `y₀` solves the Euler–Lagrange equation
(1) at `x₀`: `d/dx F_{y_x}(y₀_x, y₀; x) = F_y(y₀_x, y₀; x)`. So the curves of the field are
extremals exactly when the slope function is an integral of (1*). -/
theorem fieldEquation_iff_eulerLagrange {x₀ : ℝ}
    (hF : DifferentiableAt ℝ (fun w : (ℝ × ℝ) × ℝ ↦ F w.1 w.2)
      ((x₀, y₀ x₀), p (x₀, y₀ x₀)))
    (hp : DifferentiableAt ℝ p (x₀, y₀ x₀))
    (hA : DifferentiableAt ℝ (fieldA F p) (x₀, y₀ x₀))
    (hy₀ : ∀ᶠ x in nhds x₀, HasDerivAt y₀ (p (x, y₀ x)) x) :
    FieldEquation F p (x₀, y₀ x₀) ↔
      HasDerivAt (fun x ↦ deriv (F (x, y₀ x)) (deriv y₀ x))
        (deriv (fun y ↦ F (x₀, y) (deriv y₀ x₀)) (y₀ x₀)) x₀ := by
  have hB : DifferentiableAt ℝ (fieldB F p) (x₀, y₀ x₀) := by
    rw [show fieldB F p = energy F p from (funext energy_eq_real).symm]
    exact differentiableAt_energy hF hp (differentiableAt_momentum_real hA)
  have hd : (fun x ↦ deriv (F (x, y₀ x)) (deriv y₀ x)) =ᶠ[nhds x₀]
      fun x ↦ deriv (F (x, y₀ x)) (p (x, y₀ x)) :=
    hy₀.mono fun x hx ↦ by simp only [hx.deriv]
  rw [fieldEquation_iff_isClosedAt hA hB,
    isClosedAt_iff_hasDerivAt_deriv hF hp hA hy₀.self_of_nhds, hy₀.self_of_nhds.deriv]
  exact ⟨fun h ↦ h.congr_of_eventuallyEq hd, fun h ↦ h.congr_of_eventuallyEq hd.symm⟩

/-- Hilbert's formula (3): `∫ {F(p) + (y_x - p) F_p(p)} dx = ∫ F(ȳ_x) dx`, the left integral
along any curve `y` in the region and the right one along a curve `y₀` of the field,
`y₀_x = p(x, y₀)`, with the same endpoints. The integrands of `J*` along both curves are
assumed interval integrable. -/
theorem hilbertIntegral_eq_integral (hp : IsSlopeFunction F p D) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hint : IntervalIntegrable (fun x ↦ F (x, y x) (p (x, y x)) +
      (y' x - p (x, y x)) * deriv (F (x, y x)) (p (x, y x))) volume a b)
    (hF₀ : IntervalIntegrable (fun x ↦ F (x, y₀ x) (y₀' x)) volume a b) :
    hilbertIntegral F p a b y y' = ∫ x in a..b, F (x, y₀ x) (y₀' x) := by
  have hint₀ : IntervalIntegrable (fun x ↦ F (x, y₀ x) (p (x, y₀ x)) +
      (y₀' x - p (x, y₀ x)) * deriv (F (x, y₀ x)) (p (x, y₀ x))) volume a b := by
    refine hF₀.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with x hxb hx
    rw [uIoc_of_le hab] at hx
    rw [hfield x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩, sub_self, zero_mul, add_zero]
  rw [independence hp hab hy hy₀ hint hint₀ ha hb, hilbertIntegral_eq_invariantIntegral,
    invariantIntegral_eq_integral_of_field hab hfield]

/-- Weierstrass's formula (4): `∫ F(y_x) dx - ∫ F(ȳ_x) dx = ∫ E(y_x, p) dx` for a slope function
`p` solving (1*), a curve `y₀` of the field and any curve `y` in the region with the endpoints
of `y₀`. The integrands `F(y_x)`, `F(ȳ_x)` and the integrand of `J*` along `y` are assumed
interval integrable. -/
theorem weierstrass_formula (hp : IsSlopeFunction F p D) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hF : IntervalIntegrable (fun x ↦ F (x, y x) (y' x)) volume a b)
    (hint : IntervalIntegrable (fun x ↦ F (x, y x) (p (x, y x)) +
      (y' x - p (x, y x)) * deriv (F (x, y x)) (p (x, y x))) volume a b)
    (hF₀ : IntervalIntegrable (fun x ↦ F (x, y₀ x) (y₀' x)) volume a b) :
    (∫ x in a..b, F (x, y x) (y' x)) - ∫ x in a..b, F (x, y₀ x) (y₀' x) =
      ∫ x in a..b, weierstrassE F (x, y x) (y' x) (p (x, y x)) := by
  obtain ⟨S, hS⟩ := hp.exists_isEikonal
  simp only [← beltramiForm_one_eq] at hint
  simp only [weierstrassE_eq]
  exact hS.integral_sub_integral_eq_integral_weierstrassExcess hab hy hy₀ hfield ha hb hF hint
    hF₀

/-- Weierstrass's condition is sufficient for a minimum. If `E(y_x, p) ≥ 0` at every point of
the region and for every slope `y_x`, a curve `y₀` of the field has `J(y₀) ≤ J(y)` for every
curve `y` in the region with the same endpoints, whatever the slopes of `y`, under the
integrability assumptions of `weierstrass_formula`. The inequality is not strict. -/
theorem integral_le_of_weierstrassE_nonneg (hp : IsSlopeFunction F p D) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hF : IntervalIntegrable (fun x ↦ F (x, y x) (y' x)) volume a b)
    (hint : IntervalIntegrable (fun x ↦ F (x, y x) (p (x, y x)) +
      (y' x - p (x, y x)) * deriv (F (x, y x)) (p (x, y x))) volume a b)
    (hF₀ : IntervalIntegrable (fun x ↦ F (x, y₀ x) (y₀' x)) volume a b)
    (hE : ∀ z ∈ D, ∀ yx : ℝ, 0 ≤ weierstrassE F z yx (p z)) :
    ∫ x in a..b, F (x, y₀ x) (y₀' x) ≤ ∫ x in a..b, F (x, y x) (y' x) := by
  obtain ⟨S, hS⟩ := hp.exists_isEikonal
  simp only [← beltramiForm_one_eq] at hint
  refine hS.integral_le_of_weierstrassExcess_nonneg hab hy hy₀ hfield ha hb hF hint hF₀
    fun x hx ↦ ?_
  have h := hE (x, y x) (hy.mem x hx) (y' x)
  rwa [weierstrassE_eq] at h

/-- The function that Hilbert attributes to Kneser. For a slope function `p` solving (1*) there
is a function `S` with three properties. It is differentiable at every point of the region,
with differential `A dy - B dx` (`IsEikonal`). Along every curve in the region with an interval
integrable integrand, `J* = S(b, y(b)) - S(a, y(a))`. At every point of the region where `F`
is convex in `y_x` it solves the Hamilton–Jacobi equation
`S_x + sup_q (S_y q - F(q, y; x)) = 0`; the derivatives `S_x` and `S_y` exist by the first
property. -/
theorem exists_eikonal_hamiltonJacobi (hp : IsSlopeFunction F p D) :
    ∃ S : ℝ × ℝ → ℝ, IsEikonal F p D S ∧
      (∀ {a b : ℝ} {y y' : ℝ → ℝ}, a ≤ b → IsCurveIn D a b y y' →
        IntervalIntegrable (fun x ↦ F (x, y x) (p (x, y x)) +
          (y' x - p (x, y x)) * deriv (F (x, y x)) (p (x, y x))) volume a b →
        hilbertIntegral F p a b y y' = S (b, y b) - S (a, y a)) ∧
      ∀ z ∈ D, ConvexOn ℝ univ (F z) →
        fderiv ℝ S z (1, 0) + ⨆ q : ℝ, (fderiv ℝ S z (0, q) - F z q) = 0 := by
  obtain ⟨S, hS⟩ := hp.exists_isEikonal
  refine ⟨S, hS, fun hab hy hint ↦ ?_,
    fun z hz hconvex ↦ hS.hamiltonJacobi hz hconvex (hp.differentiableAt z hz)⟩
  simp only [← beltramiForm_one_eq] at hint
  rw [hilbertIntegral_eq_invariantIntegral]
  exact hS.invariantIntegral_eq hab hy hint

end SimpleIntegral

section SeveralFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : ℝ × E → E → ℝ} {p : ℝ × E → E} {D : Set (ℝ × E)} {a b : ℝ} {y y' y₀ y₀' : ℝ → E}

/-- Weierstrass's formula for "two or more required functions": the unknown `y` takes values in
a real normed space. The slope field must have a closed form on a convex open region; for more
than one unknown this is equation (1*) together with the symmetry of the derivative of `F_p` in
`y` (`SlopeField.isClosedAt_iff`). Then, for a curve `y₀` of the field and any curve `y` in the
region with the endpoints of `y₀`, `J(y) - J(y₀)` is the integral of the excess, when the
integrands are interval integrable. -/
theorem weierstrass_formula_of_isClosedAt (hD : Convex ℝ D) (hDo : IsOpen D)
    (hω : DifferentiableOn ℝ (beltramiForm F p) D) (hclosed : ∀ z ∈ D, IsClosedAt F p z)
    (hab : a ≤ b) (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hF : IntervalIntegrable (fun x ↦ F (x, y x) (y' x)) volume a b)
    (hint : IntervalIntegrable (fun x ↦ F (x, y x) (p (x, y x)) +
      fderiv ℝ (F (x, y x)) (p (x, y x)) (y' x - p (x, y x))) volume a b)
    (hF₀ : IntervalIntegrable (fun x ↦ F (x, y₀ x) (y₀' x)) volume a b) :
    (∫ x in a..b, F (x, y x) (y' x)) - ∫ x in a..b, F (x, y₀ x) (y₀' x) =
      ∫ x in a..b, (F (x, y x) (y' x) - F (x, y x) (p (x, y x)) -
        fderiv ℝ (F (x, y x)) (p (x, y x)) (y' x - p (x, y x))) := by
  obtain ⟨S, hS⟩ := exists_isEikonal_of_convex hD hDo hω hclosed
  have hint' : IntervalIntegrable (fun x ↦ beltramiForm F p (x, y x) (1, y' x)) volume a b := by
    simpa only [beltramiForm_one, momentum] using hint
  exact hS.integral_sub_integral_eq_integral_weierstrassExcess hab hy hy₀ hfield ha hb hF hint'
    hF₀

end SeveralFunctions

section MultipleIntegral

open PDE.Analysis PDE.CalculusOfVariations.ExtremalFamily PDE.CalculusOfVariations.Noether
  SobolevSpace
open scoped Matrix.Norms.Elementwise

variable {d m : ℕ} {Ω : Set (ℝ^(d + 1))} {J : Set ℝ}
  {F : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ}
  {Z : ℝ → ℝ^(d + 1) → ℝ^m} {θ θ' : ℝ^(d + 1) → ℝ}

/-- The integrand of Hilbert's integral `J*` for a multiple integral, on the surface
`z(x) = Z (θ x) x` in a field of surfaces `z = Z t`: `F(P) + (Dz - P) F_P(P)`, where `P` is the
matrix of derivatives at `x` of the surface of the field through the point `(x, z(x))`, and
`F` and `F_P` are taken at the value `z(x)`. For one unknown function of two variables this
is Hilbert's `F(p, q) + (z_x - p) F_p + (z_y - q) F_q`. In Lean `F P z x` is Hilbert's
`F(z_x, z_y, z; x, y)`. -/
def fieldIntegrand (F : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ)
    (Z : ℝ → ℝ^(d + 1) → ℝ^m) (θ : ℝ^(d + 1) → ℝ) (x : ℝ^(d + 1)) : ℝ :=
  fieldDensity F (Z (θ x)) x +
    fderiv ℝ (fun P ↦ F P (Z (θ x) x) x) (jacobianMatrix (Z (θ x)) x)
      (jacobianMatrix (fun y ↦ Z (θ y) y) x - jacobianMatrix (Z (θ x)) x)

/-- Hilbert's `E(z_x, z_y, p, q) = F(z_x, z_y) - F(p, q) - (z_x - p) F_p(p, q) -
(z_y - q) F_q(p, q)` at the point `x` of a surface `z₀` of the field. The matrix `P` holds
the derivatives `z_x`, `z_y` of a surface through the point `(x, z₀ x)`, the slopes `p`, `q`
are the derivatives of `z₀` at `x`, and `F` and its derivatives are taken at the value
`z₀ x`. -/
def fieldE (F : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ)
    (z₀ : ℝ^(d + 1) → ℝ^m) (x : ℝ^(d + 1)) (P : Matrix (Fin m) (Fin (d + 1)) ℝ) : ℝ :=
  F P (z₀ x) x - F (jacobianMatrix z₀ x) (z₀ x) x -
    fderiv ℝ (fun Q ↦ F Q (z₀ x) x) (jacobianMatrix z₀ x) (P - jacobianMatrix z₀ x)

/-- Hilbert's `E` for the multiple integral is the excess of the general theory of slope
fields, for `F` as a function of the matrix of derivatives: the same expression as
Weierstrass's `E` of the simple integral (`weierstrassE_eq`). -/
theorem fieldE_eq (z₀ : ℝ^(d + 1) → ℝ^m) (x : ℝ^(d + 1)) (P : Matrix (Fin m) (Fin (d + 1)) ℝ) :
    fieldE F z₀ x P = weierstrassExcess (fun Q ↦ F Q (z₀ x) x) (jacobianMatrix z₀ x) P :=
  rfl

/-- Weierstrass's condition holds for an integrand that is convex in the derivatives: `E ≥ 0`
at every point where `F` is convex in `z_x`, `z_y` and differentiable at the slopes of the
surface `z₀`. This is `SlopeField.weierstrassExcess_nonneg_of_convexOn`. -/
theorem fieldE_nonneg_of_convexOn {z₀ : ℝ^(d + 1) → ℝ^m} {x : ℝ^(d + 1)}
    (hconvex : ConvexOn ℝ univ fun Q ↦ F Q (z₀ x) x)
    (hd : DifferentiableAt ℝ (fun Q ↦ F Q (z₀ x) x) (jacobianMatrix z₀ x))
    (P : Matrix (Fin m) (Fin (d + 1)) ℝ) : 0 ≤ fieldE F z₀ x P :=
  weierstrassExcess_nonneg_of_convexOn hconvex hd P

/-- The excess of the general theory of families is Hilbert's `E`: along the surface
`z(x) = Z (θ x) x` it is `E` at the surface `Z (θ x)` of the field through the point, with the
derivatives of `z` in the first two places. -/
theorem graphExcess_eq_fieldE (x : ℝ^(d + 1)) :
    graphExcess F Z θ x = fieldE F (Z (θ x)) x (jacobianMatrix (fun y ↦ Z (θ y) y) x) :=
  rfl

/-- On the surface `z(x) = Z (θ x) x` the integrand `F(z_x, z_y)` is the integrand of `J*`
plus `E`. Integrating this identity gives formula (IV). -/
theorem fieldDensity_eq_fieldIntegrand_add_fieldE (x : ℝ^(d + 1)) :
    fieldDensity F (fun y ↦ Z (θ y) y) x =
      fieldIntegrand F Z θ x + fieldE F (Z (θ x)) x (jacobianMatrix (fun y ↦ Z (θ y) y) x) := by
  change _ = fieldIntegrand F Z θ x + graphExcess F Z θ x
  simp only [fieldIntegrand, graphExcess]
  ring

/-- At a point of `Ω`, the integrand of `J*` on the surface `z(x) = Z (θ x) x` is the
invariant integrand of the general theory: the term `(Dz - P) F_P(P)` is the pairing of the
flux of the family with the differential of `θ`. -/
theorem fieldIntegrand_eq
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ) {x : ℝ^(d + 1)}
    (hx : x ∈ Ω) :
    fieldIntegrand F Z θ x =
      fieldDensity F (Z (θ x)) x + fderiv ℝ θ x (familyFlux F Z (θ x) x) := by
  obtain ⟨hopen, -, -, hJ, -, -, ⟨hF⟩, ⟨hZ⟩, -⟩ := hfam
  obtain ⟨hθ, hθJ⟩ := hpar
  have hFi : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin (d + 1)) ℝ × (ℝ^m × ℝ^(d + 1)) ↦ F a.1 a.2.1 a.2.2)
      (jacobianMatrix (Z (θ x)) x, (Z (θ x) x, x)) :=
    (hF.contDiffOn.contDiffAt ((hopen.preimage
      (continuous_snd.comp continuous_snd)).mem_nhds hx)).differentiableAt (by norm_num)
  have hZi : DifferentiableAt ℝ (fun p : ℝ × ℝ^(d + 1) ↦ Z p.1 p.2) (θ x, x) :=
    ((hZ.contDiffOn.contDiffAt ((hopen.prod hJ).mem_nhds
      ⟨hx, hθJ (subset_closure hx)⟩)).comp (θ x, x) (f := Prod.swap)
      (contDiffAt_snd.prodMk contDiffAt_fst)).differentiableAt (by norm_num)
  rw [fieldIntegrand,
    fderiv_gradient_parameter_graph_sub hFi hZi (hθ.differentiable (by norm_num) x)]

/-- Hilbert's integral `J*` along the surface `z(x) = Z (θ x) x` is the invariant integral of
the general theory. -/
theorem integral_fieldIntegrand
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ) :
    (∫ x in Ω, fieldIntegrand F Z θ x) =
      ∫ x in Ω, (fieldDensity F (Z (θ x)) x + fderiv ℝ θ x (familyFlux F Z (θ x) x)) :=
  setIntegral_congr_fun hfam.isOpen.measurableSet fun _ hx ↦ fieldIntegrand_eq hfam hpar hx

/-- The integrand of `J*` along the surface `z(x) = Z (θ x) x` is integrable on `Ω`. So the
integrals of the theorems below are integrals of integrable functions. This is
`ExtremalFamily.integrableOn_invariant_parameter_graph`. -/
theorem integrableOn_fieldIntegrand
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ) :
    IntegrableOn (fieldIntegrand F Z θ) Ω :=
  (integrableOn_invariant_parameter_graph hfam hpar).congr_fun
    (fun _ hx ↦ (fieldIntegrand_eq hfam hpar hx).symm) hfam.isOpen.measurableSet

/-- **Hilbert's independence theorem for a multiple integral, for a family of extremal
surfaces.** Let `Ω` be a bounded open set with `C¹` graph boundary, and let `z = Z t`,
`t ∈ J`, be solutions of the Euler–Lagrange system of `∫ F(Dz, z; x) dx` on `Ω`
(`IsExtremalFamily`). Let `θ` and `θ'` be `C¹` functions with values in `J`
(`IsGraphParameter`) that agree on the boundary of `Ω`; then the surfaces
`z(x) = Z (θ x) x` and `z'(x) = Z (θ' x) x` pass through the same boundary curve. The
integral `J* = ∫ {F(P) + (Dz - P) F_P(P)} dω` has the same value along the two surfaces.
Both integrands are integrable (`integrableOn_fieldIntegrand`).

This is `ExtremalFamily.integral_invariant_eq_of_eqOn_frontier`, through
`integral_fieldIntegrand`. -/
theorem multipleIntegral_independence
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ)
    (hpar' : IsGraphParameter Ω J θ') (hfr : EqOn θ θ' (frontier Ω)) :
    (∫ x in Ω, fieldIntegrand F Z θ x) = ∫ x in Ω, fieldIntegrand F Z θ' x := by
  rw [integral_fieldIntegrand hfam hpar, integral_fieldIntegrand hfam hpar',
    integral_invariant_eq_of_eqOn_frontier hfam hpar hpar' hfr]

/-- **Independence of the surface through a given boundary curve.** Under the hypotheses of
`multipleIntegral_independence` on the family, suppose that over every boundary point the
surfaces of the family do not meet: `t ↦ Z t x` is injective on `J`. If the surfaces
`z(x) = Z (θ x) x` and `z'(x) = Z (θ' x) x` have the same boundary values, `J*` has the same
value along both. This is Hilbert's statement, "independent of the choice of the surface
passing through the given closed twisted curve", for the parameter graphs of the family.

Equal boundary values and injectivity give equal parameters on the boundary. Without
injectivity the conclusion can fail. -/
theorem multipleIntegral_independence_of_injOn
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ)
    (hpar' : IsGraphParameter Ω J θ')
    (hinj : ∀ x ∈ frontier Ω, InjOn (fun t ↦ Z t x) J)
    (hfr : ∀ x ∈ frontier Ω, Z (θ x) x = Z (θ' x) x) :
    (∫ x in Ω, fieldIntegrand F Z θ x) = ∫ x in Ω, fieldIntegrand F Z θ' x :=
  multipleIntegral_independence hfam hpar hpar' fun x hx ↦
    hinj x hx (hpar.mapsTo (frontier_subset_closure hx))
      (hpar'.mapsTo (frontier_subset_closure hx)) (hfr x hx)

/-- **Hilbert's formula that precedes (IV).** Under the hypotheses of
`multipleIntegral_independence`, if `θ` vanishes on the boundary, so that the surface
`z(x) = Z (θ x) x` passes through the boundary curve of the surface `z̄ = Z 0` of the field,
the integral `J*` along `z` is the integral `J` of `z̄`:
`∫ {F(P) + (Dz - P) F_P(P)} dω = ∫ F(Dz̄) dω`.

This is `ExtremalFamily.integral_invariant_parameter_graph`. -/
theorem multipleIntegral_eq_lagrangianAction
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ)
    (hzero : ∀ x ∈ frontier Ω, θ x = 0) :
    (∫ x in Ω, fieldIntegrand F Z θ x) = lagrangianAction Ω F (Z 0) := by
  rw [integral_fieldIntegrand hfam hpar, integral_invariant_parameter_graph hfam hpar hzero]

/-- **Hilbert's formula (IV).** Under the hypotheses of `multipleIntegral_eq_lagrangianAction`,
the integral `J` of the surface `z(x) = Z (θ x) x` minus the integral `J` of the surface
`z̄ = Z 0` of the field is the integral of `E`:
`∫ F(Dz) dω - ∫ F(Dz̄) dω = ∫ E(Dz, P) dω`, where `P` holds the slopes at `x` of the surface
of the field through the point `(x, z(x))`. No convexity is assumed.

This is `ExtremalFamily.lagrangianAction_parameter_graph_sub_eq_integral_graphExcess`, with
`graphExcess_eq_fieldE`. -/
theorem multipleIntegral_weierstrass_formula
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ)
    (hzero : ∀ x ∈ frontier Ω, θ x = 0) :
    lagrangianAction Ω F (fun x ↦ Z (θ x) x) - lagrangianAction Ω F (Z 0) =
      ∫ x in Ω, fieldE F (Z (θ x)) x (jacobianMatrix (fun y ↦ Z (θ y) y) x) :=
  (lagrangianAction_parameter_graph_sub_eq_integral_graphExcess hfam hpar hzero).2

/-- **Weierstrass's condition for a multiple integral.** Under the hypotheses of
`multipleIntegral_eq_lagrangianAction`, if `E ≥ 0` at every point of every surface of the
field and for all values of `z_x`, `z_y`, the surface `z̄ = Z 0` of the field has the smaller
integral: `∫ F(Dz̄) dω ≤ ∫ F(Dz) dω` for every surface `z(x) = Z (θ x) x` with `θ = 0` on the
boundary.

This is `ExtremalFamily.lagrangianAction_le_parameter_graph_of_graphExcess_nonneg`, which
asks for `E ≥ 0` along the surface `z` only. The condition holds for every integrand that is
convex in the derivatives (`fieldE_nonneg_of_convexOn`). -/
theorem multipleIntegral_le_of_fieldE_nonneg
    (hfam : IsExtremalFamily Ω J F Z) (hpar : IsGraphParameter Ω J θ)
    (hzero : ∀ x ∈ frontier Ω, θ x = 0)
    (hE : ∀ t ∈ J, ∀ x ∈ Ω, ∀ P, 0 ≤ fieldE F (Z t) x P) :
    lagrangianAction Ω F (Z 0) ≤ lagrangianAction Ω F (fun x ↦ Z (θ x) x) :=
  lagrangianAction_le_parameter_graph_of_graphExcess_nonneg hfam hpar hzero fun x hx ↦
    le_of_le_of_eq (hE (θ x) (hpar.mapsTo (subset_closure hx)) x hx _)
      (graphExcess_eq_fieldE x).symm

end MultipleIntegral

section CentralField

/-- The integrand `F(y_x, y; x) = y_x² / 2`. -/
def kinetic (_z : ℝ × ℝ) (q : ℝ) : ℝ := q ^ 2 / 2

/-- The slope function of the lines through the origin: `p(x, y) = y / x`. -/
def centralSlope (z : ℝ × ℝ) : ℝ := z.2 / z.1

/-- The half plane `x > 0`. -/
def halfPlane : Set (ℝ × ℝ) := {z | 0 < z.1}

private theorem hasDerivAt_kinetic (z : ℝ × ℝ) (q : ℝ) : HasDerivAt (kinetic z) q q := by
  have h := ((hasDerivAt_id' q).mul (hasDerivAt_id' q)).mul_const (2⁻¹ : ℝ)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
  · ring
  · simp only [kinetic, Pi.mul_apply]
    ring

private theorem deriv_kinetic (z : ℝ × ℝ) (q : ℝ) : deriv (kinetic z) q = q :=
  (hasDerivAt_kinetic z q).deriv

private theorem fieldA_central : fieldA kinetic centralSlope = fun z ↦ z.2 * z.1⁻¹ := by
  funext z
  rw [fieldA, deriv_kinetic, centralSlope, div_eq_mul_inv]

private theorem fieldB_central :
    fieldB kinetic centralSlope = fun z ↦ (z.2 * z.1⁻¹) ^ 2 * 2⁻¹ := by
  funext z
  rw [fieldB, deriv_kinetic, centralSlope, kinetic, div_eq_mul_inv]
  ring

/-- An instance of the field hypotheses `IsSlopeFunction`: the lines through the origin form a
field for the integral of `y_x² / 2` on the half plane `x > 0`. Their slope function
`p = y / x` solves equation (1*): `∂(y / x)/∂x + ∂(y² / (2 x²))/∂y = -y / x² + y / x² = 0`. -/
theorem isSlopeFunction_central : IsSlopeFunction kinetic centralSlope halfPlane where
  convex := convex_halfSpace_gt (ContinuousLinearMap.fst ℝ ℝ ℝ).isLinear 0
  isOpen := isOpen_lt continuous_const continuous_fst
  differentiableAt := fun z _ ↦ (hasDerivAt_kinetic z _).differentiableAt
  differentiableOn_fieldA := by
    rw [fieldA_central]
    intro z hz
    have hx : z.1 ≠ 0 := ne_of_gt (show (0 : ℝ) < z.1 from hz)
    have h : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ w.2 * w.1⁻¹) z :=
      differentiableAt_snd.fun_mul (differentiableAt_fst.fun_inv hx)
    exact h.differentiableWithinAt
  differentiableOn_fieldB := by
    rw [fieldB_central]
    intro z hz
    have hx : z.1 ≠ 0 := ne_of_gt (show (0 : ℝ) < z.1 from hz)
    have h0 : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ w.2 * w.1⁻¹) z :=
      differentiableAt_snd.fun_mul (differentiableAt_fst.fun_inv hx)
    have h : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ (w.2 * w.1⁻¹) ^ 2 * 2⁻¹) z :=
      (h0.fun_pow 2).mul_const 2⁻¹
    exact h.differentiableWithinAt
  fieldEquation := by
    intro z hz
    have hx : z.1 ≠ 0 := ne_of_gt (show (0 : ℝ) < z.1 from hz)
    have h1 : HasDerivAt (fun x : ℝ ↦ z.2 * x⁻¹) (z.2 * -(z.1 ^ 2)⁻¹) z.1 :=
      (hasDerivAt_inv hx).const_mul z.2
    have h2 : HasDerivAt (fun y : ℝ ↦ (y * z.1⁻¹) ^ 2 * 2⁻¹)
        ((1 * z.2 + z.2 * 1) * (z.1⁻¹ ^ 2 * 2⁻¹)) z.2 := by
      have h := ((hasDerivAt_id' z.2).mul (hasDerivAt_id' z.2)).mul_const (z.1⁻¹ ^ 2 * 2⁻¹)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [Pi.mul_apply]
      ring
    simp only [FieldEquation, fieldA_central, fieldB_central]
    rw [h1.deriv, h2.deriv]
    ring

end CentralField

end PDE.HilbertProblems.TwentyThird
