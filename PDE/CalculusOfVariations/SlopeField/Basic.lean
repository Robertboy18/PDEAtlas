/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import PDE.Analysis.Convex.Differentiable.Supporting
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The invariant integral of a slope field

## Motivation

When does a solution of the Euler–Lagrange equation of `J(y) = ∫ L(x, y, y') dx` really minimize
`J` among all curves with the same endpoints, and not only among curves with nearby slopes?

## The idea

Cover a region `D` of the `(x, y)` space by curves `y' = p(x, y)`; the function `p` is the slope
field. To the field belongs the 1-form
`ω = (L(x, y, p) - L_q(x, y, p) p) dx + L_q(x, y, p) dy` on `D`, with `p = p(x, y)` and `L_q` the
derivative of `L` in the slope. Its integral over the graph of a curve `y` is the invariant
integral `∫ L(x, y, p) + L_q(x, y, p) (y' - p) dx`. If `ω` is the differential of a function `S`
(an eikonal), the invariant integral of a curve is `S(b, y(b)) - S(a, y(a))`: it depends on the
endpoints only. On a curve of the field, `y' = p`, the invariant integral is `J`. Subtracting,
`J(y) - J(y₀) = ∫ E(x, y, p, y') dx` for every curve `y` in `D` with the endpoints of the field
curve `y₀`, where `E(x, y, p, q) = L(x, y, q) - L(x, y, p) - L_q(x, y, p) (q - p)` is the excess
of `L` over its tangent plane at the slope `p`. So `E ≥ 0` makes `y₀` a minimizer in `D`.

The unknown `y` takes values in a real normed space `E`; `E = ℝ` is one unknown function and
`E = ℝ^m` is `m` of them. A curve is continuous on `[a, b]` and has the derivative `y'` off a
countable set, so curves with corners are allowed.

## Main results

Every theorem on an integral along a curve assumes that its integrand is interval integrable
along that curve.

* `IsEikonal.invariantIntegral_eq` (all fields with an eikonal, all curves in the region): the
  invariant integral equals `S(b, y(b)) - S(a, y(a))`.
* `IsEikonal.invariantIntegral_eq_of_endpoints` (all): two curves in the region with the same
  endpoints have the same invariant integral.
* `IsEikonal.integral_sub_integral_eq_integral_weierstrassExcess` (all): the representation
  `J(y) - J(y₀) = ∫ E` for a curve `y₀` of the field.
* `IsEikonal.integral_le_of_weierstrassExcess_nonneg`,
  `IsEikonal.integral_le_of_convexOn` (all): `E ≥ 0`, in particular a Lagrangian convex in the
  slope, makes the field curve a minimizer among the curves in the region with its endpoints.

## Relations

* `IsEikonal.invariantIntegral_eq_of_endpoints` is a corollary of
  `IsEikonal.invariantIntegral_eq`; the representation formula uses both and
  `invariantIntegral_eq_integral_of_field`; the two minimality theorems are corollaries of the
  representation formula, the convex one through `weierstrassExcess_nonneg_of_convexOn`, which
  is `PDE.Analysis.fderiv_apply_sub_le_sub_of_convex`.
* `PDE.CalculusOfVariations.SlopeField.exists_isEikonal_of_convex` (file `Closed`) produces the
  eikonal from a closed form on a convex region, and `isEikonal_centralField` (file
  `PDE.Examples.CalculusOfVariations.CentralField`) is a concrete eikonal.
* `PDE.CalculusOfVariations.eulerLagrange_of_curveAction_min` is the necessary condition for the
  same functional when `L` does not depend on `x`.

## What stays open

The eikonal is a premise here. Jacobi's condition, which gives a field around a given extremal,
is not formalized, and neither is strict minimality when `E > 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.CalculusOfVariations.SlopeField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The momentum of the slope field `p` for the Lagrangian `L`: the derivative of `L` in the
slope variable, at the point `z = (x, y)` and the slope `p z`. -/
def momentum (L : ℝ × E → E → ℝ) (p : ℝ × E → E) (z : ℝ × E) : E →L[ℝ] ℝ :=
  fderiv ℝ (L z) (p z)

/-- The energy of the slope field `p` for the Lagrangian `L`: `L_q(z, p) p - L(z, p)` at the
slope `p = p z`. It is the Hamiltonian of `L` at the momentum of the field. -/
def energy (L : ℝ × E → E → ℝ) (p : ℝ × E → E) (z : ℝ × E) : ℝ :=
  momentum L p z (p z) - L z (p z)

/-- The 1-form of a slope field on `ℝ × E`: `ω = L_q(z, p) dy - (L_q(z, p) p - L(z, p)) dx`. -/
def beltramiForm (L : ℝ × E → E → ℝ) (p : ℝ × E → E) (z : ℝ × E) : ℝ × E →L[ℝ] ℝ :=
  (momentum L p z).comp (ContinuousLinearMap.snd ℝ ℝ E) -
    energy L p z • ContinuousLinearMap.fst ℝ ℝ E

/-- The excess of `f` at the slope `q` over its tangent plane at the slope `p`:
`E(p, q) = f q - f p - f'(p) (q - p)`. -/
def weierstrassExcess (f : E → ℝ) (p q : E) : ℝ :=
  f q - f p - fderiv ℝ f p (q - p)

/-- The invariant integral of the slope field `p` along the curve `y` with derivative `y'`:
the integral of the form of the field over the graph of `y`. -/
def invariantIntegral (L : ℝ × E → E → ℝ) (p : ℝ × E → E) (a b : ℝ) (y y' : ℝ → E) : ℝ :=
  ∫ x in a..b, beltramiForm L p (x, y x) (1, y' x)

/-- A curve in the region `D` over `[a, b]`: `y` is continuous on `[a, b]`, has the derivative
`y'` at the points of `(a, b)` off a countable set, and its graph lies in `D`. -/
structure IsCurveIn (D : Set (ℝ × E)) (a b : ℝ) (y y' : ℝ → E) : Prop where
  /-- The curve is continuous on the closed interval. -/
  continuousOn : ContinuousOn y (Icc a b)
  /-- The curve has the derivative `y'` off a countable set. -/
  hasDerivAt : ∃ s : Set ℝ, s.Countable ∧ ∀ x ∈ Ioo a b \ s, HasDerivAt y (y' x) x
  /-- The graph of the curve lies in the region. -/
  mem : ∀ x ∈ Icc a b, (x, y x) ∈ D

/-- `S` is an eikonal of the slope field `p` on the region `D`: at every point of `D` its
differential is the form of the field. -/
def IsEikonal (L : ℝ × E → E → ℝ) (p : ℝ × E → E) (D : Set (ℝ × E)) (S : ℝ × E → ℝ) : Prop :=
  ∀ z ∈ D, HasFDerivAt S (beltramiForm L p z) z

variable {L : ℝ × E → E → ℝ} {p : ℝ × E → E} {D : Set (ℝ × E)} {S : ℝ × E → ℝ}
  {a b : ℝ} {y y' y₀ y₀' : ℝ → E}

/-- The form of the field on a vector `(t, v)`. -/
theorem beltramiForm_apply (z v : ℝ × E) :
    beltramiForm L p z v = momentum L p z v.2 - energy L p z * v.1 := by
  simp [beltramiForm]

/-- On the velocity `(1, q)` of a graph, the form of the field is the value at `q` of the
tangent plane of `L` at the slope of the field. -/
theorem beltramiForm_one (z : ℝ × E) (q : E) :
    beltramiForm L p z (1, q) = L z (p z) + momentum L p z (q - p z) := by
  rw [beltramiForm_apply, energy, map_sub]
  ring

/-- On the velocity of a curve of the field, the form of the field is the Lagrangian. -/
theorem beltramiForm_one_field (z : ℝ × E) :
    beltramiForm L p z (1, p z) = L z (p z) := by
  rw [beltramiForm_one, sub_self, map_zero, add_zero]

/-- The Lagrangian is the form of the field on the velocity plus the excess. -/
theorem beltramiForm_one_add_weierstrassExcess (z : ℝ × E) (q : E) :
    beltramiForm L p z (1, q) + weierstrassExcess (L z) (p z) q = L z q := by
  rw [beltramiForm_one, weierstrassExcess, momentum]
  ring

/-- A function convex in the slope has nonnegative excess at every slope where it is
differentiable: the tangent plane lies below the graph. -/
theorem weierstrassExcess_nonneg_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ univ f) {p : E}
    (hd : DifferentiableAt ℝ f p) (q : E) : 0 ≤ weierstrassExcess f p q := by
  have h := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hf hd.hasFDerivAt q
    (mem_univ _) (mem_univ _)
  unfold weierstrassExcess
  linarith

/-- The invariant integral of a slope field with an eikonal `S` depends on the endpoints only:
it is `S(b, y(b)) - S(a, y(a))` for every curve `y` in the region along which the integrand is
interval integrable. The proof differentiates
`x ↦ S(x, y(x))`, whose derivative is the form of the field on the velocity `(1, y'(x))`, and
applies the fundamental theorem of calculus off a countable set. -/
theorem IsEikonal.invariantIntegral_eq (hS : IsEikonal L p D S) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y')
    (hint : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y x) (1, y' x)) volume a b) :
    invariantIntegral L p a b y y' = S (b, y b) - S (a, y a) := by
  obtain ⟨s, hs, hd⟩ := hy.hasDerivAt
  refine integral_eq_of_hasDerivAt_off_countable_of_le (fun x ↦ S (x, y x)) _ hab hs ?_ ?_ hint
  · -- `x ↦ S(x, y(x))` is continuous on `[a, b]`
    intro x hx
    have hc : ContinuousWithinAt (fun x ↦ (x, y x)) (Icc a b) x :=
      continuousWithinAt_id.prodMk (hy.continuousOn x hx)
    exact ContinuousAt.comp_continuousWithinAt (f := fun x ↦ (x, y x))
      (hS _ (hy.mem x hx)).continuousAt hc
  · -- its derivative is the form on the velocity of the graph
    intro x hx
    exact HasFDerivAt.comp_hasDerivAt x (hS _ (hy.mem x (Ioo_subset_Icc_self hx.1)))
      ((hasDerivAt_id x).prodMk (hd x hx))

/-- The invariant integral of a slope field with an eikonal is independent of the path: two
curves in the region with the same endpoints, along which the integrand is interval
integrable, have the same invariant integral. -/
theorem IsEikonal.invariantIntegral_eq_of_endpoints (hS : IsEikonal L p D S) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hint : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y x) (1, y' x)) volume a b)
    (hint₀ : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y₀ x) (1, y₀' x)) volume a b)
    (ha : y a = y₀ a) (hb : y b = y₀ b) :
    invariantIntegral L p a b y y' = invariantIntegral L p a b y₀ y₀' := by
  rw [hS.invariantIntegral_eq hab hy hint, hS.invariantIntegral_eq hab hy₀ hint₀, ha, hb]

/-- Almost every point of the interval is an interior point where a curve of the field has the
slope of the field, so the form on the velocity is the Lagrangian there. -/
private theorem ae_beltramiForm_eq_of_field (hab : a ≤ b)
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) :
    ∀ᵐ x ∂volume, x ∈ Ι a b →
      beltramiForm L p (x, y₀ x) (1, y₀' x) = L (x, y₀ x) (y₀' x) := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with x hxb hx
  rw [uIoc_of_le hab] at hx
  rw [hfield x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩, beltramiForm_one_field]

/-- Along a curve of the field the invariant integral is the integral of the Lagrangian. -/
theorem invariantIntegral_eq_integral_of_field (hab : a ≤ b)
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) :
    invariantIntegral L p a b y₀ y₀' = ∫ x in a..b, L (x, y₀ x) (y₀' x) :=
  intervalIntegral.integral_congr_ae (ae_beltramiForm_eq_of_field hab hfield)

/-- The representation formula: for a slope field with an eikonal, a curve `y₀` of the field
and any curve `y` in the region with the endpoints of `y₀`,
`J(y) - J(y₀) = ∫ E(x, y, p(x, y), y') dx`, when `L` along both curves and the integrand of
the invariant integral along `y` are interval integrable. The invariant integral of `y` equals
that of `y₀`, which is `J(y₀)`, and `L` minus the integrand of the invariant integral is the
excess. -/
theorem IsEikonal.integral_sub_integral_eq_integral_weierstrassExcess
    (hS : IsEikonal L p D S) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hLy : IntervalIntegrable (fun x ↦ L (x, y x) (y' x)) volume a b)
    (hint : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y x) (1, y' x)) volume a b)
    (hLy₀ : IntervalIntegrable (fun x ↦ L (x, y₀ x) (y₀' x)) volume a b) :
    (∫ x in a..b, L (x, y x) (y' x)) - ∫ x in a..b, L (x, y₀ x) (y₀' x) =
      ∫ x in a..b, weierstrassExcess (L (x, y x)) (p (x, y x)) (y' x) := by
  have hint₀ : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y₀ x) (1, y₀' x))
      volume a b := by
    refine hLy₀.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact (ae_beltramiForm_eq_of_field hab hfield).mono fun x hx hmem ↦ (hx hmem).symm
  rw [← invariantIntegral_eq_integral_of_field hab hfield,
    ← hS.invariantIntegral_eq_of_endpoints hab hy hy₀ hint hint₀ ha hb, invariantIntegral,
    ← intervalIntegral.integral_sub hLy hint]
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  simp only [← beltramiForm_one_add_weierstrassExcess (p := p) (x, y x) (y' x)]
  ring

/-- A sufficient condition for a minimum: if the excess is nonnegative along the curve `y`, the
curve `y₀` of the field has `J(y₀) ≤ J(y)`, under the integrability assumptions of the
representation formula. -/
theorem IsEikonal.integral_le_of_weierstrassExcess_nonneg
    (hS : IsEikonal L p D S) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hLy : IntervalIntegrable (fun x ↦ L (x, y x) (y' x)) volume a b)
    (hint : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y x) (1, y' x)) volume a b)
    (hLy₀ : IntervalIntegrable (fun x ↦ L (x, y₀ x) (y₀' x)) volume a b)
    (hE : ∀ x ∈ Icc a b, 0 ≤ weierstrassExcess (L (x, y x)) (p (x, y x)) (y' x)) :
    ∫ x in a..b, L (x, y₀ x) (y₀' x) ≤ ∫ x in a..b, L (x, y x) (y' x) := by
  rw [← sub_nonneg, hS.integral_sub_integral_eq_integral_weierstrassExcess hab hy hy₀ hfield
    ha hb hLy hint hLy₀]
  exact intervalIntegral.integral_nonneg hab hE

/-- A curve of a slope field with an eikonal minimizes `J` among the curves in the region with
its endpoints, when the Lagrangian is convex in the slope at every point of the region and
differentiable at the slope of the field, under the integrability assumptions of the
representation formula. No bound on the slopes of the competitor is needed. -/
theorem IsEikonal.integral_le_of_convexOn
    (hS : IsEikonal L p D S) (hab : a ≤ b)
    (hy : IsCurveIn D a b y y') (hy₀ : IsCurveIn D a b y₀ y₀')
    (hfield : ∀ x ∈ Ioo a b, y₀' x = p (x, y₀ x)) (ha : y a = y₀ a) (hb : y b = y₀ b)
    (hLy : IntervalIntegrable (fun x ↦ L (x, y x) (y' x)) volume a b)
    (hint : IntervalIntegrable (fun x ↦ beltramiForm L p (x, y x) (1, y' x)) volume a b)
    (hLy₀ : IntervalIntegrable (fun x ↦ L (x, y₀ x) (y₀' x)) volume a b)
    (hconvex : ∀ z ∈ D, ConvexOn ℝ univ (L z))
    (hdiff : ∀ z ∈ D, DifferentiableAt ℝ (L z) (p z)) :
    ∫ x in a..b, L (x, y₀ x) (y₀' x) ≤ ∫ x in a..b, L (x, y x) (y' x) :=
  hS.integral_le_of_weierstrassExcess_nonneg hab hy hy₀ hfield ha hb hLy hint hLy₀
    fun x hx ↦ weierstrassExcess_nonneg_of_convexOn (hconvex _ (hy.mem x hx))
      (hdiff _ (hy.mem x hx)) _

end PDE.CalculusOfVariations.SlopeField
