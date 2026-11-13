/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import CAS.IntegrationTactic

/-!
# One-dimensional harmonic functions and the mean-value property

A one-dimensional harmonic function, a `C²` function with `u'' = 0` on `U` (`IsHarmonicPDE`), is
affine on every closed interval `[x - r, x + r] ⊆ U`
(`IsHarmonicPDE.exists_eq_affineOn_closedBall`). It therefore has the sphere mean-value property
`u(x) = (u(x + r) + u(x - r))/2` (`IsHarmonicPDE.hasSphereMeanValueProperty`) and the ball
mean-value property for the average over `[x - r, x + r]`
(`IsHarmonicPDE.hasBallMeanValueProperty`). SymLean's `cas` tactic computes the derivative of
`y ↦ c y` and the integral of an affine function.

This is the case `n = 1` of Evans's §2.2.2, Theorem 2, (16), where the sphere `∂B(x, r)` is the pair
`{x - r, x + r}`. Evans proves that the sphere average is constant in `r` by differentiating it; in
one dimension the affine form gives both averages directly. The implication in every dimension is
`PDE.Elliptic.Classical.MeanValue.PDEToMeanValue`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, Theorem 2 (Mean-value formulas), (16), and its proof,
  pp. 25-26.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace Laplace1D

open scoped BigOperators

open scoped Interval

/-! ## Predicates and averages

These scalar predicates are separate from the generic `ℝ^1` ones. The sphere average is the
arithmetic mean of the two endpoints and the ball average is an interval integral.
-/

/-- 1D harmonicity in the PDE sense: `u ∈ C²(U)` and `u'' = 0` on `U`. -/
def IsHarmonicPDE (u : ℝ → ℝ) (U : Set ℝ) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ∀ x ∈ U, deriv (deriv u) x = 0

/-- A one-dimensional harmonic PDE solution is `C²` on its domain. -/
theorem IsHarmonicPDE.contDiffOn {u : ℝ → ℝ} {U : Set ℝ}
    (hu : IsHarmonicPDE u U) :
    ContDiffOn ℝ 2 u U :=
  hu.1

/-- The second derivative of a one-dimensional harmonic PDE solution vanishes on its domain. -/
theorem IsHarmonicPDE.deriv_deriv_eq_zero {u : ℝ → ℝ} {U : Set ℝ}
    (hu : IsHarmonicPDE u U) {x : ℝ} (hx : x ∈ U) :
    deriv (deriv u) x = 0 :=
  hu.2 x hx

/-- 1D "sphere average" over the sphere `∂B(x,r) = {x-r, x+r}`. -/
noncomputable def sphereAverage (u : ℝ → ℝ) (x r : ℝ) : ℝ :=
  if _hr : r = 0 then u x else (u (x + r) + u (x - r)) / 2

/-- Sphere mean value property on a set `U` (1D version). -/
def HasSphereMeanValueProperty (u : ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∀ r : ℝ, 0 < r → Metric.closedBall x r ⊆ U → u x = sphereAverage u x r

/-- Projection from the one-dimensional sphere mean-value property at a chosen center and radius. -/
theorem HasSphereMeanValueProperty.apply {u : ℝ → ℝ} {U : Set ℝ}
    (hu : HasSphereMeanValueProperty u U) {x r : ℝ}
    (hx : x ∈ U) (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U) :
    u x = sphereAverage u x r :=
  hu x hx r hr hball

/-- 1D "ball average" over `closedBall x r = [x-r, x+r]`, using the interval integral. -/
noncomputable def ballAverage (u : ℝ → ℝ) (x r : ℝ) : ℝ :=
  if _hr : r = 0 then u x else (1 / (2 * r)) * ∫ y in (x - r)..(x + r), u y

/-- Ball mean value property on a set `U` (1D version). -/
def HasBallMeanValueProperty (u : ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∀ r : ℝ, 0 < r → Metric.closedBall x r ⊆ U → u x = ballAverage u x r

/-- Projection from the one-dimensional ball mean-value property at a chosen center and radius. -/
theorem HasBallMeanValueProperty.apply {u : ℝ → ℝ} {U : Set ℝ}
    (hu : HasBallMeanValueProperty u U) {x r : ℝ}
    (hx : x ∈ U) (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U) :
    u x = ballAverage u x r :=
  hu x hx r hr hball

/-! ## PDE ⇒ mean value (1D) -/

/-- A `C²` one-dimensional harmonic function is affine on every closed interval contained in
the domain. Both one-dimensional mean-value properties follow from this. -/
theorem IsHarmonicPDE.exists_eq_affineOn_closedBall {u : ℝ → ℝ} {U : Set ℝ} (hu : IsHarmonicPDE u U)
    (x : ℝ) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U) :
    ∃ c a0 : ℝ, ∀ y ∈ Metric.closedBall x r, u y = c * y + a0 := by
  set s : Set ℝ := Set.Ioo (x - r) (x + r)
  have hclosure : closure s = Metric.closedBall x r := by
    rw [closure_Ioo (by linarith : x - r < x + r).ne, Real.closedBall_eq_Icc]
  have hsU : s ⊆ U := subset_closure.trans (hclosure ▸ hball)
  have hu2 : ContDiffOn ℝ 2 u s := hu.contDiffOn.mono hsU
  have hu1 : DifferentiableOn ℝ u s := hu2.differentiableOn (by norm_num)
  have hx : x ∈ s := ⟨by linarith, by linarith⟩
  let c : ℝ := deriv u x
  have hderiv (y : ℝ) (hy : y ∈ s) : deriv u y = c :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      ((((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1
        (by convert hu2 using 1; norm_num)).2.2).differentiableOn one_ne_zero)
      (fun z hz ↦ hu.deriv_deriv_eq_zero (hsU hz)) hy hx
  have hv (y : ℝ) (hy : y ∈ s) : u y - c * y = u x - c * x := by
    refine isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun y ↦ u y - c * y) isPreconnected_Ioo
      (hu1.sub (by fun_prop)) (fun z hz ↦ ?_) hy hx
    have hlin : deriv (fun y ↦ c * y) z = c := by
      cas
    rw [deriv_fun_sub (hu1.differentiableAt (isOpen_Ioo.mem_nhds hz)) (by fun_prop), hlin,
      hderiv z hz, sub_self, Pi.zero_apply]
  refine ⟨c, u x - c * x, fun y hy ↦ ?_⟩
  have := Set.EqOn.of_subset_closure (f := fun y ↦ u y - c * y) (g := fun _ ↦ u x - c * x) hv
    ((hu.contDiffOn.continuousOn.sub (by fun_prop)).mono (hclosure ▸ hball)) continuousOn_const
    subset_closure le_rfl (hclosure ▸ hy)
  linarith

/-- A one-dimensional harmonic function satisfies the sphere mean-value property:
`u x = (u (x + r) + u (x - r)) / 2` whenever `[x - r, x + r] ⊆ U`. Since `u` is affine on that
interval by `IsHarmonicPDE.exists_eq_affineOn_closedBall`, this says that its midpoint value is
the average of its endpoint values. -/
theorem IsHarmonicPDE.hasSphereMeanValueProperty {u : ℝ → ℝ} {U : Set ℝ}
    (hu : IsHarmonicPDE u U) :
    HasSphereMeanValueProperty u U := by
  intro x hx r hr hball
  obtain ⟨c, a0, haff⟩ := hu.exists_eq_affineOn_closedBall x r hr hball
  have hmem (y : ℝ) (h₁ : x - r ≤ y) (h₂ : y ≤ x + r) : y ∈ Metric.closedBall x r := by
    rw [Real.closedBall_eq_Icc]
    exact ⟨h₁, h₂⟩
  rw [haff x (hmem x (by linarith) (by linarith))]
  simp only [sphereAverage, dite_eq_right hr.ne']
  rw [haff (x + r) (hmem _ (by linarith) le_rfl), haff (x - r) (hmem _ le_rfl (by linarith))]
  ring

/-- A one-dimensional harmonic function satisfies the ball mean-value property on its domain. -/
theorem IsHarmonicPDE.hasBallMeanValueProperty {u : ℝ → ℝ} {U : Set ℝ} (hu : IsHarmonicPDE u U) :
    HasBallMeanValueProperty u U := by
  intro x hx r hr hball
  obtain ⟨c, a0, haff⟩ := hu.exists_eq_affineOn_closedBall x r hr hball
  have hint : (∫ y in (x - r)..(x + r), u y) = ∫ y in (x - r)..(x + r), c * y + a0 :=
    intervalIntegral.integral_congr fun y hy ↦ haff y (by
      rwa [Set.uIcc_of_le (by linarith), ← Real.closedBall_eq_Icc] at hy)
  have hlin : (∫ y in (x - r)..(x + r), c * y + a0) = c * (2 * x * r) + a0 * (2 * r) := by
    cas
  rw [haff x (Metric.mem_closedBall_self hr.le)]
  simp only [ballAverage, hr.ne', ↓reduceDIte, hint, hlin]
  field_simp

end Laplace1D
