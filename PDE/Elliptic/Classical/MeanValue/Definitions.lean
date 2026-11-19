/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall

/-!
# Spherical mean-value property

The spherical mean-value property used in the classical theory of harmonic functions.
Euclidean sphere integration and averaging are in `PDE.Analysis`; only the
equation-specific predicate belongs to the `LaplacianEquation` namespace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, Theorem 2 (Mean-value formulas for Laplace's
  equation), (16), p. 25.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open PDE.Analysis

/-- A function has the spherical mean-value property on `U` when its value at
each point equals its average on every sphere whose closed ball lies in `U`. -/
def HasSphereMeanValueProperty (n : ℕ)
    (u : ℝ^n → ℝ) (U : Set (ℝ^n)) : Prop :=
  ∀ x ∈ U, ∀ r : ℝ, 0 < r →
    Metric.closedBall x r ⊆ U → u x = sphereAverage n u x r

/-- Apply the spherical mean-value property to one admissible closed ball. -/
theorem HasSphereMeanValueProperty.apply {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    {x : ℝ^n} (hx : x ∈ U)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U) :
    u x = sphereAverage n u x r :=
  hu x hx r hr hball

/-- The spherical mean-value property restricts to a smaller domain. -/
theorem HasSphereMeanValueProperty.mono {n : ℕ}
    {u : ℝ^n → ℝ} {V U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) (hVU : V ⊆ U) :
    HasSphereMeanValueProperty n u V := by
  intro x hx r hr hball
  exact hu x (hVU hx) r hr fun y hy ↦ hVU (hball hy)

/-- Restrict the spherical mean-value property to an open ball contained in
the original domain. -/
theorem HasSphereMeanValueProperty.on_ball {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    {x : ℝ^n} {r : ℝ} (hball : Metric.ball x r ⊆ U) :
    HasSphereMeanValueProperty n u (Metric.ball x r) :=
  hu.mono hball

/-- Restrict the spherical mean-value property to a closed ball contained in
the original domain. -/
theorem HasSphereMeanValueProperty.on_closedBall {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    {x : ℝ^n} {r : ℝ} (hball : Metric.closedBall x r ⊆ U) :
    HasSphereMeanValueProperty n u (Metric.closedBall x r) :=
  hu.mono hball

end LaplacianEquation
