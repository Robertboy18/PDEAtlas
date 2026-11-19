/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Differentiation.Coordinate


/-!
# The scalar analytic Cauchy equation

The coefficient arguments consist of every mixed derivative below the
equation order and every position coordinate. The normalized right-hand side
uses the Euclidean coordinate derivatives `coordinateDeriv`. Both the argument map and
the right-hand side are analytic when evaluated on an analytic scalar function.

Equating the pure time derivative of order `k` with `rightHandSide a b u` gives the quasilinear
equation (1) of Evans, §4.6.1, solved for that derivative as in (5), with time in place of `xₙ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1, (1) and (5), pp. 232-234.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Topology
open Filter PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0}
local notation "A" => J ⊕ Fin (d + 1)

/-- All lower coordinate jets and all coordinates of the evaluation point. -/
def arguments (k : ℕ) (u : ℝ^(d + 1) → ℝ) (x : ℝ^(d + 1)) :
    ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) → ℝ :=
  Sum.elim (fun α ↦ coordinateDeriv α.2 u x) (fun i ↦ x i)

/-- The normalized scalar equation, solved for its highest pure time derivative. -/
def rightHandSide (a : T → (A → ℝ) → ℝ) (b : (A → ℝ) → ℝ)
    (u : ℝ^(d + 1) → ℝ) (x : ℝ^(d + 1)) : ℝ :=
  (∑ α, a α (arguments k u x) * coordinateDeriv α.1 u x) + b (arguments k u x)

/-- Analyticity of a scalar function makes its entire finite jet argument analytic. -/
theorem analyticAt_arguments {u : ℝ^(d + 1) → ℝ} {x : ℝ^(d + 1)}
    (hu : AnalyticAt ℝ u x) :
    AnalyticAt ℝ (arguments k u) x := by
  apply AnalyticAt.pi
  intro α
  cases α with
  | inl α => exact analyticAt_coordinateDeriv hu α.2
  | inr i => exact (EuclideanSpace.proj i : ℝ^(d + 1) →L[ℝ] ℝ).analyticAt x

/-- Analytic coefficients and an analytic unknown whose jet argument vanishes at
the origin give a right-hand side that is analytic at the origin. -/
theorem analyticAt_rightHandSide
    {a : T → (A → ℝ) → ℝ} {b : (A → ℝ) → ℝ}
    {u : ℝ^(d + 1) → ℝ}
    (ha : ∀ α, AnalyticAt ℝ (a α) 0) (hb : AnalyticAt ℝ b 0)
    (hu : AnalyticAt ℝ u 0) (hu0 : arguments k u 0 = 0) :
    AnalyticAt ℝ (rightHandSide a b u) 0 := by
  have harg := analyticAt_arguments (k := k) hu
  apply AnalyticAt.add
  · exact Finset.univ.analyticAt_fun_sum fun α _ ↦
      ((ha α).comp_of_eq harg hu0).mul (analyticAt_coordinateDeriv hu α.1)
  · exact hb.comp_of_eq harg hu0

end PDE.Cauchy.Quasilinear.Analytic
