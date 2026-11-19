/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Equation
import PDE.FDeriv.Operators

/-!
# Clairaut's nonlinear first-order equation

For the equation

`x · Du + f(Du) = u`,

the affine family `u(x; a) = a · x + f(a)` satisfies the residual equation. The rank
condition making it a complete integral is proved in `CompleteIntegral.Clairaut`. This is
Example 1 of Evans, §3.1.1, equations (4)-(5).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.1.1, Example 1, equations (4)-(5).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (partialDeriv)

namespace NonlinearFirstOrder

open scoped RealInnerProductSpace

variable {n : ℕ}

private theorem partialDeriv_inner_add_const (a : ℝ^n) (c : ℝ) (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y : ℝ^n ↦ ⟪a, y⟫ + c)) x = a i := by
  unfold partialDeriv
  have hdiffL : DifferentiableAt ℝ (fun y : ℝ^n ↦ ⟪a, y⟫) x := by
    simpa using (innerSL ℝ a).differentiableAt
  have hdiffC : DifferentiableAt ℝ (fun _ : ℝ^n ↦ c) x := by
    simp
  have hfderiv_add := fderiv_add (𝕜 := ℝ) (x := x) (f := fun y : ℝ^n ↦ ⟪a, y⟫) (g := fun _ ↦ c)
      hdiffL hdiffC
  have hfderivL : fderiv ℝ (fun y : ℝ^n ↦ ⟪a, y⟫) x =
        innerSL ℝ a := by
    simpa only [coe_innerSL_apply] using (ContinuousLinearMap.fderiv (innerSL ℝ a) (x := x))
  have hfderivC : fderiv ℝ (fun _ : ℝ^n ↦ c) x = 0 := by
    simp
  -- The derivative of the constant term vanishes, so evaluation on `eᵢ`
  -- extracts the corresponding coordinate of `a`.
  have : fderiv ℝ (fun y : ℝ^n ↦ ⟪a, y⟫ + c) x (EuclideanSpace.single i (1 : ℝ)) =
        (innerSL ℝ a) (EuclideanSpace.single i (1 : ℝ)) := by
    simp [hfderivL, innerSL_apply_apply]
  simpa [EuclideanSpace.inner_single_right] using this

private theorem gradient_inner_add_const (a : ℝ^n) (c : ℝ) (x : ℝ^n) :
    ∇ (fun y : ℝ^n ↦ ⟪a, y⟫ + c) x = a := by
  ext i
  rw [PDE.gradient_apply_eq_partialDeriv]
  exact partialDeriv_inner_add_const (n := n) a c i x

section Clairaut

variable [Fact (0 < n)]

/-- Clairaut's equation: `x · Du + f(Du) = u`. -/
noncomputable def clairautEquation
    (f : ℝ^n → ℝ) : Equation n where
  F := fun p z x ↦ ⟪x, p⟫ + f p - z
  domain := Set.univ

/-- The affine solution family to Clairaut's equation: `u(x; a) = a · x + f(a)`. -/
noncomputable def clairautSolution
    (f : ℝ^n → ℝ) (a : ℝ^n) :
    ℝ^n → ℝ :=
  fun x ↦ ⟪a, x⟫ + f a

/-- Every member of the affine Clairaut family is a classical solution. -/
theorem clairautSolution_isClassicalSolution (f : ℝ^n → ℝ) (a : ℝ^n) :
    IsClassicalSolution (n := n) (clairautEquation (n := n) f) (clairautSolution (n := n) f a) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · unfold clairautSolution
    exact (innerSL ℝ a).differentiableAt.add (differentiableAt_const (c := f a))
  have hgrad : ∇ (clairautSolution (n := n) f a) x = a := by
    unfold clairautSolution
    exact gradient_inner_add_const (n := n) a (f a) x
  simp [clairautEquation, clairautSolution, hgrad, real_inner_comm]

end Clairaut

end NonlinearFirstOrder
