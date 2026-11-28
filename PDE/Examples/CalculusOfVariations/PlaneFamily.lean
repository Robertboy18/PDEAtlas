/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.Comparison
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A family of planes for Dirichlet's integral on the disk

## Motivation

Are the premises of the comparison theorems for a family of extremals satisfiable? What do the
theorems say for the simplest double integral, Dirichlet's `∬ (p² + q²) / 2 dx dy`, and a simple
family of extremal surfaces, the parallel planes `z = t + x`?

## The idea

Every plane `z = t + x` solves the Euler–Lagrange equation of Dirichlet's integral, and the
planes cover the whole space. Their slopes are `(1, 0)` (`jacobianMatrix_plane`); a hand
calculation, not done in Lean, gives the flux `(1, 0)` of the family, which is not zero.
A function `θ` on the unit disk that vanishes on the circle is the parameter of the surface
`z = θ(x, y) + x`, which meets the plane `z = x` along its boundary curve. The premises hold
for every `C¹` function `θ` of this kind; `bump = 1 - x² - y²` is one. The integrand is a
polynomial, so its closure jets are continuous, and it is convex in `(p, q)`.

## Main results

All are for one integrand, one family and one parameter.

* `isExtremalFamily_plane`, `isGraphParameter_bump`: the planes are a family of extremals in
  the sense of `IsExtremalFamily`, and `bump` is a parameter in the sense of
  `IsGraphParameter` that vanishes on the circle (`bump_eq_zero_of_mem_frontier`).
* `action_bump_sub_eq_integral_graphExcess`: Weierstrass's formula for the surface
  `z = bump + x` over the field of planes.
* `action_plane_le_action_bump`: the plane `z = x` has no larger Dirichlet integral than the
  surface `z = bump + x`.
* `integral_invariant_bump_add_const`: the invariant integral has the same value for the
  parameters `bump + c` and `c`, which agree on the circle and do not vanish there for
  `c ≠ 0`.

## Relations

* The three results are `lagrangianAction_parameter_graph_sub_eq_integral_graphExcess`,
  `lagrangianAction_le_parameter_graph_of_closureJets` and
  `integral_invariant_eq_of_eqOn_frontier` with every premise instantiated.

## What stays open

Nothing here is more than an example. The integrals are not evaluated.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Matrix.Norms.Elementwise

namespace PDE.Examples.PlaneFamily

open Analysis CalculusOfVariations CalculusOfVariations.ExtremalFamily
  CalculusOfVariations.Noether SobolevSpace

/-- Dirichlet's integrand for one unknown function of two variables: `(p² + q²) / 2`, where
`p` and `q` are the entries of the one row of the matrix of derivatives. -/
def dirichlet (P : Matrix (Fin 1) (Fin 2) ℝ) (_z : ℝ^1) (_x : ℝ^2) : ℝ :=
  (P 0 0 ^ 2 + P 0 1 ^ 2) / 2

/-- The plane `z = t + x`, with slope `1` in the first variable and `0` in the second. -/
def plane (t : ℝ) (x : ℝ^2) : ℝ^1 := WithLp.toLp 2 ![t + x 0]

/-- A parameter that vanishes on the unit circle: `1 - x² - y²`. -/
def bump (x : ℝ^2) : ℝ := 1 - (x 0 ^ 2 + x 1 ^ 2)

/-- Dirichlet's integrand is smooth in all its variables. -/
theorem contDiff_dirichlet : ContDiff ℝ 2
    (fun a : Matrix (Fin 1) (Fin 2) ℝ × (ℝ^1 × ℝ^2) ↦ dirichlet a.1 a.2.1 a.2.2) := by
  have h (i : Fin 2) : ContDiff ℝ 2
      (fun a : Matrix (Fin 1) (Fin 2) ℝ × (ℝ^1 × ℝ^2) ↦ a.1 0 i) :=
    (contDiff_apply_apply ℝ (0 : Fin 1) i).comp contDiff_fst
  exact (((h 0).pow 2).add ((h 1).pow 2)).div_const 2

/-- The family of planes is smooth in the point and the parameter. -/
theorem contDiff_plane : ContDiff ℝ 2 (fun p : ℝ^2 × ℝ ↦ plane p.2 p.1) := by
  apply (contDiff_piLp 2).mpr
  intro k
  fin_cases k
  exact contDiff_snd.add
    ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.comp contDiff_fst)

/-- The parameter is smooth. -/
theorem contDiff_bump : ContDiff ℝ 1 bump :=
  contDiff_const.sub
    ((((EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).contDiff).pow 2).add
      (((EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).contDiff).pow 2))

/-- The parameter vanishes on the unit circle. -/
theorem bump_eq_zero_of_mem_frontier (x : ℝ^2) (hx : x ∈ frontier (ball (0 : ℝ^2) 1)) :
    bump x = 0 := by
  have hxnorm : ‖x‖ = 1 := by
    simpa [frontier_ball (0 : ℝ^2) one_ne_zero, mem_sphere, dist_zero_right] using hx
  have hs : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    simpa [Fin.sum_univ_two, hxnorm] using (EuclideanSpace.real_norm_sq_eq x).symm
  rw [bump, hs, sub_self]

/-- Every plane of the family has the matrix of derivatives `(1, 0)`. -/
theorem jacobianMatrix_plane (t : ℝ) (x : ℝ^2) :
    jacobianMatrix (plane t) x = Matrix.of fun _ i ↦ if i = 0 then 1 else 0 := by
  ext k i
  have h : HasFDerivAt (fun y : ℝ^2 ↦ plane t y k)
      (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ) x := by
    fin_cases k
    exact (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt.const_add t
  change fderiv ℝ (fun y ↦ plane t y k) x _ = _
  rw [h.fderiv]
  fin_cases i <;> simp

/-- Every plane solves the Euler–Lagrange equation of Dirichlet's integral. -/
theorem classicalEulerLagrange_plane (t : ℝ) (x : ℝ^2) (k : Fin 1) :
    classicalEulerLagrange dirichlet (plane t) x k = 0 := by
  simp [classicalEulerLagrange, jacobianMatrix_plane, dirichlet]

/-- Dirichlet's integrand is convex in the derivatives. -/
theorem convexOn_dirichlet (z : ℝ^1) (x : ℝ^2) :
    ConvexOn ℝ univ fun P ↦ dirichlet P z x := by
  refine ⟨convex_univ, fun P _ Q _ t r ht hr htr ↦ ?_⟩
  simp only [dirichlet, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hr' : r = 1 - t := by linarith
  subst hr'
  nlinarith [mul_nonneg ht hr, sq_nonneg (P 0 0 - Q 0 0), sq_nonneg (P 0 1 - Q 0 1)]

/-- The planes `z = t + x` are a family of extremals of Dirichlet's integral on the unit disk,
with every real parameter. -/
theorem isExtremalFamily_plane :
    IsExtremalFamily (ball (0 : ℝ^2) 1) univ dirichlet plane where
  isOpen := isOpen_ball
  isBounded := isBounded_ball
  graphBoundary := (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl
  isOpen_parameter := isOpen_univ
  ordConnected := ordConnected_univ
  zero_mem := mem_univ 0
  density := ⟨ContinuousSecondJetOn.ofContDiff contDiff_dirichlet _⟩
  family := ⟨ContinuousSecondJetOn.ofContDiff contDiff_plane _⟩
  eulerLagrange := fun t _ x _ k ↦ classicalEulerLagrange_plane t x k

/-- The function `1 - x² - y²` is the parameter of a graph over the unit disk. -/
theorem isGraphParameter_bump : IsGraphParameter (ball (0 : ℝ^2) 1) univ bump where
  contDiff := contDiff_bump
  mapsTo := mapsTo_univ _ _

/-- Weierstrass's formula for the surface `z = 1 - x² - y² + x` over the field of planes
`z = t + x`: its Dirichlet integral over the unit disk minus that of the plane `z = x` is the
integral of the excess. -/
theorem action_bump_sub_eq_integral_graphExcess :
    lagrangianAction (ball (0 : ℝ^2) 1) dirichlet (fun x ↦ plane (bump x) x) -
        lagrangianAction (ball (0 : ℝ^2) 1) dirichlet (plane 0) =
      ∫ x in ball (0 : ℝ^2) 1, graphExcess dirichlet plane bump x :=
  (lagrangianAction_parameter_graph_sub_eq_integral_graphExcess isExtremalFamily_plane
    isGraphParameter_bump bump_eq_zero_of_mem_frontier).2

/-- The plane `z = x` has no larger Dirichlet integral over the unit disk than the surface
`z = 1 - x² - y² + x`, which has the same boundary curve. Every premise of
`lagrangianAction_le_parameter_graph_of_closureJets` holds here. -/
theorem action_plane_le_action_bump :
    lagrangianAction (ball (0 : ℝ^2) 1) dirichlet (plane 0) ≤
      lagrangianAction (ball (0 : ℝ^2) 1) dirichlet (fun x ↦ plane (bump x) x) :=
  lagrangianAction_le_parameter_graph_of_closureJets (J := univ) isOpen_ball
    isBounded_ball ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 2 1).hasC1GraphBoundary
      le_rfl) isOpen_univ ordConnected_univ (mem_univ 0)
    (ContinuousSecondJetOn.ofContDiff contDiff_dirichlet _)
    (ContinuousSecondJetOn.ofContDiff contDiff_plane _) contDiff_bump (mapsTo_univ _ _)
    bump_eq_zero_of_mem_frontier (fun t _ x _ k ↦ classicalEulerLagrange_plane t x k)
    (fun x _ z ↦ convexOn_dirichlet z x)

/-- The invariant integral of the family of planes has the same value for the parameter
`1 - x² - y² + c` and the constant parameter `c`. The two parameters agree on the unit
circle, where they have the value `c`. -/
theorem integral_invariant_bump_add_const (c : ℝ) :
    (∫ x in ball (0 : ℝ^2) 1, (fieldDensity dirichlet (plane (bump x + c)) x +
        fderiv ℝ (fun y ↦ bump y + c) x (familyFlux dirichlet plane (bump x + c) x))) =
      ∫ x in ball (0 : ℝ^2) 1, (fieldDensity dirichlet (plane c) x +
        fderiv ℝ (fun _ : ℝ^2 ↦ c) x (familyFlux dirichlet plane c x)) :=
  integral_invariant_eq_of_eqOn_frontier (θ := fun y ↦ bump y + c) (θ' := fun _ ↦ c)
    isExtremalFamily_plane ⟨contDiff_bump.add contDiff_const, mapsTo_univ _ _⟩
    ⟨contDiff_const, mapsTo_univ _ _⟩
    fun x hx ↦ by simp [bump_eq_zero_of_mem_frontier x hx]

end PDE.Examples.PlaneFamily
