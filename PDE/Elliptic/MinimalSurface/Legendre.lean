/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Legendre.Linearization
public import PDE.Elliptic.MinimalSurface.Calculus
import CAS.ExactTactic

/-!
# Local Legendre linearization of the minimal-surface equation

Let `u` be a `C²` solution of the planar minimal-surface equation whose Hessian determinant is
nonzero at a point. The gradient of `u` has a local inverse near that point, and the Legendre dual
`localLegendre` built from it is `C²` and solves the linear equation `dualResidual` with coefficient
matrix `I + p pᵀ` (`exists_localLegendre_solution` for the nondivergence form of the equation,
`exists_localLegendre_solution_of_divergence_eq_zero` for the divergence form). The calculus
identity for the normalized gradient connects the two forms. The quadratic form of `I + p pᵀ`
dominates `‖ξ‖²` (`dual_principalForm_lower_bound`, checked by SymLean's `cas` tactic), so the
linear equation is elliptic. Convexity of `u` is not assumed, and the results are local and
classical.

This is the minimal-surface example of Evans's §4.4.3(b): the equation (24), the inversion (25)-(26)
of the gradient where (27) holds, the dual (28), and the linear equation (30).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.3(b) (Legendre transform), (24)-(30), p. 210.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped Gradient

namespace PDE.Elliptic.MinimalSurface

open PDE.Analysis

/-- The linear PDE in gradient coordinates, with coefficient matrix `I + p pᵀ`. -/
def dualResidual (v : ℝ^2 → ℝ) (p : ℝ^2) : ℝ :=
  (1 + (p 0) ^ 2) * (∂[0] (∂[0] v)) p +
    2 * p 0 * p 1 * (∂[0] (∂[1] v)) p +
    (1 + (p 1) ^ 2) * (∂[1] (∂[1] v)) p

/-- The transformed principal form dominates the Euclidean squared length.
This lower bound is global in p; no boundedness of the coefficients is asserted. -/
theorem dual_principalForm_lower_bound (p ξ : ℝ^2) :
    (ξ 0) ^ 2 + (ξ 1) ^ 2 ≤
      (1 + (p 0) ^ 2) * (ξ 0) ^ 2 +
        2 * p 0 * p 1 * ξ 0 * ξ 1 + (1 + (p 1) ^ 2) * (ξ 1) ^ 2 := by
  have h := sq_nonneg (p 0 * ξ 0 + p 1 * ξ 1)
  cas using h

/-- A nondegenerate C² solution of the minimal-graph equation has a local C² Legendre
dual solving the linear equation with principal matrix `I + p pᵀ`. The local inverse
gradient map is constructed from nonsingularity at the chosen point. -/
theorem exists_localLegendre_solution
    {u : ℝ^2 → ℝ} {Ω : Set (ℝ^2)} {x : ℝ^2}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hdet : (jacobianMatrix (∇ u) x).det ≠ 0)
    (hPDE : ∀ y ∈ Ω, residual u y = 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^2) (ℝ^2),
      (e : ℝ^2 → ℝ^2) = ∇ u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ContDiffOn ℝ 2 (localLegendre u e.symm) e.target ∧
            (∀ p ∈ e.target, HasGradientAt (localLegendre u e.symm) (e.symm p) p) ∧
              ∀ p ∈ e.target, dualResidual (localLegendre u e.symm) p = 0 := by
  have hsource : ∀ y ∈ Ω,
      (1 + (∇ u y 1) ^ 2) * (∂[0] (∂[0] u)) y +
        2 * (-(∇ u y 0) * ∇ u y 1) * (∂[0] (∂[1] u)) y +
        (1 + (∇ u y 0) ^ 2) * (∂[1] (∂[1] u)) y = 0 := by
    intro y hy
    have h := hPDE y hy
    unfold residual at h
    simp only [gradient_apply_eq_partialDeriv]
    cas using h
  obtain ⟨e, he, hxe, hsub, hi, hv, hgrad, hlin⟩ :=
    exists_localLegendre_linearized hΩ hx hu hdet
      (fun p ↦ 1 + (p 1) ^ 2) (fun p ↦ -p 0 * p 1) (fun p ↦ 1 + (p 0) ^ 2)
      hsource
  refine ⟨e, he, hxe, hsub, hi, hv, hgrad, ?_⟩
  intro p hp
  have h := hlin p hp
  unfold dualResidual
  cas using h

/-- A C² solution of the divergence minimal-surface equation with nonsingular Hessian
at one point has a local C² Legendre dual solving the linear elliptic equation. -/
theorem exists_localLegendre_solution_of_divergence_eq_zero
    {u : ℝ^2 → ℝ} {Ω : Set (ℝ^2)} {x : ℝ^2}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hdet : (jacobianMatrix (∇ u) x).det ≠ 0)
    (hPDE : ∀ y ∈ Ω,
      (∇· (fun z ↦ (Real.sqrt (1 + ‖∇ u z‖ ^ 2))⁻¹ • ∇ u z)) y = 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^2) (ℝ^2),
      (e : ℝ^2 → ℝ^2) = ∇ u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ContDiffOn ℝ 2 (localLegendre u e.symm) e.target ∧
            (∀ p ∈ e.target, HasGradientAt (localLegendre u e.symm) (e.symm p) p) ∧
              ∀ p ∈ e.target, dualResidual (localLegendre u e.symm) p = 0 := by
  apply exists_localLegendre_solution hΩ hx hu hdet
  intro y hy
  exact (divergence_normalizedGradient_eq_zero_iff
    (hu.contDiffAt (hΩ.mem_nhds hy))).mp (hPDE y hy)

end PDE.Elliptic.MinimalSurface
