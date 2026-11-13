/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Nondivergence
import PDE.Analysis.LinearAlgebra.Ellipticity
import PDE.Elliptic.Classical.MaximumPrinciple.MatrixSymmetrization

/-!
# Classical comparison for smooth full coefficients

The coefficient data supply the bounded effective drift required by the
matrix maximum principle. Uniform ellipticity supplies its diagonal lower bound
and the nonnegativity of the principal quadratic form; the principal coefficients need
not be symmetric. Thus ordered loads and boundary values order classical functions
without any sign assumption on the drift or its divergence.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open Set
open scoped InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Classical comparison for the full load, with its maximum-principle
coefficient bounds derived from smoothness and uniform ellipticity.
Boundary regularity and connectedness are not required. -/
theorem le_on_closure_of_classicalLoad_le
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    {u v : ℝ^n → ℝ}
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hvreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hload : ∀ x ∈ Ω, P.classicalLoad u x ≤ P.classicalLoad v x)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ closure Ω, u x ≤ v x := by
  classical
  let i : Fin n := ⟨0, Fact.out⟩
  have hquad (x : ℝ^n) (hx : x ∈ Ω) (ξ : ℝ^n) :
      0 ≤ ∑ j : Fin n, ∑ k : Fin n, Matrix.of (P.principal x) j k * ξ j * ξ k := by
    have h0 : 0 ≤ alpha * ((fun j ↦ ξ j) ⬝ᵥ (fun j ↦ ξ j)) :=
      mul_nonneg halpha.le (Finset.sum_nonneg fun j _ ↦ mul_self_nonneg (ξ j))
    simpa only [Matrix.of_apply, principalEnergy] using h0.trans (hell x hx (fun j ↦ ξ j))
  have hdiag (x : ℝ^n) (hx : x ∈ Ω) : alpha ≤ P.principal x i i := by
    simpa [principalEnergy, dotProduct, Pi.single_apply] using hell x hx (Pi.single i 1)
  obtain ⟨B, _, hB⟩ :=
    (P.nondivergenceDrift_regular hopen 0 i).exists_derivative_bound hbounded [] (by simp)
  have hdrift (x : ℝ^n) (hx : x ∈ Ω) : P.nondivergenceDrift x i ≤ B :=
    (le_abs_self _).trans (hB x hx)
  have hsub (x : ℝ^n) (hx : x ∈ Ω) :
      EllipticMaximum.matrixOperator (fun x ↦ Matrix.of (P.principal x)) P.nondivergenceDrift
        P.potential (fun y ↦ u y - v y) x ≤ 0 := by
    rw [EllipticMaximum.matrixOperator_sub _ _ _ (hureg x hx) (hvreg x hx)]
    exact sub_nonpos.mpr ((P.classicalLoad_eq_matrixOperator hopen hx (hureg x hx)).symm.le.trans
      ((hload x hx).trans (P.classicalLoad_eq_matrixOperator hopen hx (hvreg x hx)).le))
  have h := EllipticMaximum.matrix_subsolution_le_of_boundary_le_of_nonneg_quadratic hopen
    hbounded.isCompact_closure (fun x ↦ Matrix.of (P.principal x))
    P.nondivergenceDrift P.potential i halpha hquad hdiag hdrift (M := 0) hc
    (fun x _ ↦ by rw [mul_zero]) (hucont.sub hvcont)
    (fun x hx ↦ (hureg x hx).sub (hvreg x hx)) hsub
    (fun x hx ↦ sub_nonpos.mpr (hboundary x hx))
  exact fun x hx ↦ sub_nonpos.mp (h x hx)

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
