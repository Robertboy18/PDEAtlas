/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.Full.Existence
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Coefficients.Adjoint
import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Coefficients.Shift
import PDE.Analysis.MeasureTheory.Lp.PositivePairing

/-!
# A positive adjoint Dirichlet eigenfunction

A constant shift makes the formal adjoint's potential nonnegative, so the
same existence construction applies. Testing the two weak
equations against each other identifies the adjoint eigenvalue. Positivity
of their `L²` pairing removes the shift.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A nonnegative nonzero eigenfunction determines a strictly positive
adjoint eigenfunction at the same real eigenvalue. The adjoint's zeroth-order
coefficient is allowed to change sign. -/
theorem exists_pos_adjoint_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (lambda : ℝ) (u : H¹₀(Ω))
    (hunonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM u x)
    (hune : baseCoordCLM u ≠ 0)
    (heq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v = lambda * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ) :
    ∃ (q : H¹₀(Ω)) (z : ℝ^n → ℝ),
      ‖baseCoordCLM q‖ = 1 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase q ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧ (∀ x ∈ Ω, 0 < z x) ∧
      ∀ v : H¹₀(Ω),
        P.form hopen hbounded v q = lambda * ⟪baseCoordCLM v, baseCoordCLM q⟫_ℝ := by
  let Q := P.formalAdjoint hopen
  obtain ⟨C, _, hC⟩ := (Q.potential_smooth 0).exists_derivative_bound hbounded [] (by simp)
  let S := Q.shiftPotential hopen C
  -- The adjoint principal part is the transpose, which has the same quadratic form.
  have hSell (x : ℝ^n) (hx : x ∈ Ω) :
      MatrixEllipticLowerBound (S.principal x) alpha := by
    intro ξ
    refine (hell x hx ξ).trans_eq ?_
    change principalEnergy (P.principal x) ξ = ∑ i, ∑ j, P.principal x j i * ξ i * ξ j
    rw [principalEnergy, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hSc (x : ℝ^n) (hx : x ∈ Ω) : 0 ≤ S.potential x := by
    have h := hC x hx
    change ‖Q.potential x‖ ≤ C at h
    change 0 ≤ Q.potential x + C
    have := (abs_le.mp h).1
    linarith
  obtain ⟨eta, q, z, _, hnorm, hz, hzraw, hzae, hboundary, hzpos, _, hq⟩ :=
    S.exists_pos_eigenpair hopen hbounded hconn hgraph halpha hSell hSc
  have hqpos : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM q x := by
    filter_upwards [hzae, ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (hzpos x hxΩ).trans_eq hx
  have hpair : 0 < ⟪baseCoordCLM q, baseCoordCLM u⟫_ℝ :=
    Lp.inner_pos_of_pos_ae_of_nonneg_ae _ _ hqpos hunonneg hune
  have heta : eta = lambda + C := by
    have h := hq u
    change (Q.shiftPotential hopen C).form hopen hbounded q u = _ at h
    rw [form_shiftPotential, form_formalAdjoint, heq,
      real_inner_comm (baseCoordCLM u) (baseCoordCLM q)] at h
    rw [real_inner_comm (baseCoordCLM u) (baseCoordCLM q)] at hpair
    nlinarith
  refine ⟨q, z, hnorm, hz, hzraw, hzae, hboundary, hzpos, fun v ↦ ?_⟩
  have h := hq v
  change (Q.shiftPotential hopen C).form hopen hbounded q v = _ at h
  rw [form_shiftPotential, form_formalAdjoint, heta,
    real_inner_comm (baseCoordCLM v) (baseCoordCLM q)] at h
  linarith

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
