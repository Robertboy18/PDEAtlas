/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.ClassicalEquation
import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.StrictPositivity
import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Coefficients.Shift
import PDE.Analysis.MeasureTheory.ContinuousBounds

/-!
# Smooth representatives and positivity of full weak eigenfunctions

The weak eigen-equation is a shifted equation with zero load. Thus
elliptic regularity applies without first assuming regularity of the
unknown eigenfunction. Trace identification supplies its
zero boundary values. A nonnegative nonzero eigenfunction is strictly
positive, for any real eigenvalue, by shifting the classical potential.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A full weak eigenfunction has a smooth closure representative
with the classical eigen-equation and geometric zero boundary values. -/
theorem exists_smoothRepresentative_of_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (lambda : ℝ) (u : H¹₀(Ω))
    (heq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v = lambda * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ) :
    ∃ z : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase u ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧
      ∀ x ∈ Ω, P.classicalLoad z x = lambda * z x := by
  let hzero (k : ℕ) : ContDiffUpToBoundary k (fun _ : ℝ^n ↦ (0 : ℝ)) Ω :=
    ContDiffUpToBoundary.const 0
  have hzeroLp : (hzero 0).toLp hopen hbounded 2 = 0 :=
    Lp.ext (((hzero 0).toLp_coeFn hopen hbounded 2).trans
      (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)).symm)
  obtain ⟨z, hz, hzraw, hzae, hboundary, hload⟩ :=
    P.exists_smoothRepresentative_of_form_eq hopen hbounded hgraph halpha hell
      (fun _ ↦ 0) hzero (-lambda) u (fun v ↦ by
        rw [hzeroLp, inner_zero_left, heq]
        ring)
  refine ⟨z, hz, hzraw, hzae, hboundary, fun x hx ↦ ?_⟩
  have h := hload x hx
  linarith

/-- A nonnegative nonzero eigenfunction has a strictly positive
smooth representative. No sign assumption on its eigenvalue or the
operator's potential is needed for this conclusion. -/
theorem exists_pos_smoothRepresentative_of_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (lambda : ℝ) (u : H¹₀(Ω))
    (heq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v = lambda * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ)
    (hu : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM u x)
    (hne : baseCoordCLM u ≠ 0) :
    ∃ z : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase u ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧ (∀ x ∈ Ω, 0 < z x) ∧
      ∀ x ∈ Ω, P.classicalLoad z x = lambda * z x := by
  obtain ⟨z, hz, hzraw, hzae, hboundary, hload⟩ :=
    P.exists_smoothRepresentative_of_eigenfunction hopen hbounded hgraph halpha hell
      lambda u heq
  have hznonneg : ∀ x ∈ Ω, 0 ≤ z x := by
    apply PDE.Analysis.leOn_open_of_ae_le (μ := volume) hopen continuousOn_const
      ((hzraw 0).contDiffOn.continuousOn)
    exact (hzae.and hu).mono fun _ hx ↦ hx.2.trans_eq hx.1.symm
  have hzpositive : ∃ x ∈ Ω, 0 < z x := by
    by_contra h
    have hnonpos : ∀ x ∈ Ω, z x ≤ 0 := by
      simpa only [not_exists, not_and, not_lt] using h
    apply hne
    apply Lp.ext
    filter_upwards [hzae, ae_restrict_mem hopen.measurableSet,
      Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx hxΩ hx0
    exact hx.symm.trans ((le_antisymm (hnonpos x hxΩ) (hznonneg x hxΩ)).trans hx0.symm)
  refine ⟨z, hz, hzraw, hzae, hboundary, ?_, hload⟩
  apply (P.shiftPotential hopen (-lambda)).pos_of_nonneg_of_classicalLoad_nonneg
    hopen hbounded hconn halpha hell
    (fun x hx ↦ (hzraw 2).contDiffOn.contDiffAt (hopen.mem_nhds hx)) ?_ hznonneg hzpositive
  intro x hx
  rw [classicalLoad_shiftPotential, hload x hx]
  linarith

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
