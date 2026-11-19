/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Positivity
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.StrictPositivity
import PDE.Analysis.MeasureTheory.ContinuousBounds

/-!
# Positive representatives for smooth nonnegative loads

The Dirichlet inverse of a nonzero smooth nonnegative load has a smooth
representative, zero geometric boundary values, and is strictly positive in a
connected domain. Nontriviality follows from injectivity of the inverse.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Smooth nonzero nonnegative forcing gives a strictly positive representative
of the constructed full Dirichlet solution, with its PDE and trace. -/
theorem exists_pos_smoothRepresentative_l2SolutionOperator
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (f : ℝ^n → ℝ) (hf : ∀ k, ContDiffUpToBoundary k f Ω)
    (hfnonneg : ∀ x ∈ Ω, 0 ≤ f x)
    (hfne : (hf 0).toLp hopen hbounded 2 ≠ 0) :
    ∃ z : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω]
        ⇑(P.l2SolutionOperator hopen hbounded ((hf 0).toLp hopen hbounded 2)) ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧
      (∀ x ∈ Ω, P.classicalLoad z x = f x) ∧
      ∀ x ∈ Ω, 0 < z x := by
  let F := (hf 0).toLp hopen hbounded 2
  obtain ⟨z, hz, hzraw, hzae, hboundary, heq⟩ :=
    P.exists_smoothRepresentative_of_form_eq hopen hbounded hgraph halpha hell f hf 0
      (P.dirichletSolution hopen hbounded F) (fun v ↦ by
        simpa only [zero_mul, add_zero] using
          P.form_dirichletSolution hopen hbounded hgraph halpha hell hc F v)
  have hload (x : ℝ^n) (hx : x ∈ Ω) : P.classicalLoad z x = f x := by
    simpa only [zero_mul, add_zero] using heq x hx
  have hF : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ F x := by
    filter_upwards [(hf 0).toLp_coeFn hopen hbounded 2,
      ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (hfnonneg x hxΩ).trans_eq hx.symm
  have hznonneg : ∀ x ∈ Ω, 0 ≤ z x := by
    apply PDE.Analysis.leOn_open_of_ae_le (μ := volume) hopen continuousOn_const
      ((hzraw 0).contDiffOn.continuousOn)
    filter_upwards [hzae,
      P.nonneg_l2SolutionOperator hopen hbounded hgraph halpha hell hc F hF]
        with x hx hz0
    exact hz0.trans_eq hx.symm
  have hpos : ∃ x ∈ Ω, 0 < z x := by
    by_contra h
    have hnonpos : ∀ x ∈ Ω, z x ≤ 0 := by
      simpa only [not_exists, not_and, not_lt] using h
    apply hfne
    apply P.injective_l2SolutionOperator hopen hbounded hgraph halpha hell hc
    rw [map_zero]
    apply Lp.ext
    filter_upwards [hzae, ae_restrict_mem hopen.measurableSet,
      Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx hxΩ hx0
    exact hx.symm.trans ((le_antisymm (hnonpos x hxΩ) (hznonneg x hxΩ)).trans hx0.symm)
  refine ⟨z, hz, hzraw, hzae, hboundary, hload, ?_⟩
  exact P.pos_of_nonneg_of_classicalLoad_nonneg hopen hbounded hconn halpha hell
    (fun x hx ↦ (hzraw 2).contDiffOn.contDiffAt (hopen.mem_nhds hx))
    (fun x hx ↦ (hfnonneg x hx).trans_eq (hload x hx).symm) hznonneg hpos

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
