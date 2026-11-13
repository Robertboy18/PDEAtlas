/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Operator
import PDE.Analysis.MeasureTheory.Lp.SmoothNonnegative
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure

/-!
# Positivity of the full Dirichlet inverse

Classical comparison first proves positivity for smooth nonnegative loads.
Nonnegative smooth approximation and the closed `L²` cone then extend
positivity to every nonnegative `L²` forcing. No smooth representative of the
original forcing, drift sign, or coercivity of the full form is assumed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Nonnegative `L²` loads have nonnegative Dirichlet solutions, for
smooth uniformly elliptic (not necessarily symmetric) coefficients with nonnegative
potential. -/
theorem nonneg_l2SolutionOperator
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (f : DerivLp n 2 Ω) (hf : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ f x) :
    ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ P.l2SolutionOperator hopen hbounded f x := by
  -- Without an invertible form, `ContinuousLinearMap.inverse` is zero and so is the solution.
  by_cases hinv : (P.form hopen hbounded).IsInvertible
  swap
  · have hzero : P.l2SolutionOperator hopen hbounded f = 0 := by
      simp [l2SolutionOperator, dirichletSolution,
        ContinuousLinearMap.inverse_of_not_isInvertible hinv]
    rw [hzero]
    filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
    rw [hx]
    rfl
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hclosed : IsClosed {g : DerivLp n 2 Ω |
      ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ P.l2SolutionOperator hopen hbounded g x} :=
    Lp.isClosed_nonneg_ae.preimage (P.l2SolutionOperator hopen hbounded).continuous
  apply (Metric.mem_of_closed' hclosed).mpr
  intro ε hε
  obtain ⟨g, hgsmooth, hg0, hgp, hgf⟩ :=
    Lp.exists_nonneg_contDiff_dist_lt (by norm_num : (2 : ℝ≥0∞) ≠ ∞) f hf hε
  let hgraw (k : ℕ) : ContDiffUpToBoundary k g Ω :=
    ContDiffUpToBoundary.of_contDiff (hgsmooth.of_le (by simp)) hbounded
  have hgLp : (hgraw 0).toLp hopen hbounded 2 = hgp.toLp g :=
    Lp.ext (((hgraw 0).toLp_coeFn hopen hbounded 2).trans hgp.coeFn_toLp.symm)
  obtain ⟨z, hz, hzraw, hzae, hboundary, heq⟩ :=
    P.exists_smoothRepresentative_of_form_eq hopen hbounded hgraph halpha hell
      g hgraw 0 (P.dirichletSolution hopen hbounded (hgp.toLp g)) (fun v ↦ by
        simpa only [zero_mul, add_zero, hgLp] using
          P.form_dirichletSolution_of_isInvertible hopen hbounded hinv (hgp.toLp g) v)
  have hnonneg : ∀ x ∈ closure Ω, 0 ≤ z x := by
    apply P.le_on_closure_of_classicalLoad_le hopen hbounded halpha hell hc
      continuousOn_const hz.continuousOn (fun _ _ ↦ contDiffAt_const)
      (fun x hx ↦ (hzraw 2).contDiffOn.contDiffAt (hopen.mem_nhds hx))
    · intro x hx
      have hzero : P.classicalLoad (fun _ ↦ 0) x = 0 :=
        (P.classicalLoad_eq_matrixOperator hopen hx contDiffAt_const).trans
          ((EllipticMaximum.matrixOperator_const
            (fun y ↦ Matrix.of (P.principal y)) P.nondivergenceDrift P.potential 0 x).trans
            (mul_zero _))
      rw [hzero]
      simpa only [zero_mul, add_zero] using (hg0 x).trans_eq (heq x hx).symm
    · intro x hx
      exact (hboundary x hx).symm.le
  refine ⟨hgp.toLp g, ?_, by simpa only [dist_comm] using hgf⟩
  filter_upwards [hzae, ae_restrict_mem hopen.measurableSet] with x hxz hx
  change 0 ≤ weakSolutionBase (P.dirichletSolution hopen hbounded (hgp.toLp g)) x
  exact (hnonneg x (subset_closure hx)).trans_eq hxz

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
