/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.Full.Regularity
public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Eigenfunction
import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Positivity
import PDE.Analysis.Spectral.Positive.LpPositivePart

/-!
# Nonvanishing at the positive adjoint eigenvalue

The positive adjoint weight makes the order defect of a positive part
vanish. The positive part therefore lifts through the Dirichlet
inverse to a weak eigenfunction. Strong positivity then rules out
zeros of the original eigenfunction, without a boundary quotient or a
uniform positive lower bound on the adjoint weight.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Every nonzero real eigenfunction at a strictly positive adjoint
eigenvalue has a nowhere zero continuous representative on the domain. -/
theorem exists_nonvanishingRepresentative_of_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (q : H¹₀(Ω)) (hq : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM q x)
    {r : ℝ} (hr : 0 < r)
    (hqeq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded v q = r * ⟪baseCoordCLM v, baseCoordCLM q⟫_ℝ)
    (u : H¹₀(Ω)) (hune : baseCoordCLM u ≠ 0)
    (heq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v = r * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ) :
    ∃ f : ℝ^n → ℝ, (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      ContinuousOn f Ω ∧ ∀ x ∈ Ω, f x ≠ 0 := by
  classical
  by_cases hposzero : Lp.posPart (baseCoordCLM u) = 0
  · have hunonpos : ∀ᵐ x ∂domainMeasure n Ω, baseCoordCLM u x ≤ 0 := by
      have hzero : ∀ᵐ x ∂domainMeasure n Ω, Lp.posPart (baseCoordCLM u) x = 0 := by
        rw [hposzero]
        exact Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)
      filter_upwards [Lp.coeFn_posPart (baseCoordCLM u), hzero] with x hx hz
      exact (le_max_left _ _).trans_eq (hx.symm.trans hz)
    have hneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM (-u) x := by
      rw [map_neg]
      filter_upwards [Lp.coeFn_neg (baseCoordCLM u), hunonpos] with x hx hu
      simpa only [hx, Pi.neg_apply] using neg_nonneg.mpr hu
    have hnegne : baseCoordCLM (-u) ≠ 0 := by
      simpa only [map_neg, neg_ne_zero] using hune
    have hnegeq (v : H¹₀(Ω)) :
        P.form hopen hbounded (-u) v =
          r * ⟪baseCoordCLM (-u), baseCoordCLM v⟫_ℝ := by
      rw [map_neg, neg_apply, heq, map_neg, inner_neg_left]
      ring
    obtain ⟨f, _, hfraw, hfae, _, hfpos, _⟩ :=
      P.exists_pos_smoothRepresentative_of_eigenfunction hopen hbounded hconn hgraph
        halpha hell r (-u) hnegeq hneg hnegne
    refine ⟨fun x ↦ -f x, ?_, (hfraw 0).contDiffOn.continuousOn.neg,
      fun x hx ↦ neg_ne_zero.mpr (ne_of_gt (hfpos x hx))⟩
    have ha := hfae
    change f =ᵐ[domainMeasure n Ω] ⇑(baseCoordCLM (-u)) at ha
    rw [map_neg] at ha
    filter_upwards [ha, Lp.coeFn_neg (baseCoordCLM u)] with x hx hn
    simpa only [hn, Pi.neg_apply, neg_neg] using congrArg Neg.neg hx.symm
  · let A := P.l2SolutionOperator hopen hbounded
    have hA := P.nonneg_l2SolutionOperator hopen hbounded hgraph halpha hell hc
    have hweight := P.mul_inner_l2SolutionOperator_of_adjoint_eigenfunction
      hopen hbounded hgraph halpha hell hc r q hqeq
    have hueq := P.base_eq_smul_l2SolutionOperator_of_eigenfunction
      hopen hbounded hgraph halpha hell hc r u heq
    have hpos := A.toLinearMap.posPart_eq_smul_apply_of_pos_adjoint_weight
      hA (baseCoordCLM q) hq hr hweight (baseCoordCLM u) hueq
    obtain ⟨v, hbase, hveq⟩ := P.exists_eigenfunction_of_eq_smul_l2SolutionOperator
      hopen hbounded hgraph halpha hell hc r (Lp.posPart (baseCoordCLM u)) hpos
    have hvnonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM v x := by
      rw [hbase]
      exact Lp.posPart_nonneg_ae (baseCoordCLM u)
    have hvne : baseCoordCLM v ≠ 0 := by rwa [hbase]
    obtain ⟨g, _, hgraw, hgae, _, hgpos, _⟩ :=
      P.exists_pos_smoothRepresentative_of_eigenfunction hopen hbounded hconn hgraph
        halpha hell r v hveq hvnonneg hvne
    obtain ⟨f, _, hfraw, hfae, _, _⟩ :=
      P.exists_smoothRepresentative_of_eigenfunction hopen hbounded hgraph halpha hell r u heq
    have hae : (fun x ↦ max (f x) 0) =ᵐ[domainMeasure n Ω] g := by
      change g =ᵐ[domainMeasure n Ω] ⇑(baseCoordCLM v) at hgae
      rw [hbase] at hgae
      filter_upwards [hfae, hgae, Lp.coeFn_posPart (baseCoordCLM u)] with x hf hg hp
      exact (congrArg (fun t : ℝ ↦ max t 0) hf).trans (hp.symm.trans hg.symm)
    have hsame := Measure.eqOn_open_of_ae_eq hae hopen
      ((hfraw 0).contDiffOn.continuousOn.sup continuousOn_const)
      (hgraw 0).contDiffOn.continuousOn
    refine ⟨f, hfae.symm, (hfraw 0).contDiffOn.continuousOn, fun x hx hzero ↦ ?_⟩
    have h := hsame hx
    change max (f x) 0 = g x at h
    rw [hzero, max_self] at h
    exact (ne_of_gt (hgpos x hx)) h.symm

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
