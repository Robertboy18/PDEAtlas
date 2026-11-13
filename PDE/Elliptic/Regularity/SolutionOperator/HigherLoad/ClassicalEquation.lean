/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Elliptic.Regularity.Global.ClassicalSmoothBoundaryData
import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary

/-!
# Classical equations and boundary values of smooth weak solutions

Smooth coefficients and forcing give a single smooth representative of a
Dirichlet weak solution. Its boundary values follow from the geometric trace kernel,
and its classical equation follows from the higher load identification and density
of the energy space in `L²`; neither is assumed.

A constant shift is retained. In particular, real eigenfunctions are covered by zero
forcing and a negative shift, without assuming regularity of the unknown forcing.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Smooth full weak equations give smooth representatives with the zero
boundary values and the shifted classical equation. Geometry and data are
specified at each finite order; no common ambient extension is required. -/
theorem exists_smoothRepresentative_of_form_eq
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (f : ℝ^n → ℝ) (hf : ∀ k, ContDiffUpToBoundary k f Ω)
    (lambda : ℝ) (u : H¹₀(Ω))
    (hu : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v + lambda * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ =
        ⟪(hf 0).toLp hopen hbounded 2, baseCoordCLM v⟫_ℝ) :
    ∃ z : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase u ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧
      ∀ x ∈ Ω, P.classicalLoad z x + lambda * z x = f x := by
  have hweak := (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen
    (fun i j ↦ (P.principal_smooth 0 i j).toLp hopen hbounded ∞)
    (fun i ↦ (P.drift_smooth 0 i).toLp hopen hbounded ∞)
    ((P.potential_smooth 0).toLp hopen hbounded ∞)
    lambda ((hf 0).toLp hopen hbounded 2) 0 u).mp (by
      intro v
      simp only [shiftedDivergenceForm_apply, generalizedLoad_apply, Pi.zero_apply,
        inner_zero_left, Finset.sum_const_zero, add_zero]
      change P.form hopen hbounded u v + lambda * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ =
        ⟪(hf 0).toLp hopen hbounded 2, baseCoordCLM v⟫_ℝ
      exact hu v)
  obtain ⟨z, hz, hzraw, hzae⟩ :=
    exists_smoothRepresentativeOnClosure_of_contDiffUpToBoundary hopen hbounded hgraph
      P.principal P.drift P.potential f P.principal_smooth P.drift_smooth
      P.potential_smooth hf lambda alpha halpha hell u hweak
  have hboundary : ∀ x ∈ frontier Ω, z x = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
    have htrace (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : ENNReal.ofReal 2 = p)
        (U : W^{1,p}(Ω))
        (hU : U ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p)
          (Ω := Ω)).toSubmodule)
        (hUz : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] z) :
        ∀ x ∈ frontier Ω, z x = 0 := by
      subst p
      exact (Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
        hopen hbounded ((hgraph 1).hasC1GraphBoundary le_rfl) 2
        U hz.continuousOn hUz).mp hU
    exact htrace 2 (ENNReal.ofReal_ofNat 2) u.val u.property hzae.symm
  let F : DerivLp n 2 Ω :=
    (P.classicalLoad_regular hopen hbounded (hzraw 2)).toLp hopen hbounded 2
  have hbase : wkpBaseCoordinateCLM ((hzraw 2).toWkpSpaceOn hopen hbounded 2) =
      baseCoordCLM u :=
    Lp.ext (((hzraw 2).toWkpSpaceOn_base_ae hopen hbounded 2).trans hzae)
  have hload : F + lambda • baseCoordCLM u = (hf 0).toLp hopen hbounded 2 := by
    apply (h10L2GelfandTriple hopen).pivotToDual_injective
    ext v
    change ⟪F + lambda • baseCoordCLM u, baseCoordCLM v⟫_ℝ = _
    rw [inner_add_left, real_inner_smul_left]
    have hform := P.form_eq_load hopen hbounded 0
      ((hzraw 2).toWkpSpaceOn hopen hbounded 2) u v hbase
    rw [P.load_toWkpSpaceOn hopen hbounded (hzraw 2),
      ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] at hform
    exact hform ▸ hu v
  have hae : (fun x ↦ P.classicalLoad z x + lambda * z x) =ᵐ[domainMeasure n Ω] f := by
    filter_upwards [Lp.coeFn_add F (lambda • baseCoordCLM u),
      Lp.coeFn_smul lambda (baseCoordCLM u),
      (P.classicalLoad_regular hopen hbounded (hzraw 2)).toLp_coeFn hopen hbounded 2,
      (hf 0).toLp_coeFn hopen hbounded 2, hzae] with x hadd hsmul hF hfval hzval
    rw [← hfval, ← hload, hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hF, hzval]
    rfl
  refine ⟨z, hz, hzraw, hzae, hboundary, ?_⟩
  exact Measure.eqOn_open_of_ae_eq hae hopen
    ((P.classicalLoad_regular hopen hbounded (hzraw 2)).contDiffOn.continuousOn.add
      (continuousOn_const.mul ((hzraw 0).contDiffOn.continuousOn)))
    ((hf 0).contDiffOn.continuousOn)

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
