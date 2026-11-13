/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ClassicalZero

/-!
# Classical Dirichlet functions in the full weak equation

The geometric trace theorem constructs `H¹₀` from zero boundary
values. The classical `H²` graph and the full load identity then give every
weak test, including the drift and potential. This direction uses no
ellipticity, symmetry, invertibility, or sign hypothesis.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A classical Dirichlet function determines an `H¹₀`
state, and its classical full load represents every weak test. -/
theorem exists_H10_form_eq_classicalLoad
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    {z : ℝ^n → ℝ} (hz : ContDiffUpToBoundary 2 z Ω)
    (hcont : ContinuousOn z (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, z x = 0) :
    ∃ u : H¹₀(Ω),
      (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] z ∧
      ∀ v : H¹₀(Ω),
        P.form hopen hbounded u v =
          ⟪(P.classicalLoad_regular hopen hbounded hz).toLp hopen hbounded 2,
            baseCoordCLM v⟫_ℝ := by
  obtain ⟨u, huae, _⟩ := (hz.of_le (by decide : 1 ≤ 2)).exists_H10_of_eq_zero_on_frontier
    hopen hbounded hgraph hcont hzero
  have hbase : wkpBaseCoordinateCLM (hz.toWkpSpaceOn hopen hbounded 2) =
      baseCoordCLM u :=
    Lp.ext ((hz.toWkpSpaceOn_base_ae hopen hbounded 2).trans huae.symm)
  refine ⟨u, huae, fun v ↦ ?_⟩
  rw [P.form_eq_load hopen hbounded 0 _ u v hbase, P.load_toWkpSpaceOn]
  congr 1
  apply Lp.ext
  exact ((P.classicalLoad_regular hopen hbounded hz).toWkpSpaceOn_base_ae
    hopen hbounded 2).trans
    ((P.classicalLoad_regular hopen hbounded hz).toLp_coeFn hopen hbounded 2).symm

/-- A classical eigen-equation with zero boundary values constructs
the weak eigen-equation; no weak solution is assumed. -/
theorem exists_eigenfunction_of_classicalLoad_eq
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    {z : ℝ^n → ℝ} (hz : ContDiffUpToBoundary 2 z Ω)
    (hcont : ContinuousOn z (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, z x = 0) (r : ℝ)
    (heq : ∀ x ∈ Ω, P.classicalLoad z x = r * z x) :
    ∃ u : H¹₀(Ω),
      (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] z ∧
      ∀ v : H¹₀(Ω),
        P.form hopen hbounded u v = r * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ := by
  obtain ⟨u, huae, hform⟩ :=
    P.exists_H10_form_eq_classicalLoad hopen hbounded hgraph hz hcont hzero
  have hload : (P.classicalLoad_regular hopen hbounded hz).toLp hopen hbounded 2 =
      r • baseCoordCLM u := by
    apply Lp.ext
    filter_upwards [(P.classicalLoad_regular hopen hbounded hz).toLp_coeFn
      hopen hbounded 2, Lp.coeFn_smul r (baseCoordCLM u),
      huae, ae_restrict_mem hopen.measurableSet] with x hf hs hu hx
    simpa only [hf, hs, Pi.smul_apply, smul_eq_mul, hu] using heq x hx
  refine ⟨u, huae, fun v ↦ ?_⟩
  rw [hform, hload, real_inner_smul_left]

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
