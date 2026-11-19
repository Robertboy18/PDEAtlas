/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Zero-boundary Sobolev fields from classical boundary values

Interior classical regularity and uniform continuity of the first derivatives construct
the Sobolev graph. Continuity on the closure ties its representative to the prescribed
boundary values, and the geometric trace theorem proves membership in the closure of
interior test functions. No compact support of the classical function is required.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open MeasureTheory Set GraphSpace Boundary
open scoped ENNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- A classical `C¹` function vanishing on the boundary gives an `H¹₀` field,
with its value and every first derivative represented by the original function. -/
theorem exists_H10_of_eq_zero_on_frontier
    (hf : ContDiffUpToBoundary 1 f Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (hc : ContinuousOn f (closure Ω)) (hzero : ∀ x ∈ frontier Ω, f x = 0) :
    ∃ U : H¹₀(Ω),
      (baseCoordCLM U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      ∀ i, (derivCoordCLM i U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        ∂[i] f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
  let V := hf.toWkpSpaceOn hopen hbounded (ENNReal.ofReal 2)
  have hmem := (Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
    hopen hbounded hgraph 2 V hc
    (hf.toWkpSpaceOn_base_ae hopen hbounded (ENNReal.ofReal 2))).mpr hzero
  let U : H¹₀(Ω) :=
    ⟨Trace.C1.domainW1pTwoEquivH1 V,
      (Trace.C1.domainW1pTwoEquivH1_mem_H10_iff V).mpr hmem⟩
  refine ⟨U, ?_, fun i ↦ ?_⟩
  · change (wkpCoordinateCLM (baseIndex (m + 1) 1) (Trace.C1.domainW1pTwoEquivH1 V) :
      ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] f
    rw [Trace.C1.domainW1pTwoEquivH1_coordinate]
    exact hf.toWkpSpaceOn_base_ae hopen hbounded (ENNReal.ofReal 2)
  · change (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (Trace.C1.domainW1pTwoEquivH1 V) :
      ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] (∂[i] f)
    rw [Trace.C1.domainW1pTwoEquivH1_coordinate]
    simpa only [wkpCoordinateCLM_apply, V, singleDerivIndex_toList, iteratedPartialDeriv] using
      hf.toWkpSpaceOn_apply_ae hopen hbounded (ENNReal.ofReal 2) (singleDerivIndex (m + 1) i)

end SobolevSpace.ContDiffUpToBoundary
