/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalBoundaryData

/-!
# The full elliptic solution lift from classical boundary data

`C²` graph geometry and principal coefficients of class `C¹` up to the boundary
produce a bounded `L² → H²` solver at a coercive shift. Every weak solution of the
unshifted full operator is represented by this same map after adding the shift to
its load. No atlas or measurable choice of spatial representatives is assumed.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A bounded shifted `H²` lift represents every weak solution of the full unshifted
operator. Its shift and operator are chosen before the right-hand side and solution. -/
theorem exists_classical_full_h2_lift
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ (mu : ℝ) (S : DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω)),
      ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
        IsWeakShiftedFullDivergenceSolution
          (fun i j ↦ (ha i j).toLp hopen hbounded ∞) b c 0 f 0 u →
        wkpBaseCoordinateCLM (S (f + mu • baseCoordCLM u)) = baseCoordCLM u := by
  let aLp := fun i j ↦ (ha i j).toLp hopen hbounded ∞
  have hAE : AEUniformlyElliptic aLp alpha := by
    have h := coefficientBase_aeUniformlyElliptic hopen.measurableSet
      (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) a
      (fun i j ↦ (ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞) alpha halpha hell
    change AEUniformlyElliptic (fun i j ↦ wkpBaseCoordinateCLM
      ((ha i j).toWkpSpaceOn hopen hbounded ∞)) alpha at h
    simpa only [ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] using h
  have hA := integratedElliptic_multiplication_of_ae aLp hAE
  let beta := ∑ i, ‖b i‖
  let gamma := ‖c‖
  have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
  have hgamma : 0 ≤ gamma := norm_nonneg c
  have hb : ∀ i, ‖b i‖ ≤ beta := fun i ↦
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (b j)) (Finset.mem_univ i)
  have hc : ‖c‖ ≤ gamma := le_rfl
  let mu := coerciveShift (n := n) alpha beta gamma
  let S₁ := fullDivergenceWeakSolveCLM aLp b c hA hbeta hgamma hb hc (le_refl mu)
  obtain ⟨K, _, hreg⟩ := exists_global_h2_estimate_of_contDiffUpToBoundary
    hopen hbounded hgraph a ha b c mu alpha halpha hell
  have hqual : HasHigherSolutionLift 0 S₁ := hasHigherSolutionLift_zero S₁ (by
    intro f
    obtain ⟨W, hW, _⟩ := hreg f (S₁ f)
      (fullDivergenceWeakSolveCLM_isWeakSolution aLp b c hA hbeta hgamma hb hc
        (le_refl mu) hopen f)
    refine ⟨W, ?_⟩
    rw [hW]
    exact Filter.EventuallyEq.rfl)
  let S := (higherSolutionOperator hopen S₁ hqual).comp
    (orderZeroSobolevCLM (n := n) (p := 2) (Omega := Ω))
  refine ⟨mu, S, ?_⟩
  intro f u hu
  have hshift : IsWeakShiftedFullDivergenceSolution aLp b c mu
      (f + mu • baseCoordCLM u) 0 u := by
    simpa only [sub_zero] using
      (isWeakShiftedFullDivergenceSolution_change_shift aLp b c 0 mu f u).mp hu
  have heq := eq_fullDivergenceWeakSolveCLM aLp b c hA hbeta hgamma hb hc
    (le_refl mu) (f + mu • baseCoordCLM u) hshift
  change wkpBaseCoordinateCLM (higherSolutionOperator hopen S₁ hqual
    (orderZeroSobolevCLM (f + mu • baseCoordCLM u))) = _
  rw [higherSolutionOperator_base, higherWeakSolutionBaseCLM_apply,
    orderZeroSobolevCLM_base, ← heq]

end SobolevSpace.GraphSpace.BoundaryRegularity
