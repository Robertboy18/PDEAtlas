/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalHigherBoundaryData

/-!
# Higher full elliptic solvers at one fixed shift

Boundary geometry of class `C^{r+2}` and coefficients of class `C^{r+1}`
give bounded maps `H^r → H^{r+2}` at each requested order. All maps lift the
same weak Dirichlet solver at one Gårding shift. Their construction uses the higher
boundary estimate and the closed graph theorem, so no atlas or regularity lift is assumed.

The principal matrix need not be symmetric here. Drift and potential may
have either sign.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Any family of finite elliptic regularity orders admits higher solution lifts
at one coefficient-dependent shift. Boundary and coefficient derivatives are
required only at the requested orders. -/
theorem exists_classical_full_higher_lifts_family
    {ι : Type*} (order : ι → ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ i, Boundary.HasContDiffGraphBoundary (order i + 2) Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
    (hb : ∀ i, ContDiffUpToBoundary 1 (b i) Ω)
    (hc : ContDiffUpToBoundary 0 c Ω)
    (haHigher : ∀ t i j, ContDiffUpToBoundary (order t + 1) (fun x ↦ a x i j) Ω)
    (hbHigher : ∀ t i, ContDiffUpToBoundary (order t + 1) (b i) Ω)
    (hcHigher : ∀ t, ContDiffUpToBoundary (order t + 1) c Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ (mu : ℝ)
      (S : ∀ i, W^{order i,2}(Ω) →L[ℝ] W^{order i + 2,2}(Ω)),
      ∀ i (F : W^{order i,2}(Ω)) (u : H¹₀(Ω)),
        IsWeakShiftedFullDivergenceSolution
          (fun i j ↦ (ha i j).toLp hopen hbounded ∞)
          (fun i ↦ (hb i).toLp hopen hbounded ∞) (hc.toLp hopen hbounded ∞)
          mu (wkpBaseCoordinateCLM F) 0 u →
        wkpBaseCoordinateCLM (S i F) = baseCoordCLM u := by
  let aLp := fun i j ↦ (ha i j).toLp hopen hbounded ∞
  let bLp := fun i ↦ (hb i).toLp hopen hbounded ∞
  let cLp := hc.toLp hopen hbounded ∞
  have hAE : AEUniformlyElliptic aLp alpha := by
    have h := coefficientBase_aeUniformlyElliptic hopen.measurableSet
      (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) a
      (fun i j ↦ (ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞) alpha halpha hell
    change AEUniformlyElliptic (fun i j ↦ wkpBaseCoordinateCLM
      ((ha i j).toWkpSpaceOn hopen hbounded ∞)) alpha at h
    simpa only [ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] using h
  have hA := integratedElliptic_multiplication_of_ae aLp hAE
  let beta := ∑ i, ‖bLp i‖
  let gamma := ‖cLp‖
  have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
  have hgamma : 0 ≤ gamma := norm_nonneg cLp
  have hbLp : ∀ i, ‖bLp i‖ ≤ beta := fun i ↦
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (bLp j)) (Finset.mem_univ i)
  let mu := coerciveShift (n := n) alpha beta gamma
  let S₀ := fullDivergenceWeakSolveCLM aLp bLp cLp hA hbeta hgamma hbLp le_rfl (le_refl mu)
  have hweak (f : DerivLp n 2 Ω) :
      IsWeakShiftedFullDivergenceSolution aLp bLp cLp mu f 0 (S₀ f) :=
    fullDivergenceWeakSolveCLM_isWeakSolution aLp bLp cLp hA hbeta hgamma hbLp le_rfl
      (le_refl mu) hopen f
  have hreg (i : ι) : HasHigherSolutionLift (order i) S₀ := by
    obtain ⟨_, _, hR⟩ := exists_global_higherOrder_estimate_of_contDiffUpToBoundary (order i)
      hopen hbounded (hgraph i) a b c (haHigher i) (hbHigher i) (hcHigher i)
      mu alpha halpha hell
    intro F
    obtain ⟨W, hW, _⟩ := hR F (S₀ (wkpBaseCoordinateCLM F)) (hweak _)
    exact ⟨W, hW⟩
  refine ⟨mu, fun r ↦ higherSolutionOperator hopen S₀ (hreg r), ?_⟩
  intro r F u hu
  have heq := eq_fullDivergenceWeakSolveCLM aLp bLp cLp hA hbeta hgamma hbLp le_rfl
    (le_refl mu) (wkpBaseCoordinateCLM F) hu
  rw [higherSolutionOperator_base, higherWeakSolutionBaseCLM_apply, ← heq]

/-- One coefficient-dependent shift gives the complete bounded higher solver
family. Every shifted weak solution agrees with the corresponding lift. -/
theorem exists_classical_full_higher_lifts
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ k : ℕ, ∀ i j, ContDiffUpToBoundary k (fun x ↦ a x i j) Ω)
    (hb : ∀ k : ℕ, ∀ i, ContDiffUpToBoundary k (b i) Ω)
    (hc : ∀ k : ℕ, ContDiffUpToBoundary k c Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ (mu : ℝ)
      (S : ∀ r : ℕ, W^{r,2}(Ω) →L[ℝ] W^{r + 2,2}(Ω)),
      ∀ (r : ℕ) (F : W^{r,2}(Ω)) (u : H¹₀(Ω)),
        IsWeakShiftedFullDivergenceSolution
          (fun i j ↦ (ha 1 i j).toLp hopen hbounded ∞)
          (fun i ↦ (hb 1 i).toLp hopen hbounded ∞) ((hc 0).toLp hopen hbounded ∞)
          mu (wkpBaseCoordinateCLM F) 0 u →
        wkpBaseCoordinateCLM (S r F) = baseCoordCLM u := by
  exact exists_classical_full_higher_lifts_family id hopen hbounded
    (fun r ↦ hgraph (r + 2)) a b c (ha 1) (hb 1) (hc 0)
    (fun r ↦ ha (r + 1)) (fun r ↦ hb (r + 1)) (fun r ↦ hc (r + 1)) halpha hell

end SobolevSpace.GraphSpace.BoundaryRegularity
