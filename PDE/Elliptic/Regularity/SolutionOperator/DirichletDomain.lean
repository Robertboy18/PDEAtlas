/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalBoundaryData
public import PDE.Elliptic.Regularity.SolutionOperator.FullLoad
public import PDE.Elliptic.Variational.Operator.Dirichlet

/-!
# The classical domain of the full Dirichlet operator

`C²` boundary geometry and principal coefficients that are `C¹` up to the boundary
identify the variational operator domain with `H² ∩ H¹₀`. Elliptic regularity gives one
inclusion; integration by parts gives the converse and the exact action `-L`.
Bounded drift and potential are retained throughout.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open PDE.Analysis.Evolution
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Integration by parts places every zero-boundary `H²` field in the full operator graph. -/
theorem mem_negativeDirichletOperator_graph_fullStrongLoad (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (G : W^{2,2}(Ω)) (u : H¹₀(Ω))
    (hbase : wkpBaseCoordinateCLM G = baseCoordCLM u) :
    (baseCoordCLM u, -fullStrongLoad A b c G) ∈
      (negativeDirichletOperator hopen (coefficientBase A) b c).graph := by
  apply (mem_negativeDirichletOperator_graph_iff hopen _ b c _ _).2
  exact ⟨u, rfl, by simpa only [neg_neg] using
    fullStrongLoad_isWeakShiftedFullDivergenceSolution hopen A b c G u hbase⟩

variable [Fact (0 < n)]
variable (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
  (a : ℝ^n → Fin n → Fin n → ℝ)
  (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
  (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
  (α : ℝ) (hα : 0 < α)
  (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) α)

include hgraph hα hell

/-- The full operator graph has exactly the `H² ∩ H¹₀` representatives and action `-L`. -/
theorem mem_negativeDirichletOperator_graph_iff_h2 (x f : DerivLp n 2 Ω) :
    (x, f) ∈
      (negativeDirichletOperator hopen (fun i j ↦ (ha i j).toLp hopen hbounded ∞) b c).graph ↔
      ∃ (u : H¹₀(Ω)) (G : W^{2,2}(Ω)),
        baseCoordCLM u = x ∧ wkpBaseCoordinateCLM G = x ∧
        f = -fullStrongLoad (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) b c G := by
  let A : Fin n → Fin n → W^{1,∞}(Ω) :=
    fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
  have hcoeff : coefficientBase A = fun i j ↦ (ha i j).toLp hopen hbounded ∞ := by
    funext i j
    exact (ha i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
  constructor
  · intro h
    obtain ⟨u, hu, hweak⟩ := (mem_negativeDirichletOperator_graph_iff hopen _ b c x f).1 h
    obtain ⟨_, _, hreg⟩ :=
      exists_global_h2_estimate_of_contDiffUpToBoundary hopen hbounded hgraph a ha b c
        0 α hα hell
    obtain ⟨G, hG, _⟩ := hreg (-f) u hweak
    refine ⟨u, G, hu, hG.trans hu, ?_⟩
    have hload := mem_negativeDirichletOperator_graph_fullStrongLoad hopen A b c G u hG
    rw [hcoeff, hu] at hload
    exact (negativeDirichletOperator hopen _ b c).mem_graph_snd_inj h hload rfl
  · rintro ⟨u, G, hu, hG, rfl⟩
    have hload :=
      mem_negativeDirichletOperator_graph_fullStrongLoad hopen A b c G u (hG.trans hu.symm)
    rwa [hcoeff, hu] at hload

/-- The full operator domain equals the intersection of `H¹₀` and `H²` inside `L²`. -/
theorem mem_negativeDirichletOperator_domain_iff_h2 (x : DerivLp n 2 Ω) :
    x ∈ (negativeDirichletOperator hopen (fun i j ↦ (ha i j).toLp hopen hbounded ∞) b c).domain ↔
      (∃ u : H¹₀(Ω), baseCoordCLM u = x) ∧
        ∃ G : W^{2,2}(Ω), wkpBaseCoordinateCLM G = x := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨u, G, hu, hG, _⟩ :=
      (mem_negativeDirichletOperator_graph_iff_h2 hopen hbounded hgraph a ha b c α hα hell x f).1 hf
    exact ⟨⟨u, hu⟩, ⟨G, hG⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨G, hG⟩⟩
    refine ⟨-fullStrongLoad
      (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) b c G, ?_⟩
    apply (mem_negativeDirichletOperator_graph_iff_h2
      hopen hbounded hgraph a ha b c α hα hell x _).2
    exact ⟨u, G, hu, hG, rfl⟩

/-- An `L²` representation of the full weak form is equivalent to an `H²` representative
with exactly that strong load. This formulation keeps the given `H¹₀` field fixed. -/
theorem fullDivergenceForm_eq_pivotToDual_iff_h2
    (u : H¹₀(Ω)) (f : DerivLp n 2 Ω) :
    fullDivergenceForm
        (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hopen hbounded ∞))
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u =
      (h10L2GelfandTriple hopen).pivotToDual f ↔
      ∃ G : W^{2,2}(Ω), wkpBaseCoordinateCLM G = baseCoordCLM u ∧
        fullStrongLoad (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) b c G = f := by
  constructor
  · intro h
    have hgraph' : (baseCoordCLM u, -f) ∈
        (negativeDirichletOperator hopen
          (fun i j ↦ (ha i j).toLp hopen hbounded ∞) b c).graph := by
      rw [negativeDirichletOperator, GelfandTriple.mem_formOperator_graph_iff]
      exact ⟨u, rfl, by simpa only [map_neg, neg_neg] using h⟩
    obtain ⟨_, G, _, hG, hf⟩ := (mem_negativeDirichletOperator_graph_iff_h2
      hopen hbounded hgraph a ha b c α hα hell _ _).1 hgraph'
    exact ⟨G, hG, (neg_injective hf).symm⟩
  · rintro ⟨G, hG, hf⟩
    have hcoeff :
        coefficientBase (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) =
          fun i j ↦ (ha i j).toLp hopen hbounded ∞ := by
      funext i j
      exact (ha i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
    ext v
    rw [← hcoeff, fullDivergenceForm_eq_fullStrongLoad hopen _ b c G u hG v, hf]
    rfl

end SobolevSpace.GraphSpace.BoundaryRegularity
