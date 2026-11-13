/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Dirichlet
public import PDE.Analysis.WeakSequentialCompactness
public import PDE.Analysis.Operator.CompactConvergence
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.ZeroBoundaryFiniteExponent
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Compactness of the oscillatory Dirichlet solutions

The energy estimate makes the periodic Dirichlet solutions bounded in
the canonical zero-boundary Sobolev space. Reflexivity and the Rellich
theorem give one subsequence converging weakly in `H¹₀` and strongly in `L²`.
No regularity of the boundary or symmetry of the coefficient is assumed.
The oscillating-test argument of `PeriodicCell.LimitEquation` identifies the
subsequential limit with the effective solution.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω) (f : DerivLp n 2 Ω)

include hΩo

/-- The oscillatory solution family is bounded in the `H¹₀` space. -/
theorem isBounded_range_rescaledDirichletSolution {ι : Type*}
    (ε : ι → ℝ) (hε : ∀ j, ε j ≠ 0) :
    Bornology.IsBounded (range (fun j ↦
      rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j) f)) := by
  obtain ⟨M, hM⟩ := exists_rescaledDirichletSolution_norm_bound A hα hA hn hΩ hΩo f
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨M, fun _ ⟨j, hj⟩ ↦ hj ▸ hM (ε j) (hε j)⟩

/-- Every sequence of oscillatory solutions has a common weak Sobolev and
strong value subsequence. This compactness statement does not identify the limit. -/
theorem exists_subseq_rescaledDirichletSolution
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≠ 0) :
    ∃ (u : H¹₀(Ω)) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (fun j ↦ toWeakSpace ℝ (H¹₀(Ω))
        (rescaledDirichletSolution A hα hA hn hΩ (ε (ns j)) (hε (ns j)) f)) atTop
        (𝓝 (toWeakSpace ℝ (H¹₀(Ω)) u)) ∧
      Tendsto (fun j ↦ baseCoordCLM
        (rescaledDirichletSolution A hα hA hn hΩ (ε (ns j)) (hε (ns j)) f)) atTop
        (𝓝 (baseCoordCLM u)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 Ω) := Lp.SecondCountableTopology
  obtain ⟨u, ns, hns, hu⟩ :=
    PDE.Analysis.WeakCompactness.exists_subseq_tendsto_weak_of_isBounded
      (PDE.Analysis.inclusionInDoubleDual_surjective (H := H¹₀(Ω)))
      (fun j ↦ rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j) f)
      (isBounded_range_rescaledDirichletSolution A hα hA hn hΩ hΩo f ε hε)
  refine ⟨u, ns, hns, hu, ?_⟩
  apply PDE.Analysis.tendsto_compactOperator_of_tendsto_weak
    (baseCoordCLM (n := n) (Ω := Ω)) _ hu
  exact RellichKondrachov.wkp0BaseCoordinate_isCompactOperator_of_bounded
    hΩo.measurableSet hΩ (by norm_num)

end PDE.Elliptic.Homogenization.PeriodicCell
