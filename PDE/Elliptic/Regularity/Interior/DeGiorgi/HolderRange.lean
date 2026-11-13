/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.RangeDecay
import PDE.Elliptic.Regularity.Interior.DeGiorgi.PowerDecay

/-!
# Power decay of the essential range at every radius

Geometric oscillation decay determines a positive Hölder exponent.
Choosing the adjacent geometric radius gives the corresponding estimate at
an arbitrary smaller radius. The exponent and constant are uniform over the
measurable uniformly elliptic weak solutions.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The essential range of an elliptic H¹ weak solution decays as
`(r/R)^γ` at every interior radius, for a uniform positive exponent `γ < 1`.
An initial essential bound supplies its amplitude; local boundedness derives
that bound from H¹ data. -/
theorem exists_holder_essential_range_decay
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ (γ : ℝ≥0) (C : ℝ), 0 < γ ∧ γ < 1 ∧ 0 < C ∧
      ∀ (W : Set (ℝ^n)) (A : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ W →
      ∀ (c M : ℝ), 0 < M →
        (∀ᵐ x ∂volume.restrict (ball z R), |wkpBaseCoordinateCLM u x - c| ≤ M) →
      ∀ (r : ℝ), 0 < r → r ≤ R → ∃ d : ℝ,
        ∀ᵐ x ∂volume.restrict (ball z r),
          |wkpBaseCoordinateCLM u x - d| ≤ C * (r / R) ^ (γ : ℝ) * M := by
  obtain ⟨ρ, hρ, hρ1, hdecay⟩ := exists_geometric_oscillation_decay hq2 hq hα hΛ
  obtain ⟨γ, C, hγ, hγ1, hC, hpower⟩ :=
    PDE.Elliptic.Regularity.DeGiorgi.exists_holder_range_decay_of_geometric_decay
      (μ := (volume : Measure ℝ^n)) hρ hρ1
  refine ⟨γ, C, hγ, hγ1, hC, ?_⟩
  intro W A hAΛ hA u hu z R hR hball c M hM hbound
  exact hpower (wkpBaseCoordinateCLM u) z R hR M hM
    (hdecay W A hAΛ hA u hu z R hR hball c M hM hbound)

end SobolevSpace.GraphSpace
