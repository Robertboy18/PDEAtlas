/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration

/-!
# General subcritical Sobolev inequalities on C¹ domains

First-order embeddings of the derivative coordinates give the higher-order
inclusion. The closed graph theorem supplies its norm bound. Only the first-order
extension constructed from the boundary graphs is used.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace
open scoped ENNReal Sobolev

/-- The exact subcritical Sobolev exponent and its full norm estimate on a bounded
open C¹ domain, including exponent one and order zero. -/
theorem exists_subcritical_bound_of_hasC1GraphBoundary
    {n k : ℕ} {p q : NNReal} {Ω : Set (ℝ^n)}
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hn : 0 < n) (hp : 1 ≤ p) (hsub : (k : ℝ) * p < n)
    (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (k : ℝ) * (n : ℝ)⁻¹)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,(p : ℝ≥0∞)}(Ω),
      MemLp (baseRepresentative U) (q : ℝ≥0∞) (domainMeasure n Ω) ∧
      eLpNorm (baseRepresentative U) (q : ℝ≥0∞) (domainMeasure n Ω) ≤
        ENNReal.ofReal (C * ‖U‖) := by
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  rw [eq_higherOrderExponent_of_inv_eq hp0 hsub hq]
  have : Fact (0 < n) := ⟨hn⟩
  have : Fact (1 ≤ (higherOrderExponent n k p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_higherOrderExponent hp hsub⟩
  obtain ⟨atlas, _, _⟩ :=
    (Boundary.hasContDiffGraphBoundary_one_iff.mpr hboundary).exists_c1ExtensionAtlas
      le_rfl hopen hbounded
  let := atlas
  have hmem (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
      MemLp (baseRepresentative U) (higherOrderExponent n k p : ℝ≥0∞)
        (domainMeasure n Ω) :=
    Embedding.base_memLp_iterated hp hsub U
  obtain ⟨C, hC, hbound⟩ := exists_pos_eLpNorm_bound_of_memLp hmem
  exact ⟨C, hC, fun U ↦ ⟨hmem U, hbound U⟩⟩

end SobolevSpace.Inequalities
