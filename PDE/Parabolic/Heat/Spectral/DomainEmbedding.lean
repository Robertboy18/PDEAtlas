/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Iteration

/-!
# Higher classical representatives on bounded graph domains

Finite volume lowers the Sobolev exponent from two to one. Spending `n` derivatives
in the critical Sobolev iteration then gives a `C^{j,γ}` representative
from `H^{j+1+n}`, for any strict Hölder exponent. The closed-graph embedding controls
all classical derivatives in the uniform norm.

This deliberately nonoptimal derivative count is convenient for heat smoothing,
where every Sobolev order is available at positive time.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Inequalities HolderSpace
open MeasureTheory
open scoped Sobolev ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}

/-- Geometric `C¹` boundary regularity supplies classical representatives at the indicated
Sobolev order. The derivative count is sufficient, without claiming optimality. -/
theorem exists_domainHolder (j : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 1 Ω) (hγ : (γ : ℝ) < 1)
    (U : W^{j + 1 + n,2}(Ω)) :
    ∃ F : CKGammaOn n j Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  obtain ⟨atlas, _, _⟩ := hgraph.exists_c1ExtensionAtlas le_rfl hopen hbounded
  let := atlas
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  let V := lowerExponentOfFiniteMeasure (q := 1) (by norm_num : (1 : ℝ≥0∞) ≤ 2) U
  obtain ⟨F, hF⟩ := exists_higherHolder_of_critical_iteration (p := 1)
    (Fact.out : 0 < n) (by simp) hγ V
  refine ⟨F, hF.trans ?_⟩
  exact lowerExponentOfFiniteMeasure_apply_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    U (baseIndex n (j + 1 + n))

/-- The bounded classical embedding is derived from the analytic representative theorem. -/
def domainHolderCLM (j : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 1 Ω) (hγ : (γ : ℝ) < 1) :
    W^{j + 1 + n,2}(Ω) →L[ℝ] CKGammaOn n j Ω γ := by
  haveI : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  exact holderEmbeddingCLMOfExists hopen (exists_domainHolder j hopen hbounded hgraph hγ)

/-- The bounded classical embedding preserves the underlying equivalence class. -/
theorem domainHolderCLM_ae (j : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 1 Ω) (hγ : (γ : ℝ) < 1)
    (U : W^{j + 1 + n,2}(Ω)) :
    (domainHolderCLM j hopen hbounded hgraph hγ U).interiorDerivative 0
      =ᵐ[domainMeasure n Ω] baseRepresentative U :=
  holderRepresentativeOfExists_ae (exists_domainHolder j hopen hbounded hgraph hγ) U

end HeatEquation
