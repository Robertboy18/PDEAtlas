/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder

/-!
# The first jet of a finite Sobolev system as one `Lᵖ` field

`vectorWkpJetCLM` records the Euclidean value `vectorWkpValueCLM` and the flattened matrix
gradient `vectorWkpGradientCLM` of a finite Sobolev system together, as one `Lᵖ` field with the
product norm on `ℝ^m × ℝ^(m * n)`. A coupled integral density acts on this field.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- The Euclidean value and the flattened matrix gradient together, as one `Lᵖ` field with the
product norm on `ℝ^m × ℝ^(m * n)`. This is the state on which a coupled integral density acts. -/
def vectorWkpJetCLM : (Fin m → W^{1,p}(Ω)) →L[ℝ] Lp (ℝ^m × ℝ^(m * n)) p μ :=
  ((firstJetValueCLM.prod firstJetGradientCLM).compLpL p μ).comp vectorWkpFirstJetCLM

/-- The bundled jet agrees almost everywhere with the pair of the value and the gradient. -/
theorem vectorWkpJetCLM_apply_ae (u : Fin m → W^{1,p}(Ω)) :
    vectorWkpJetCLM u =ᵐ[μ] fun x ↦ (vectorWkpValueCLM u x, ∇ u x) := by
  unfold vectorWkpJetCLM vectorWkpValueCLM vectorWkpGradientCLM
  filter_upwards [(firstJetValueCLM.prod firstJetGradientCLM).coeFn_compLpL
      (vectorWkpFirstJetCLM u),
    firstJetValueCLM.coeFn_compLpL (vectorWkpFirstJetCLM u),
    firstJetGradientCLM.coeFn_compLpL (vectorWkpFirstJetCLM u)] with x h hv hg
  rw [ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.comp_apply, hv,
    ContinuousLinearMap.comp_apply, hg]
  rfl

end SobolevSpace.GraphSpace
