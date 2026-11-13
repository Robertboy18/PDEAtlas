/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Lp functions taking values in a submodule

An ambient Lp class whose values belong almost everywhere to a submodule lifts
to an Lp class in that submodule, with exactly the same norm. The embedding
detects strong measurability; closedness of the submodule is not needed.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal

/-- An almost-everywhere submodule-valued Lp class has a norm-preserving lift. -/
theorem exists_submodule {α 𝕜 X : Type*} [MeasurableSpace α]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}
    (S : Submodule 𝕜 X) (u : Lp X p μ) (hu : ∀ᵐ x ∂μ, u x ∈ S) :
    ∃ v : Lp S p μ, S.subtypeL.compLpL p μ v = u ∧ ‖v‖ = ‖u‖ := by
  classical
  let f (x : α) : S := if h : u x ∈ S then ⟨u x, h⟩ else 0
  have hcoe : (fun x ↦ (f x : X)) =ᵐ[μ] fun x ↦ u x := by
    filter_upwards [hu] with x hx
    simp only [f, dite_eq_left hx]
  have hm : AEStronglyMeasurable f μ :=
    (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
      ((Lp.aestronglyMeasurable u).congr hcoe.symm)
  have hn : ∀ᵐ x ∂μ, ‖f x‖ = ‖u x‖ := hcoe.mono fun _ hx ↦ congrArg norm hx
  have hf : MemLp f p μ := (Lp.memLp u).of_le hm (hn.mono fun _ hx ↦ hx.le)
  refine ⟨hf.toLp f, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [S.subtypeL.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp, hcoe]
      with x hx hfx hcx
    exact hx.trans ((congrArg S.subtypeL hfx).trans hcx)
  · rw [Lp.norm_toLp, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae hm (Lp.aestronglyMeasurable u) hn)

end MeasureTheory.Lp
