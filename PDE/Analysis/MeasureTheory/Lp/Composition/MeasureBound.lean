/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Bounded composition on Lp spaces

Composition by a measurable map is bounded on `Lᵖ` when its pushforward measure is
bounded by a finite multiple of the target measure. We compose Mathlib's change of
measure operator with its measure-preserving pullback. This separates the measure
estimate from the construction on almost-everywhere classes.

The same operator serves changes of coordinates and reflected normal dilations.
The norm estimate includes `p = ∞`; for an exact positive measure factor, it becomes
an equality on each function.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} {p c : ℝ≥0∞} [Fact (1 ≤ p)]
  (f : α → β) (hf : Measurable f) (hc : c ≠ ∞)
  (hmap : Measure.map f μ ≤ c • ν)

/-- Composition on Lp classes under a finite pushforward-measure bound. -/
def compMeasureLeSMul : Lp E p ν →L[ℝ] Lp E p μ :=
  (compMeasurePreservingₗᵢ (𝕜 := ℝ) (p := p) (E := E) f
    (⟨hf, rfl⟩ : MeasurePreserving f μ (Measure.map f μ))).toContinuousLinearMap.comp
      (LpToLpOfMeasureLeSMul hc hmap)

/-- The bounded composition operator represents ordinary function composition. -/
theorem coeFn_compMeasureLeSMul (u : Lp E p ν) :
    ⇑(compMeasureLeSMul f hf hc hmap u) =ᵐ[μ] u ∘ f := by
  have hpres : MeasurePreserving f μ (Measure.map f μ) := ⟨hf, rfl⟩
  exact (coeFn_compMeasurePreserving _ hpres).trans
    (hpres.quasiMeasurePreserving.ae_eq_comp (coeFn_LpToLpOfMeasureLeSMul hc hmap u))

/-- The pushforward bound contributes its `1/p` power to the composition norm. -/
theorem norm_compMeasureLeSMul_apply_le (u : Lp E p ν) :
    ‖compMeasureLeSMul f hf hc hmap u‖ ≤ c.toReal ^ (1 / p).toReal * ‖u‖ := by
  let M := LpToLpOfMeasureLeSMul (E := E) (p := p) hc hmap
  change ‖(compMeasurePreservingₗᵢ _ _ _ : _ →ₗᵢ[ℝ] _) (M u)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact (M.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_LpToLpOfMeasureLeSMul_le hc hmap) (norm_nonneg u))

/-- An exact positive pushforward factor gives the exact norm of every pullback.
The positivity condition also keeps this valid at `p = ∞`. -/
theorem norm_compMeasureLeSMul_apply_eq (hc₀ : c ≠ 0)
    (heq : Measure.map f μ = c • ν) (u : Lp E p ν) :
    ‖compMeasureLeSMul f hf hc hmap u‖ = c.toReal ^ (1 / p).toReal * ‖u‖ := by
  have hu : AEStronglyMeasurable u (Measure.map f μ) :=
    ((Lp.memLp u).of_measure_le_smul hc hmap).aestronglyMeasurable
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_compMeasureLeSMul f hf hc hmap u),
    ← eLpNorm_map_measure hu hf.aemeasurable, heq,
    eLpNorm_smul_measure_of_ne_zero hc₀, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_rpow, Lp.norm_def]

end MeasureTheory.Lp
