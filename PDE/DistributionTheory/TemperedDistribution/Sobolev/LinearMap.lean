/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Continuous linear maps on vector-valued Bessel distributions

Mathlib's postcomposition operation commutes with the Bessel potential
and with the embedding of `Lp`. Consequently bounded linear maps preserve
fractional Sobolev membership, for real orders and all exponents in `[1,∞]`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace TemperedDistribution

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A constant map on the values commutes with the Bessel multiplier. -/
theorem postcomp_besselPotential (L : F →L[ℂ] G) (s : ℝ) (T : 𝓢'(E, F)) :
    PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L (besselPotential E F s T) =
      besselPotential E G s (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L T) := by
  ext φ
  rfl

variable [CompleteSpace F] [CompleteSpace G]

/-- Postcomposition of an `Lp` distribution is the distribution of its
mapped `Lp` class. -/
theorem postcomp_toTemperedDistribution
    (L : F →L[ℂ] G) {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (f : Lp F p (volume : Measure E)) :
    PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L (f : 𝓢'(E, F)) =
      (L.compLpL p volume f : 𝓢'(E, G)) := by
  ext φ
  have := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have hφf : Integrable (fun x ↦ φ x • f x) :=
    memLp_one_iff_integrable.mp ((φ.memLp (1 - p⁻¹)⁻¹).smul (Lp.memLp f))
  change L ((f : 𝓢'(E, F)) φ) = (L.compLpL p volume f : 𝓢'(E, G)) φ
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    ← L.integral_comp_comm hφf]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLpL f] with x hx
  rw [hx, map_smul]

/-- Continuous linear maps preserve every real Sobolev order. -/
theorem MemSobolev.postcomp
    (L : F →L[ℂ] G) {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {T : 𝓢'(E, F)} (hT : MemSobolev s p T) :
    MemSobolev s p (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L T) := by
  obtain ⟨f, hf⟩ := hT
  refine ⟨L.compLpL p volume f, ?_⟩
  rw [← postcomp_besselPotential, hf, postcomp_toTemperedDistribution]

end TemperedDistribution
