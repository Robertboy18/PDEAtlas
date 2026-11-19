/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Multiplication of Lp distributions and their representatives

Multiplying an Lp distribution by a smooth function of temperate growth gives
another Lp distribution precisely when the corresponding representatives agree
almost everywhere. The input and output exponents may differ.

The product need not be globally integrable. Local integrability suffices to
recover its values from compactly supported smooth tests.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff ENNReal SchwartzMap

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth multiplier can be moved from the test function to the Lp representative. -/
private theorem smulLeft_toTemperedDistribution_apply {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (u : Lp F p μ) (φ : 𝓢(E, ℂ)) :
    TemperedDistribution.smulLeftCLM F g (u : 𝓢'(E, F)) φ =
      ∫ x, φ x • (g x • u x) ∂μ := by
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards with x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  change (g x * φ x) • u x = φ x • (g x • u x)
  rw [mul_comm, mul_smul]

variable [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]
    {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Equality between a smooth multiple of an Lp distribution and another Lp
distribution is equivalent to equality of their representatives almost everywhere.
Both exponents lie in `[1, ∞]`. Local finiteness of the measure and continuity of
the multiplier give the local integrability needed for distributional uniqueness. -/
theorem smulLeft_toTemperedDistribution_eq_iff {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {u : Lp F p μ} {v : Lp F q μ} :
    TemperedDistribution.smulLeftCLM F g (u : 𝓢'(E, F)) = (v : 𝓢'(E, F)) ↔
      (fun x ↦ g x • u x) =ᵐ[μ] (v : E → F) := by
  constructor
  · intro h
    refine ae_eq_of_integral_contDiff_smul_eq
      (LocallyIntegrable.continuous_smul hg.1.continuous
        ((Lp.memLp u).locallyIntegrable (Fact.out : 1 ≤ p)))
      ((Lp.memLp v).locallyIntegrable (Fact.out : 1 ≤ q)) ?_
    intro ψ hψ hcs
    have hcs' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hcs.comp_left rfl
    have hψ' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
    have htest := congrArg (fun T : 𝓢'(E, F) ↦ T (hcs'.toSchwartzMap hψ')) h
    rw [smulLeft_toTemperedDistribution_apply hg u, Lp.toTemperedDistribution_apply] at htest
    change (∫ x, (ψ x : ℂ) • (g x • u x) ∂μ) =
      ∫ x, (ψ x : ℂ) • v x ∂μ at htest
    simpa only [Complex.coe_smul] using htest
  · intro h
    ext φ
    rw [smulLeft_toTemperedDistribution_apply hg u, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [h] with x hx using congrArg (fun z : F ↦ φ x • z) hx

end MeasureTheory.Lp
