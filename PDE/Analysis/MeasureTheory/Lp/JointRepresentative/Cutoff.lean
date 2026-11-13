/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Mixed
public import PDE.Analysis.MeasureTheory.Lp.Cutoff

/-!
# Cutoffs of mixed Lebesgue representatives

Cutting off the outer variable of a mixed Lp class agrees almost everywhere
with cutting off its actual joint representative. The proof transports through
both quotient levels, including the zero representative outside the cutoff.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α β E 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [_root_.SecondCountableTopology E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  {μ : Measure α} {ν : Measure β} [SFinite ν]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A cutoff in the outer variable is the same cutoff of the joint representative. -/
theorem jointRepresentative_indicatorCLM {s : Set α} (hs : MeasurableSet s)
    (u : Lp (Lp E p ν) q μ) :
    jointRepresentative (indicatorCLM 𝕜 hs u) =ᵐ[μ.prod ν]
      (Prod.fst ⁻¹' s).indicator (jointRepresentative u) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_jointRepresentative _) ((measurable_jointRepresentative u).indicator
      (hs.preimage measurable_fst)))).mpr
  filter_upwards [indicatorCLM_coeFn (𝕜 := 𝕜) hs u] with t ht
  by_cases hts : t ∈ s
  · filter_upwards [jointRepresentative_section (indicatorCLM 𝕜 hs u) t,
      jointRepresentative_section u t] with x hcut hu
    rw [hcut, ht, indicator_of_mem hts]
    exact hu.symm.trans (indicator_of_mem (show (t, x) ∈ Prod.fst ⁻¹' s from hts) _).symm
  · filter_upwards [jointRepresentative_section (indicatorCLM 𝕜 hs u) t,
      Lp.coeFn_zero E p ν] with x hcut hz
    rw [hcut, ht, indicator_of_notMem hts, hz]
    exact (indicator_of_notMem (show (t, x) ∉ Prod.fst ⁻¹' s from hts) _).symm

end MeasureTheory.Lp
