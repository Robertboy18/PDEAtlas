/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import PDE.Analysis.MeasureTheory.Lp.RadialPower.Smul

/-!
# Singular radial weights on Schwartz functions

Schwartz functions belong to every finite Lᵖ space and are bounded. Negative
radial powers therefore preserve Lᵖ membership whenever the local dimensional
criterion holds. This supplies, for example, the square-integrability of a
Schwartz datum divided by frequency in dimensions above two.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Negative radial powers preserve the finite Lᵖ membership of a Schwartz function
when the local singularity satisfies the dimensional integrability criterion. -/
theorem memLp_norm_sub_rpow_smul (f : 𝓢(E, F))
    (hd : 1 ≤ Module.finrank ℝ E) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞)
    {a : ℝ} (ha : a ≤ 0) (hap : -a * p.toReal < (Module.finrank ℝ E : ℝ)) (z : E) :
    MemLp (fun x ↦ ‖x - z‖ ^ a • f x) p μ :=
  (f.memLp p μ).norm_sub_rpow_smul (f.memLp_top μ) hd hp hp' ha hap z

end SchwartzMap
