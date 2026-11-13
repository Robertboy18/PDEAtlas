/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.WeakDerivative
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakBound

/-!
# Pointwise Hilbert bounds from weak H¹ input

The concrete spectral Hilbert transform commutes with the weak derivative.
Applying the one-dimensional weak Sobolev bound to a continuous Hilbert
representative gives `|Hω(x)| ≤ ‖ω‖₂ + ‖η‖₂` when `Dω = η ∈ L²`.

Neither classical differentiability nor compact support of the input is
required. Continuity of the chosen output representative makes the estimate
pointwise rather than almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory PDE.Analysis.Evolution
open scoped ENNReal

namespace PDE.Analysis

/-- A continuous Hilbert representative is bounded at every point by
the input's `L²` norm and the `L²` norm of its weak derivative. -/
theorem IsHilbertPair.norm_le_eLpNorm_add_weakDerivative
    {omega eta v : ℝ → ℝ} (h : IsHilbertPair omega v) (hv : Continuous v)
    (heta : MemLp eta 2 volume)
    (hweak : HasWeakTimeDerivativeOn Set.univ omega eta) (x : ℝ) :
    ‖v x‖ ≤ (eLpNorm omega 2 volume).toReal + (eLpNorm eta 2 volume).toReal := by
  obtain ⟨w, hw, hderiv⟩ := h.exists_hasWeakTimeDerivativeOn heta hweak
  have hbound := hderiv.norm_apply_le_eLpNorm_toReal_add hv
    (by norm_num : (1 : ℝ≥0∞) < 2) h.memLp_right hw.memLp_right x
  rwa [h.eLpNorm_eq, hw.eLpNorm_eq] at hbound

end PDE.Analysis
