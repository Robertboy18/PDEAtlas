/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
import PDE.Analysis.Fourier.HilbertTransform.Translation

/-!
# Translation of real Hilbert pairs

The spectral covariance under translation descends to real representatives: if `v` represents
the Hilbert transform of `ω`, then `v (· - a)` represents the Hilbert transform of `ω (· - a)`,
for every real `a` (`IsHilbertPair.translate`). Translations preserve null sets, so the
almost-everywhere relation passes to the translated representatives, and the `L²` statement is
`hilbertTransform_compMeasurePreserving_add_right`.

The statement is a standard fact on the Hilbert transform, and the proof follows no particular
source.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis

/-- **Translation of a Hilbert pair.** If `v` represents the Hilbert transform of `ω`, then
`v (· - a)` represents the Hilbert transform of `ω (· - a)`, for every real `a`. -/
theorem IsHilbertPair.translate {ω v : ℝ → ℝ} (h : IsHilbertPair ω v) (a : ℝ) :
    IsHilbertPair (fun x ↦ ω (x - a)) (fun x ↦ v (x - a)) := by
  obtain ⟨f, hω, hv⟩ := h
  have hp := measurePreserving_add_right (volume : Measure ℝ) (-a)
  simp only [sub_eq_add_neg]
  refine ⟨Lp.compMeasurePreserving (· + -a) hp f, ?_, ?_⟩
  · exact (hp.quasiMeasurePreserving.ae_eq_comp hω).trans
      (Lp.coeFn_compMeasurePreserving f hp).symm
  · rw [hilbertTransform_compMeasurePreserving_add_right]
    exact (hp.quasiMeasurePreserving.ae_eq_comp hv).trans
      (Lp.coeFn_compMeasurePreserving _ hp).symm

end PDE.Analysis
