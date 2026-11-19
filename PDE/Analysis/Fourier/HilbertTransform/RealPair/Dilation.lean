/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
public import PDE.Analysis.Fourier.HilbertTransform.Dilation

/-!
# Positive dilation of real Hilbert pairs

The spectral covariance under positive spatial dilation descends to real
representatives through preservation of null sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- Positive dilation preserves the concrete `L²` Hilbert-pair relation. -/
theorem IsHilbertPair.dilate {ω v : ℝ → ℝ} {c : ℝ}
    (h : IsHilbertPair ω v) (hc : 0 < c) :
    IsHilbertPair (fun x ↦ ω (c * x)) (fun x ↦ v (c * x)) := by
  obtain ⟨f, hω, hv⟩ := h
  refine ⟨PDE.Analysis.complexL2Dilation c hc.ne' f, ?_, ?_⟩
  · exact ((PDE.Analysis.quasiMeasurePreserving_real_dilation hc.ne').ae_eq_comp
      hω).trans (PDE.Analysis.coe_complexL2Dilation c hc.ne' f).symm
  · rw [PDE.Analysis.hilbertTransform_complexL2Dilation hc]
    exact ((PDE.Analysis.quasiMeasurePreserving_real_dilation hc.ne').ae_eq_comp
      hv).trans (PDE.Analysis.coe_complexL2Dilation c hc.ne' _).symm

end PDE.Analysis
