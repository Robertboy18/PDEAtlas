/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
public import PDE.Analysis.Fourier.HilbertTransform.Reflection

/-!
# Reflection of a real Hilbert pair

The Hilbert transform reverses parity. Signed reflection of its input therefore
reflects its output without a sign. This follows from the spectral multiplier
and applies to any real L² pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis

/-- Signed reflection of the vorticity reflects its concrete Hilbert transform
without an output sign. -/
theorem IsHilbertPair.neg_reflect {f g : ℝ → ℝ} (h : IsHilbertPair f g) :
    IsHilbertPair (fun x ↦ -f (-x)) (fun x ↦ g (-x)) := by
  obtain ⟨F, hf, hg⟩ := h
  refine ⟨-(complexL2Dilation (-1) (by norm_num) F), ?_, ?_⟩
  · filter_upwards [
      (quasiMeasurePreserving_real_dilation (c := -1) (by norm_num)).ae_eq_comp hf,
      coe_complexL2Dilation (-1) (by norm_num) F,
      Lp.coeFn_neg (complexL2Dilation (-1) (by norm_num) F)] with x hx hdil hneg
    simp only [Function.comp_apply, neg_one_mul] at hx hdil
    rw [Complex.ofReal_neg, hneg, Pi.neg_apply, hdil, hx]
  · rw [map_neg, hilbertTransform_complexL2Dilation_neg_one, neg_neg]
    simpa only [Function.comp_def, neg_one_mul] using
      ((quasiMeasurePreserving_real_dilation (c := -1) (by norm_num)).ae_eq_comp hg).trans
        (coe_complexL2Dilation (-1) (by norm_num) (hilbertTransform F)).symm

end PDE.Analysis
