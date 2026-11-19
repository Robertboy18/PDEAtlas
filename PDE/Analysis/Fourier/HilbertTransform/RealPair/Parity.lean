/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Reflection
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.ContinuousRepresentative

/-!
# Parity of real Hilbert pairs

The spectral Hilbert transform of an almost-everywhere odd input is almost everywhere
even, and a continuous output representative is even at every point.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis

/-- The spectral Hilbert transform reverses almost-everywhere odd parity. -/
theorem IsHilbertPair.ae_even_of_ae_odd {f c : ℝ → ℝ} (hp : IsHilbertPair f c)
    (hf : ∀ᵐ x ∂volume, f (-x) = -f x) :
    ∀ᵐ x ∂volume, c (-x) = c x := by
  have hinput : (fun x ↦ -f (-x)) =ᵐ[volume] f := by
    filter_upwards [hf] with x hx
    simp only [hx, neg_neg]
  exact (hp.neg_reflect.congr_ae hinput EventuallyEq.rfl).ae_eq_right hp

/-- Continuity upgrades spectral parity to equality at every spatial point. -/
theorem IsHilbertPair.even_of_ae_odd {f c : ℝ → ℝ} (hp : IsHilbertPair f c)
    (hf : ∀ᵐ x ∂volume, f (-x) = -f x) (hc : Continuous c) :
    Function.Even c :=
  congrFun (Measure.eq_of_ae_eq (hp.ae_even_of_ae_odd hf) (hc.comp continuous_neg) hc)

end PDE.Analysis
