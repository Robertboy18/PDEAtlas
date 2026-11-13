/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.WeakDerivative.RealLine
public import PDE.Analysis.Fourier.HilbertTransform.RealPair

/-!
# Weak differentiation of real Hilbert pairs

An `L²` weak derivative of the input yields an `L²` weak derivative of its
Hilbert representative. The derivative itself forms the concrete spectral
Hilbert pair with the input derivative. No differentiability or continuity
of either representative is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory PDE.Analysis.Evolution
open scoped SchwartzMap LineDeriv

namespace PDE.Analysis

/-- Two Hilbert pairs transport an input weak-derivative identity to the
output representatives. -/
theorem IsHilbertPair.hasWeakTimeDerivativeOn
    {omega eta v w : ℝ → ℝ}
    (h : IsHilbertPair omega v) (h' : IsHilbertPair eta w)
    (hweak : HasWeakTimeDerivativeOn Set.univ omega eta) :
    HasWeakTimeDerivativeOn Set.univ v w := by
  obtain ⟨F, hF, hv⟩ := h
  obtain ⟨G, hG, hw⟩ := h'
  apply (hasWeakTimeDerivativeOn_re_hilbertTransform_of_weak hweak hF hG).congr_ae
  · filter_upwards [hv] with x hx
    simpa using (congrArg Complex.re hx).symm
  · filter_upwards [hw] with x hx
    simpa using (congrArg Complex.re hx).symm

/-- Every Hilbert pair with an `L²` weak input derivative has an `L²`
weak output derivative, and these derivatives themselves form a
spectral Hilbert pair. Only the input derivative identity is assumed. -/
theorem IsHilbertPair.exists_hasWeakTimeDerivativeOn
    {omega eta v : ℝ → ℝ} (h : IsHilbertPair omega v)
    (heta : MemLp eta 2 volume)
    (hweak : HasWeakTimeDerivativeOn Set.univ omega eta) :
    ∃ w : ℝ → ℝ, IsHilbertPair eta w ∧
      HasWeakTimeDerivativeOn Set.univ v w := by
  obtain ⟨F, hF, hv⟩ := h
  have hGmem : MemLp (fun x ↦ (eta x : ℂ)) 2 volume := heta.ofReal
  let G : ComplexL2 := hGmem.toLp _
  have hG : (fun x ↦ (eta x : ℂ)) =ᵐ[volume] G := hGmem.coeFn_toLp.symm
  have hd := lineDeriv_hilbertTransform (lineDeriv_of_hasWeakTimeDerivativeOn hweak hF hG)
  have hreal : (fun x ↦ (hilbertTransform F x).im) =ᵐ[volume] 0 := by
    filter_upwards [hv] with x hx
    simpa using (congrArg Complex.im hx).symm
  have hdreal := ae_im_lineDeriv_eq_zero hd hreal
  let w : ℝ → ℝ := fun x ↦ (hilbertTransform G x).re
  have hpair : IsHilbertPair eta w := by
    refine ⟨G, hG, ?_⟩
    filter_upwards [hdreal] with x hx
    apply Complex.ext
    · rfl
    · simpa using hx.symm
  refine ⟨w, hpair, ?_⟩
  apply (hasWeakTimeDerivativeOn_re_of_lineDeriv hd).congr_ae _ Filter.EventuallyEq.rfl
  filter_upwards [hv] with x hx
  simpa using (congrArg Complex.re hx).symm

end PDE.Analysis
