/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
public import PDE.Analysis.Fourier.HilbertTransform.SpectralBridge

/-!
# The real Hilbert transform on all of L²

The spectral transform of a real Schwartz function agrees with its real
principal value. Density and continuity therefore show that the spectral
transform preserves the real subspace of complex L². Taking its real part
defines a concrete real operator, with no assumed real output representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace PDE.Analysis

/-- The real part of the spectral Hilbert transform of the complex embedding. -/
def realHilbertTransformL2 :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  (Complex.reCLM.compLpL 2 volume).comp
    ((hilbertTransform.toContinuousLinearMap.restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume))

private theorem realHilbertTransformL2_apply (f : Lp ℝ 2 (volume : Measure ℝ)) :
    realHilbertTransformL2 f =
      (Complex.reCLM.compLpL 2 volume)
        (hilbertTransform ((Complex.ofRealCLM.compLpL 2 volume) f)) := rfl

private theorem spectral_real_of_pair (f : Lp ℝ 2 (volume : Measure ℝ)) (g : ℝ → ℝ)
    (h : IsHilbertPair f g) :
    (Complex.ofRealCLM.compLpL 2 volume) (realHilbertTransformL2 f) =
      hilbertTransform ((Complex.ofRealCLM.compLpL 2 volume) f) := by
  obtain ⟨F, hF, hG⟩ := h
  have hinput : (Complex.ofRealCLM.compLpL 2 volume) f = F :=
    Lp.ext ((Complex.ofRealCLM.coeFn_compLpL f).trans hF)
  subst F
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (realHilbertTransformL2 f),
    Complex.reCLM.coeFn_compLpL
      (hilbertTransform ((Complex.ofRealCLM.compLpL 2 volume) f)), hG] with x hx hy hz
  rw [hx, Complex.ofRealCLM_apply, realHilbertTransformL2_apply, hy,
    Complex.reCLM_apply, ← hz, Complex.ofReal_re]

private theorem schwartz_pair (g : 𝓢(ℝ, ℝ)) :
    IsHilbertPair (g.toLp 2) (hilbertPV g) := by
  let F := (Complex.ofRealCLM.compLpL 2 volume) (g.toLp 2)
  have hF : (fun x ↦ (g x : ℂ)) =ᵐ[volume] F := by
    filter_upwards [g.coeFn_toLp 2, Complex.ofRealCLM.coeFn_compLpL (g.toLp 2)]
      with x hx hy
    simpa only [Complex.ofRealCLM_apply, hx] using hy.symm
  refine ⟨F, ?_, hilbertPV_eq_hilbertTransform_ae_schwartz_of_ae g F hF⟩
  exact (Complex.ofRealCLM.coeFn_compLpL (g.toLp 2)).symm

private theorem spectral_real_schwartz (g : 𝓢(ℝ, ℝ)) :
    (Complex.ofRealCLM.compLpL 2 volume) (realHilbertTransformL2 (g.toLp 2)) =
      hilbertTransform ((Complex.ofRealCLM.compLpL 2 volume) (g.toLp 2)) := by
  have hp := schwartz_pair g
  generalize g.toLp 2 = F at hp ⊢
  exact spectral_real_of_pair F (hilbertPV g) hp

/-- The concrete real operator satisfies the spectral Biot–Savart relation
for every real L² input. Realness follows from the principal-value identification
for Schwartz functions and density. -/
theorem isHilbertPair_realHilbertTransformL2 (f : Lp ℝ 2 (volume : Measure ℝ)) :
    IsHilbertPair f (realHilbertTransformL2 f) := by
  let embed := Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)
  have hreal : embed (realHilbertTransformL2 f) = hilbertTransform (embed f) := by
    have hdense := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℝ)
      (μ := (volume : Measure ℝ)) (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    refine hdense.induction_on f ?_ ?_
    · exact isClosed_eq (embed.continuous.comp realHilbertTransformL2.continuous)
        (hilbertTransform.continuous.comp embed.continuous)
    · intro g
      simp only [SchwartzMap.toLpCLM_apply, embed]
      exact spectral_real_schwartz g
  refine ⟨embed f, (Complex.ofRealCLM.coeFn_compLpL f).symm, ?_⟩
  have hout := Complex.ofRealCLM.coeFn_compLpL (realHilbertTransformL2 f)
  change embed (realHilbertTransformL2 f) =ᵐ[volume]
    (fun x ↦ (realHilbertTransformL2 f x : ℂ)) at hout
  rw [hreal] at hout
  exact hout.symm

/-- The concrete real transform preserves the L² norm. -/
@[simp] theorem norm_realHilbertTransformL2 (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖realHilbertTransformL2 f‖ = ‖f‖ := by
  simp only [Lp.norm_def, (isHilbertPair_realHilbertTransformL2 f).eLpNorm_eq]

end PDE.Analysis
