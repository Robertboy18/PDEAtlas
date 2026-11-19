/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Laplace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Vertical-line Laplace inversion

Fourier inversion reconstructs positive-time data when both the damped causal
extension and its vertical Laplace trace are integrable. Smooth compactly supported
causal data satisfy these hypotheses on every vertical line, by Mathlib's Schwartz-space
results. The inversion step is Mathlib's `MeasureTheory.Integrable.fourierInv_fourier_eq`,
applied to the damped causal extension.

## Main results

* `inversion`: `f t = exp (a t) • ∫ exp (2πiξt) • L[f](a + 2πiξ) dξ` at a point `t > 0` of
  continuity, when the damped extension and the vertical trace are integrable.
* `integrable_transform_vertical`: smooth compactly supported causal data have an integrable
  trace on every vertical line.
* `inversion_of_contDiff_hasCompactSupport`: the inversion formula for such data at every
  `t > 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped FourierTransform Topology ContDiff

namespace PDE.Analysis.Laplace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Laplace inversion with explicit absolute convergence on the chosen vertical line. -/
theorem inversion {f : ℝ → E} {a t : ℝ} (ht : 0 < t)
    (hf : ContinuousAt f t) (hd : Integrable (dampedExtension f a))
    (hL : Integrable (fun ξ : ℝ ↦ transform f ((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I))) :
    f t = exp ((a : ℂ) * t) •
      ∫ ξ : ℝ, exp ((2 * Real.pi * ξ * t : ℝ) * I) •
        transform f ((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) := by
  have heq : dampedExtension f a =ᶠ[𝓝 t]
      fun y : ℝ ↦ exp (-(a : ℂ) * y) • f y := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
    exact indicator_of_mem hy _
  have hc : ContinuousAt (dampedExtension f a) t := by
    apply ContinuousAt.congr_of_eventuallyEq _ heq
    exact (by fun_prop : ContinuousAt (fun y : ℝ ↦ exp (-(a : ℂ) * y)) t).smul hf
  simp_rw [transform_vertical_eq_fourier] at hL ⊢
  have hi := hd.fourierInv_fourier_eq hL hc
  rw [Real.fourierInv_eq'] at hi
  simp only [RCLike.inner_apply, conj_trivial, mul_comm t, ← mul_assoc] at hi
  rw [hi]
  simp only [dampedExtension, indicator, mem_Ioi, ht, ↓reduceIte, smul_smul, ← exp_add]
  simp

omit [CompleteSpace E] in
/-- Smooth compactly supported causal data have an integrable vertical Laplace trace. -/
theorem integrable_transform_vertical {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hzero : ∀ t ≤ 0, f t = 0) (a : ℝ) :
    Integrable (fun ξ : ℝ ↦ transform f ((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I)) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ ↦ exp (-(a : ℂ) * t) • f t) := by
    exact ((contDiff_const.mul ofRealCLM.contDiff).cexp :
      ContDiff ℝ ∞ (fun t : ℝ ↦ exp (-(a : ℂ) * t))).smul hf
  let g := hc.smul_left.toSchwartzMap hs
  simpa only [transform_vertical_eq_fourier, dampedExtension_eq hzero,
    SchwartzMap.fourier_coe] using (𝓕 g).integrable

/-- Absolutely convergent vertical inversion for a smooth compactly supported causal pulse. -/
theorem inversion_of_contDiff_hasCompactSupport {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hzero : ∀ t ≤ 0, f t = 0) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    f t = exp ((a : ℂ) * t) •
      ∫ ξ : ℝ, exp ((2 * Real.pi * ξ * t : ℝ) * I) •
        transform f ((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) := by
  refine inversion ht hf.continuous.continuousAt ?_
    (integrable_transform_vertical hf hc hzero a)
  rw [dampedExtension_eq hzero]
  exact ((by fun_prop : Continuous (fun t : ℝ ↦ exp (-(a : ℂ) * t))).smul
    hf.continuous).integrable_of_hasCompactSupport hc.smul_left

end PDE.Analysis.Laplace
