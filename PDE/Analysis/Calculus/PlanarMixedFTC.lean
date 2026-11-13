/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A planar pointwise bound from the mixed derivative

For a compactly supported C² function, integrate first along a horizontal line and
then along a vertical line. The two one-dimensional fundamental theorems give a
pointwise bound by the L¹ norm of the actual mixed derivative.

This form is useful for weighted decay: apply it to a cutoff of `(1 + r² + z²) * u²`.
The mixed derivative involves `u * u_rz` and `u_r * u_z`, so Cauchy–Schwarz can use
the available weighted derivative energies without requiring the moment
`∫ (1 + r² + z²) * u²`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis

private theorem hasCompactSupport_horizontal {f : ℝ × ℝ → ℝ}
    (hf : HasCompactSupport f) (z : ℝ) :
    HasCompactSupport (fun r ↦ f (r, z)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.isCompact.image continuous_fst)
  intro r hr
  exact ⟨(r, z), subset_tsupport f hr, rfl⟩

private theorem hasCompactSupport_vertical {f : ℝ × ℝ → ℝ}
    (hf : HasCompactSupport f) (r : ℝ) :
    HasCompactSupport (fun z ↦ f (r, z)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.isCompact.image continuous_snd)
  intro z hz
  exact ⟨(r, z), subset_tsupport f hz, rfl⟩

private theorem enorm_le_lintegral_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) (x : ℝ) :
    ‖f x‖ₑ ≤ ∫⁻ y, ‖deriv f y‖ₑ :=
  (HasCompactSupport.enorm_le_lintegral_Ici_deriv hf hcompact x).trans
    (lintegral_mono' Measure.restrict_le_self le_rfl)

private theorem enorm_le_lintegral_mixed_fderiv {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f) (r z : ℝ) :
    ‖f (r, z)‖ₑ ≤
      ∫⁻ s : ℝ, ∫⁻ t : ℝ,
        ‖fderiv ℝ (fun p ↦ fderiv ℝ f p (1, 0)) (s, t) (0, 1)‖ₑ := by
  let fr : ℝ × ℝ → ℝ := fun p ↦ fderiv ℝ f p (1, 0)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfr : ContDiff ℝ 1 fr :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hfrCompact : HasCompactSupport fr := hcompact.fderiv_apply ℝ (1, 0)
  have hhorizontal (s : ℝ) : deriv (fun s ↦ f (s, z)) s = fr (s, z) := by
    exact ((hf1.differentiable_one (s, z)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))).deriv
  have hvertical (s t : ℝ) :
      deriv (fun t ↦ fr (s, t)) t = fderiv ℝ fr (s, t) (0, 1) := by
    exact ((hfr.differentiable_one (s, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))).deriv
  calc
    ‖f (r, z)‖ₑ ≤ ∫⁻ s, ‖deriv (fun s ↦ f (s, z)) s‖ₑ :=
      enorm_le_lintegral_deriv (hf1.comp (contDiff_prodMk_left z))
        (hasCompactSupport_horizontal hcompact z) r
    _ = ∫⁻ s, ‖fr (s, z)‖ₑ := by simp_rw [hhorizontal]
    _ ≤ ∫⁻ s : ℝ, ∫⁻ t : ℝ, ‖fderiv ℝ fr (s, t) (0, 1)‖ₑ := by
      apply lintegral_mono
      intro s
      have h := enorm_le_lintegral_deriv (hfr.comp (contDiff_prodMk_right s))
        (hasCompactSupport_vertical hfrCompact s) z
      simpa only [Function.comp_def, hvertical] using h

/-- Two applications of the fundamental theorem control every value of a compact C²
function by the L¹ norm of its actual mixed coordinate derivative. -/
theorem norm_le_integral_norm_mixed_fderiv {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f) (x : ℝ × ℝ) :
    ‖f x‖ ≤ ∫ p : ℝ × ℝ,
      ‖fderiv ℝ (fun q ↦ fderiv ℝ f q (1, 0)) p (0, 1)‖ := by
  let fr : ℝ × ℝ → ℝ := fun p ↦ fderiv ℝ f p (1, 0)
  let frz : ℝ × ℝ → ℝ := fun p ↦ fderiv ℝ fr p (0, 1)
  have hfr : ContDiff ℝ 1 fr :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hfrz : Continuous frz :=
    ((hfr.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hfrzCompact : HasCompactSupport frz :=
    (hcompact.fderiv_apply ℝ (1, 0)).fderiv_apply ℝ (0, 1)
  have hfrzInt : Integrable frz := hfrz.integrable_of_hasCompactSupport hfrzCompact
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ norm_nonneg _)).mp
  change ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal (∫ p, ‖frz p‖)
  rw [ofReal_integral_norm_eq_lintegral_enorm hfrzInt, ofReal_norm]
  change ‖f x‖ₑ ≤ ∫⁻ p, ‖frz p‖ₑ ∂(volume.prod volume)
  rw [lintegral_prod _ hfrz.enorm.aemeasurable]
  exact enorm_le_lintegral_mixed_fderiv hf hcompact x.1 x.2

end PDE.Analysis
