/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegrationByParts.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Lipschitz integration by parts with an initial face

The normal derivative of a Lipschitz function has a boundary contribution on
the closed forward half-plane. Rademacher's theorem identifies the derivatives
of almost every slice with the actual Fréchet derivative. Absolute continuity
then gives the boundary term without a classical differentiability assumption.
-/

@[expose] public section

open MeasureTheory Measure Set
open scoped NNReal

namespace PDE.Analysis

/-- A bounded actual derivative becomes integrable after compact continuous testing. -/
theorem integrable_fderiv_mul_test_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ]
    {f φ : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : E) :
    Integrable (fun p ↦ fderiv ℝ f p v * φ p) μ := by
  apply (hφ.integrable_of_hasCompactSupport hc).bdd_mul
    (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
  exact ae_of_all _ fun p ↦ (fderiv ℝ f p).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

/-- Normal integration by parts for a Lipschitz potential includes its actual
initial value. The coordinates here are space first, time second. -/
theorem integral_halfSpace_fderiv_mul_normal_of_lipschitz
    {W φ : ℝ × ℝ → ℝ} {K : ℝ≥0} (hW : LipschitzWith K W)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ p in univ ×ˢ Ioi 0, fderiv ℝ W p (0, 1) * φ p) =
      -(∫ x : ℝ, W (x, 0) * φ (x, 0)) -
        ∫ p in univ ×ˢ Ioi 0, W p * fderiv ℝ φ p (0, 1) := by
  have hleft : Integrable (fun p ↦ fderiv ℝ W p (0, 1) * φ p) := by
    rw [Measure.volume_eq_prod]
    exact integrable_fderiv_mul_test_of_lipschitz hW hφ.continuous hc (0, 1)
  have hright : Integrable (fun p ↦ W p * fderiv ℝ φ p (0, 1)) := by
    apply (hW.continuous.mul
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport
    exact (hc.fderiv_apply ℝ (0, 1)).mul_left
  have hleft' : Integrable (fun p ↦ fderiv ℝ W p (0, 1) * φ p)
      (volume.prod (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ] using hleft.integrableOn (s := univ ×ˢ Ioi 0)
  have hright' : Integrable (fun p ↦ W p * fderiv ℝ φ p (0, 1))
      (volume.prod (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ] using hright.integrableOn (s := univ ×ˢ Ioi 0)
  have hdiff : ∀ᵐ x : ℝ, ∀ᵐ t : ℝ, DifferentiableAt ℝ W (x, t) :=
    ae_ae_of_ae_prod (hW.ae_differentiableAt (μ := volume.prod volume))
  have hslice : ∀ᵐ x : ℝ,
      (∫ t in Ioi 0, fderiv ℝ W (x, t) (0, 1) * φ (x, t)) =
        -W (x, 0) * φ (x, 0) -
          ∫ t in Ioi 0, W (x, t) * fderiv ℝ φ (x, t) (0, 1) := by
    filter_upwards [hdiff] with x hx
    have hWL : LipschitzWith K (fun t : ℝ ↦ W (x, t)) :=
      LipschitzWith.of_dist_le_mul fun s t ↦ by
        simpa only [dist_prod_same_left] using hW.dist_le_mul (x, s) (x, t)
    have hφC : ContDiff ℝ 1 (fun t : ℝ ↦ φ (x, t)) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    have hφK : HasCompactSupport (fun t : ℝ ↦ φ (x, t)) := by
      apply HasCompactSupport.intro (hc.image continuous_snd)
      intro t ht
      by_contra h
      exact ht ⟨(x, t), subset_tsupport φ h, rfl⟩
    have hderiv : ∀ᵐ t : ℝ,
        deriv (fun s : ℝ ↦ W (x, s)) t = fderiv ℝ W (x, t) (0, 1) := by
      filter_upwards [hx] with t ht
      exact (ht.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv
    have htest (t : ℝ) :
        deriv (fun s : ℝ ↦ φ (x, s)) t = fderiv ℝ φ (x, t) (0, 1) :=
      ((hφ.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv
    have hp := integral_Ioi_deriv_mul_eq_of_absolutelyContinuous
      (fun a b ↦ hWL.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
      hφC hφK 0
    simp_rw [htest] at hp
    rw [← hp]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hderiv] with t ht
    rw [ht]
  have hboundary : Integrable (fun x : ℝ ↦ W (x, 0) * φ (x, 0)) := by
    apply ((hW.continuous.comp (continuous_id.prodMk continuous_const)).mul
      (hφ.continuous.comp (continuous_id.prodMk continuous_const))
      ).integrable_of_hasCompactSupport
    have hφK : HasCompactSupport (fun x : ℝ ↦ φ (x, 0)) := by
      apply HasCompactSupport.intro (hc.image continuous_fst)
      intro x hx
      by_contra h
      exact hx ⟨(x, 0), subset_tsupport φ h, rfl⟩
    exact hφK.mul_left
  simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_prod _ hleft', integral_prod _ hright']
  rw [integral_congr_ae hslice]
  simp_rw [neg_mul]
  exact (integral_sub hboundary.neg hright'.integral_prod_left).trans
    (by simp only [Pi.neg_apply, integral_neg])

/-- Tangential integration by parts has no boundary contribution on the initial face. -/
theorem integral_halfSpace_fderiv_mul_tangent_of_lipschitz
    {W φ : ℝ × ℝ → ℝ} {K : ℝ≥0} (hW : LipschitzWith K W)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ p in univ ×ˢ Ioi 0, fderiv ℝ W p (1, 0) * φ p) =
      -∫ p in univ ×ˢ Ioi 0, W p * fderiv ℝ φ p (1, 0) := by
  have hleft : Integrable (fun p ↦ fderiv ℝ W p (1, 0) * φ p) := by
    rw [Measure.volume_eq_prod]
    exact integrable_fderiv_mul_test_of_lipschitz hW hφ.continuous hc (1, 0)
  have hright : Integrable (fun p ↦ W p * fderiv ℝ φ p (1, 0)) := by
    apply (hW.continuous.mul
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport
    exact (hc.fderiv_apply ℝ (1, 0)).mul_left
  have hleft' : Integrable (fun p ↦ fderiv ℝ W p (1, 0) * φ p)
      (volume.prod (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ] using hleft.integrableOn (s := univ ×ˢ Ioi 0)
  have hright' : Integrable (fun p ↦ W p * fderiv ℝ φ p (1, 0))
      (volume.prod (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ] using hright.integrableOn (s := univ ×ˢ Ioi 0)
  have hdiff : ∀ᵐ t : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ W (x, t) :=
    ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae
      (hW.ae_differentiableAt (μ := volume.prod volume)))
  have hslice : ∀ᵐ t : ℝ,
      (∫ x : ℝ, fderiv ℝ W (x, t) (1, 0) * φ (x, t)) =
        -∫ x : ℝ, W (x, t) * fderiv ℝ φ (x, t) (1, 0) := by
    filter_upwards [hdiff] with t ht
    have hWL : LipschitzWith K (fun x : ℝ ↦ W (x, t)) :=
      LipschitzWith.of_dist_le_mul fun x y ↦ by
        simpa only [dist_prod_same_right] using hW.dist_le_mul (x, t) (y, t)
    have hφC : ContDiff ℝ 1 (fun x : ℝ ↦ φ (x, t)) :=
      hφ.comp (contDiff_id.prodMk contDiff_const)
    have hφK : HasCompactSupport (fun x : ℝ ↦ φ (x, t)) := by
      apply HasCompactSupport.intro (hc.image continuous_fst)
      intro x hx
      by_contra h
      exact hx ⟨(x, t), subset_tsupport φ h, rfl⟩
    have hderiv : ∀ᵐ x : ℝ,
        deriv (fun y : ℝ ↦ W (y, t)) x = fderiv ℝ W (x, t) (1, 0) := by
      filter_upwards [ht] with x hx
      exact (hx.hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))).deriv
    have htest (x : ℝ) :
        deriv (fun y : ℝ ↦ φ (y, t)) x = fderiv ℝ φ (x, t) (1, 0) :=
      ((hφ.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))).deriv
    have hp := integral_deriv_mul_eq_neg_of_absolutelyContinuous
      (fun a b ↦ hWL.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
      hφC hφK
    simp_rw [htest] at hp
    rw [← hp]
    apply integral_congr_ae
    filter_upwards [hderiv] with x hx
    rw [hx]
  simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_prod_symm _ hleft', integral_prod_symm _ hright']
  exact (integral_congr_ae (ae_restrict_of_ae hslice)).trans (integral_neg _)

end PDE.Analysis
