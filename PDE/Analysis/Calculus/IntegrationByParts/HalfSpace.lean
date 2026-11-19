/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegrationByParts.CompactSupport
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Signed derivative integrals on a product half-space

Fubini and the one-dimensional fundamental theorem give the normal boundary
term. Tangential derivatives integrate to zero. A continuous tangential weight
in the normal formula needs no derivative and need not have compact support.
-/

@[expose] public section

open MeasureTheory Measure Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

namespace PDE

/-- Normal integration over an upper half-space has the negative boundary
value, including when multiplied by a continuous tangential weight. -/
theorem integral_halfSpace_mul_fderiv_normal {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    {a : E → ℝ} (ha : Continuous a) :
    ∫ z in Set.univ ×ˢ Ioi 0, a z.1 * fderiv ℝ f z (0, 1) ∂μ.prod volume =
      -(∫ y, a y * f (y, 0) ∂μ) := by
  have hc : Continuous (fun z : E × ℝ ↦ a z.1 * fderiv ℝ f z (0, 1)) :=
    (ha.comp continuous_fst).mul
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hint : Integrable (fun z : E × ℝ ↦ a z.1 * fderiv ℝ f z (0, 1))
      (μ.prod volume) :=
    hc.integrable_of_hasCompactSupport (hcompact.fderiv_apply ℝ (0, 1)).mul_left
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hint' : Integrable (fun z : E × ℝ ↦ a z.1 * fderiv ℝ f z (0, 1))
      (μ.prod (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using
      hint.integrableOn (s := Set.univ ×ˢ Ioi 0)
  rw [integral_prod _ hint']
  have hslice (y : E) :
      ∫ t in Ioi 0, fderiv ℝ f (y, t) (0, 1) = -f (y, 0) := by
    have hsc : HasCompactSupport (fun t : ℝ ↦ f (y, t)) := by
      apply HasCompactSupport.intro (hcompact.image continuous_snd)
      intro t ht
      by_contra hne
      exact ht ⟨(y, t), subset_tsupport f hne, rfl⟩
    have hd (t : ℝ) : deriv (fun s : ℝ ↦ f (y, s)) t =
        fderiv ℝ f (y, t) (0, 1) :=
      ((hf.differentiable one_ne_zero (y, t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))).deriv
    simpa only [Function.comp_def, id_eq, hd] using HasCompactSupport.integral_Ioi_deriv_eq
      (hf.comp (contDiff_const.prodMk contDiff_id)) hsc 0
  simp_rw [integral_const_mul, hslice, mul_neg]
  exact integral_neg _

/-- A tangential directional derivative has zero integral over the upper
half-space. -/
theorem integral_halfSpace_fderiv_tangential {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) (v : E) :
    ∫ z in Set.univ ×ˢ Ioi 0, fderiv ℝ f z (v, 0) ∂μ.prod volume = 0 := by
  have hint : Integrable (fun z : E × ℝ ↦ fderiv ℝ f z (v, 0)) (μ.prod volume) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcompact.fderiv_apply ℝ (v, 0))
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hint' : Integrable (fun z : E × ℝ ↦ fderiv ℝ f z (v, 0))
      (μ.prod (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using
      hint.integrableOn (s := Set.univ ×ˢ Ioi 0)
  rw [integral_prod_symm _ hint']
  have hslice (t : ℝ) : ∫ y, fderiv ℝ f (y, t) (v, 0) ∂μ = 0 := by
    have hsc : HasCompactSupport (fun y : E ↦ f (y, t)) := by
      apply HasCompactSupport.intro (hcompact.image continuous_fst)
      intro y hy
      by_contra hne
      exact hy ⟨(y, t), subset_tsupport f hne, rfl⟩
    have hd (y : E) : fderiv ℝ (fun x : E ↦ f (x, t)) y v =
        fderiv ℝ f (y, t) (v, 0) := by
      have h := ((hf.differentiable one_ne_zero (y, t)).hasFDerivAt.comp y
        ((hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const t y))).fderiv
      exact congrArg (fun A : E →L[ℝ] ℝ ↦ A v) h
    simpa only [Function.comp_def, id_eq, hd] using integral_fderiv_eq_zero_of_hasCompactSupport
      (μ := μ) (hf.comp (contDiff_id.prodMk contDiff_const)) hsc v
  simp only [hslice, integral_zero]

end PDE
