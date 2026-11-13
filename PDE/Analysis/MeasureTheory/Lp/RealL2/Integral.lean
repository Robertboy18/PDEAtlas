/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.MeasureTheory.Lp.RealL2.Testing
import PDE.Analysis.MeasureTheory.Integral.Minkowski
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Representatives of Bochner L2 integrals

A jointly strongly measurable representative commutes with the Bochner
integral of an integrable real L2 curve. Cauchy--Schwarz derives the product
integrability needed for Fubini, and L2 tests identify the resulting class.
Integral Minkowski consequently bounds this actual integral in every finite
Lq norm, with no additional spatial integrability premise.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SigmaFinite ν]

/-- A joint representative commutes with the integral of a real L2 curve.
Fubini integrability is derived from the Bochner L1 norm and Cauchy--Schwarz. -/
theorem integral_jointRepresentative_ae_eq
    {u : α → Lp ℝ 2 ν} (hu : Integrable u μ) {U : α × β → ℝ}
    (hU : StronglyMeasurable U)
    (hsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → ℝ)) :
    (fun x ↦ ∫ t, U (t, x) ∂μ) =ᵐ[ν] (∫ t, u t ∂μ : Lp ℝ 2 ν) := by
  let K : β → ℝ := fun x ↦ ∫ t, U (t, x) ∂μ
  have hswap : StronglyMeasurable (fun z : β × α ↦ U (z.2, z.1)) :=
    hU.comp_measurable measurable_swap
  have hnorm : (fun t ↦ eLpNorm (fun x ↦ U (t, x)) 2 ν) =ᵐ[μ] fun t ↦ ‖u t‖ₑ := by
    filter_upwards [hsec] with t ht
    rw [eLpNorm_congr_ae ht, ← Lp.enorm_def]
  have hfin : (∫⁻ t, eLpNorm (fun x ↦ U (t, x)) 2 ν ∂μ) < ∞ := by
    rw [lintegral_congr_ae hnorm]
    exact hasFiniteIntegral_iff_enorm.mp hu.hasFiniteIntegral
  have hK : MemLp K 2 ν := by
    have hM := eLpNorm_integral_le_lintegral_eLpNorm (μ := ν) (ν := μ) (p := 2) (by norm_num)
      hswap.aestronglyMeasurable
    exact lt_of_le_of_lt (by simpa only [ENNReal.ofReal_ofNat] using hM) hfin
  have heq : hK.toLp K = ∫ t, u t ∂μ := by
    apply ext_inner_right ℝ
    intro φ
    have htest : StronglyMeasurable (fun z : α × β ↦ U z * φ z.2) :=
      hU.mul ((Lp.stronglyMeasurable φ).comp_measurable measurable_snd)
    have hprod : Integrable (fun z : α × β ↦ U z * φ z.2) (μ.prod ν) := by
      apply (integrable_prod_iff htest.aestronglyMeasurable).mpr
      refine ⟨?_, ?_⟩
      · filter_upwards [hsec] with t ht
        exact ((memLp_congr_ae ht).mpr (Lp.memLp (u t))).integrable_mul (Lp.memLp φ)
      · apply (hu.norm.mul_const ‖φ‖).mono'
          htest.norm.integral_prod_right'.aestronglyMeasurable
        filter_upwards [hsec] with t ht
        have htLp : MemLp (fun x ↦ U (t, x)) 2 ν := (memLp_congr_ae ht).mpr (Lp.memLp (u t))
        have hb := abs_integral_mul_le_lpNorm_two_mul_lpNorm_two htLp.norm (Lp.memLp φ).norm
        have hnormU : lpNorm (fun x ↦ U (t, x)) 2 ν = ‖u t‖ := by
          rw [← toReal_eLpNorm, eLpNorm_congr_ae ht, ← Lp.norm_def]
        have hnormφ : lpNorm (fun x ↦ φ x) 2 ν = ‖φ‖ := by
          rw [← toReal_eLpNorm, ← Lp.norm_def]
        rw [lpNorm_norm htLp.aestronglyMeasurable,
          lpNorm_norm (Lp.aestronglyMeasurable φ), hnormU, hnormφ] at hb
        simpa only [norm_mul, ← Real.norm_eq_abs] using hb
    have hpair : (∫ x, (hK.toLp K) x * φ x ∂ν) =
        ∫ x, (∫ t, u t ∂μ : Lp ℝ 2 ν) x * φ x ∂ν := by
      calc
        _ = ∫ x, K x * φ x ∂ν := by
          apply integral_congr_ae
          filter_upwards [hK.coeFn_toLp] with x hx
          rw [hx]
        _ = ∫ x, ∫ t, U (t, x) * φ x ∂μ ∂ν := by
          congr 1
          funext x
          exact (integral_mul_const _ _).symm
        _ = ∫ t, ∫ x, U (t, x) * φ x ∂ν ∂μ := integral_integral_swap hprod.swap
        _ = ∫ t, ∫ x, (u t) x * φ x ∂ν ∂μ := by
          apply integral_congr_ae
          filter_upwards [hsec] with t ht
          exact integral_congr_ae (ht.mul (Filter.EventuallyEq.rfl))
        _ = _ := (Lp.integral_mul_integral hu (Lp.memLp φ)).symm
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using hpair
  exact hK.coeFn_toLp.symm.trans (heq ▸ Filter.EventuallyEq.rfl)

/-- Integral Minkowski also bounds the actual representative of a Bochner L2
integral in any finite Lq norm, with no additional Lq integrability premise. -/
theorem eLpNorm_integral_le_lintegral_sections
    {u : α → Lp ℝ 2 ν} (hu : Integrable u μ) {U : α × β → ℝ}
    (hU : StronglyMeasurable U)
    (hsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → ℝ))
    {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (∫ t, u t ∂μ : Lp ℝ 2 ν) (ENNReal.ofReal q) ν ≤
      ∫⁻ t, eLpNorm (fun x ↦ U (t, x)) (ENNReal.ofReal q) ν ∂μ := by
  rw [← eLpNorm_congr_ae (integral_jointRepresentative_ae_eq hu hU hsec)]
  exact eLpNorm_integral_le_lintegral_eLpNorm hq
    (hU.comp_measurable measurable_swap).aestronglyMeasurable

end MeasureTheory.Lp
