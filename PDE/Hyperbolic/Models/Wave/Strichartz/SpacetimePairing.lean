/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.InnerProduct
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyKernel
public import PDE.Hyperbolic.Models.Wave.Strichartz.LpOperator

/-!
# The spacetime Gram pairing

Absolute kernel integrability justifies the four-variable interchange in the
Newton spacetime pairing. The Fourier energy integrals have precisely this
pairing, with coefficient (4*pi)^(-1). Explicit almost-everywhere transport
connects the mixed quotient pairing to arbitrary measurable representatives.
-/

@[expose] public section

open MeasureTheory
open FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- Absolute four-variable kernel integrability justifies the time-space interchange
in the spacetime pairing. -/
theorem integral_mul_spacetimeNewtonIntegral_eq
    {F G : ℝ × ℝ^3 → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume)
    (hGfin : MemLp (fun t ↦ eLpNorm (fun x ↦ G (t, x)) (12 / 11) volume) (4 / 3) volume) :
    (∫ t, ∫ x, G (t, x) * spacetimeNewtonIntegral F t x) = ∫ t, ∫ s, ∫ x, G (t, x) * ∫ y,
      exteriorNewtonKernel |t - s| (x - y) * F (s, y) := by
  have hfull := integrable_spacetime_exteriorNewtonKernel_mul hF hG hFfin hGfin
  apply integral_congr_ae
  filter_upwards [hfull.prod_right_ae] with t ht
  have hprod : Integrable (fun z : (ℝ × ℝ^3) × ℝ^3 ↦
      exteriorNewtonKernel |t - z.1.1| (z.1.2 - z.2) * F (z.1.1, z.2) * G (t, z.1.2))
      ((volume.prod volume).prod volume) :=
    (measurePreserving_prodAssoc volume volume volume).integrable_comp_of_integrable ht
  have hi : Integrable (fun z : ℝ × ℝ^3 ↦ G (t, z.2) *
      ∫ y, exteriorNewtonKernel |t - z.1| (z.2 - y) * F (z.1, y))
      (volume.prod volume) := by
    have he (z : ℝ × ℝ^3) :
        (∫ y, exteriorNewtonKernel |t - z.1| (z.2 - y) * F (z.1, y) * G (t, z.2)) =
          G (t, z.2) * ∫ y, exteriorNewtonKernel |t - z.1| (z.2 - y) * F (z.1, y) := by
      rw [integral_mul_const, mul_comm]
    simpa only [he] using hprod.integral_prod_left
  calc
    _ = ∫ x, ∫ s, G (t, x) *
        ∫ y, exteriorNewtonKernel |t - s| (x - y) * F (s, y) := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_const_mul (G (t, x)) _).symm
    _ = _ := (integral_integral_swap hi).symm

/-- The Fourier adjoint integrals pair through the exterior Newton
spacetime operator, with the exact Fourier normalization coefficient. -/
theorem re_inner_integral_frequencyEnergyDatum_eq (F G : ℝ → 𝓢(ℝ^3, ℝ))
    (hF : Measurable (fun z : ℝ × ℝ^3 ↦ F z.1 z.2)) (hG : Measurable (fun z : ℝ × ℝ^3 ↦ G z.1 z.2))
    (hFc : ∀ t, HasCompactSupport (F t : ℝ^3 → ℝ)) (hGc : ∀ t, HasCompactSupport (G t : ℝ^3 → ℝ))
    (hFfin : MemLp (fun t ↦ eLpNorm (F t) (12 / 11) volume) (4 / 3) volume)
    (hGfin : MemLp (fun t ↦ eLpNorm (G t) (12 / 11) volume) (4 / 3) volume)
    (hAF : Integrable (fun t ↦ frequencyEnergyDatum (𝓕 ((F t).postcompCLM Complex.ofRealCLM)) t))
    (hAG : Integrable (fun t ↦ frequencyEnergyDatum (𝓕 ((G t).postcompCLM Complex.ofRealCLM)) t)) :
    (inner ℂ (∫ t, frequencyEnergyDatum (𝓕 ((G t).postcompCLM Complex.ofRealCLM)) t)
      (∫ s, frequencyEnergyDatum (𝓕 ((F s).postcompCLM Complex.ofRealCLM)) s)).re =
      (4 * Real.pi)⁻¹ * ∫ t, ∫ x, G t x *
        spacetimeNewtonIntegral (fun z ↦ F z.1 z.2) t x := by
  have hgram : (inner ℂ (∫ t, frequencyEnergyDatum (𝓕 ((G t).postcompCLM Complex.ofRealCLM)) t)
        (∫ s, frequencyEnergyDatum (𝓕 ((F s).postcompCLM Complex.ofRealCLM)) s)).re =
      ∫ t, ∫ s, (inner ℂ (frequencyEnergyDatum (𝓕 ((G t).postcompCLM Complex.ofRealCLM)) t)
        (frequencyEnergyDatum (𝓕 ((F s).postcompCLM Complex.ofRealCLM)) s)).re := by
    let AF := fun t ↦ frequencyEnergyDatum (𝓕 ((F t).postcompCLM Complex.ofRealCLM)) t
    let AG := fun t ↦ frequencyEnergyDatum (𝓕 ((G t).postcompCLM Complex.ofRealCLM)) t
    change RCLike.re (inner ℂ (∫ t, AG t) (∫ s, AF s)) = ∫ t, ∫ s, RCLike.re (inner ℂ (AG t) (AF s))
    rw [inner_re_symm, ← integral_inner hAG, ← integral_re (hAG.const_inner _)]
    apply integral_congr_ae
    filter_upwards with t
    rw [inner_re_symm, ← integral_inner hAF, ← integral_re (hAF.const_inner _)]
  rw [hgram]
  calc
    _ = ∫ t, ∫ s, (4 * Real.pi)⁻¹ * ∫ x, G t x *
        ∫ y, exteriorNewtonKernel |t - s| (x - y) * F s y := by
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards [volume.ae_ne t] with s hs
      exact re_inner_frequencyEnergyDatum_eq_exteriorNewtonKernel
        (G t) (F s) (hGc t) (hFc s) hs.symm
    _ = (4 * Real.pi)⁻¹ * ∫ t, ∫ s, ∫ x, G t x *
        ∫ y, exteriorNewtonKernel |t - s| (x - y) * F s y := by
      simp only [integral_const_mul]
    _ = _ := by rw [← integral_mul_spacetimeNewtonIntegral_eq hF hG hFfin hGfin]

end WaveEquation.Strichartz

open MeasureTheory
open scoped ENNReal

namespace WaveEquation.Strichartz

local instance : ENNReal.HolderConjugate (12 : ℝ≥0∞) (12 / 11) := by
  rw [ENNReal.holderConjugate_iff,
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← one_div, ENNReal.div_add_div_same]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)
local instance : ENNReal.HolderConjugate (4 : ℝ≥0∞) (4 / 3) := by
  rw [ENNReal.holderConjugate_iff,
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← one_div, ENNReal.div_add_div_same]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- The continuous mixed pairing for the wave spacetime exponents. -/
noncomputable def spacetimePairing :
    Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ) →L[ℝ]
      Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume 12 (12 / 11)).lpPairing volume 4 (4 / 3)

/-- The continuous pairing is the iterated integral of representatives. -/
theorem spacetimePairing_eq_integral
    (u : Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ))
    (v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    spacetimePairing u v = ∫ t, ∫ x, u t x * v t x := by
  simp only [spacetimePairing, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The quotient Newton pairing equals integration of the kernel output
against the joint measurable input representative. -/
theorem spacetimePairing_spacetimeNewtonOperator_eq
    (u v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    spacetimePairing (spacetimeNewtonOperator u) v = ∫ t, ∫ x, Lp.jointRepresentative v (t, x) *
      spacetimeNewtonIntegral (Lp.jointRepresentative u) t x := by
  refine (spacetimePairing_eq_integral (spacetimeNewtonOperator u) v).trans ?_
  apply integral_congr_ae
  filter_upwards [spacetimeNewtonOperator_section u] with t ht
  apply integral_congr_ae
  filter_upwards [ht, Lp.jointRepresentative_section v t] with x hx hv
  exact (congrArg₂ (fun a b : ℝ ↦ a * b) hx.symm hv.symm).trans (mul_comm _ _)

/-- Any measurable spatial representatives give the same kernel pairing.
Transport is performed through both almost-everywhere quotient levels. -/
theorem spacetimePairing_spacetimeNewtonOperator_eq_of_sections
    (u v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ))
    {F G : ℝ × ℝ^3 → ℝ} (hF : Measurable F)
    (hFu : ∀ᵐ t, (fun x ↦ F (t, x)) =ᵐ[volume] (u t : ℝ^3 → ℝ))
    (hGv : ∀ᵐ t, (fun x ↦ G (t, x)) =ᵐ[volume] (v t : ℝ^3 → ℝ)) :
    spacetimePairing (spacetimeNewtonOperator u) v =
      ∫ t, ∫ x, G (t, x) * spacetimeNewtonIntegral F t x := by
  have hu : Lp.jointRepresentative u =ᵐ[volume.prod volume] F := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.measurable_jointRepresentative u) hF)).mpr
    filter_upwards [hFu] with t ht using (Lp.jointRepresentative_section u t).trans ht.symm
  rw [spacetimePairing_spacetimeNewtonOperator_eq, spacetimeNewtonIntegral_congr_ae hu]
  apply integral_congr_ae
  filter_upwards [hGv] with t ht
  apply integral_congr_ae
  filter_upwards [Lp.jointRepresentative_section v t, ht] with x hx hGx
  rw [hx, hGx]

end WaveEquation.Strichartz
