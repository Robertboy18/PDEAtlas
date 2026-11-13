/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Uniqueness from smooth tensor tests

Compact smooth tensor tests determine locally integrable vector-valued functions
on products of finite-dimensional real spaces. The integrable case applies
Mathlib's distributional uniqueness theorem separately in each variable and
then vector-measure uniqueness on measurable rectangles. Compact cutoffs reduce
the local case to the integrable one. No density of joint smooth tests is assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace MeasureTheory

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure D} {ν : Measure E} [SFinite μ] [SFinite ν]

omit [NormedSpace ℝ D] [FiniteDimensional ℝ D] [CompleteSpace F]
  [SFinite μ] [SFinite ν] in
/-- Compact continuous spatial weights preserve product integrability. -/
theorem Integrable.smul_snd_of_hasCompactSupport {f : D × E → F}
    (hf : Integrable f (μ.prod ν)) {h : E → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Integrable (fun z ↦ h z.2 • f z) (μ.prod ν) := by
  obtain ⟨C, hC⟩ := hhc.exists_bound_of_continuous hh
  exact hf.bdd_smul C (hh.comp continuous_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ hC z.2)

/-- An integrable function is determined by compact smooth tensor tests. -/
theorem Integrable.ae_eq_zero_of_integral_contDiff_tensor_smul_eq_zero
    {f : D × E → F} (hf : Integrable f (μ.prod ν))
    (htest : ∀ (g : D → ℝ) (h : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ContDiff ℝ ∞ h → HasCompactSupport h →
      ∫ t, ∫ x, (g t * h x) • f (t, x) ∂ν ∂μ = 0) : f =ᵐ[μ.prod ν] 0 := by
  have htime (h : E → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
      (fun t ↦ ∫ x, h x • f (t, x) ∂ν) =ᵐ[μ] 0 := by
    have hi := hf.smul_snd_of_hasCompactSupport hh.continuous hhc
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.integral_prod_left.locallyIntegrable
    intro g hg hgc
    simpa only [← MeasureTheory.integral_smul, smul_smul] using htest g h hg hgc hh hhc
  have hspace (A : Set D) : (fun x ↦ ∫ t in A, f (t, x) ∂μ) =ᵐ[ν] 0 := by
    have hi : Integrable f ((μ.restrict A).prod ν) :=
      hf.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.integral_prod_right.locallyIntegrable
    intro h hh hhc
    have hw := hi.smul_snd_of_hasCompactSupport hh.continuous hhc
    simp_rw [← MeasureTheory.integral_smul]
    rw [← integral_integral_swap hw]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae (htime h hh hhc))
  have hrect (A : Set D) (B : Set E) : ∫ z in A ×ˢ B, f z ∂μ.prod ν = 0 := by
    have hi : Integrable f ((μ.restrict A).prod (ν.restrict B)) :=
      hf.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
    rw [← Measure.prod_restrict, integral_prod_symm _ hi]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae (hspace A))
  have hv : (μ.prod ν).withDensityᵥ f = 0 := by
    apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
    · rw [withDensityᵥ_apply hf MeasurableSet.univ]
      simpa only [univ_prod_univ, Measure.restrict_univ, zero_apply] using
        hrect univ univ
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [withDensityᵥ_apply hf (hA.prod hB), hrect, zero_apply]
  exact hf.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
    (by simpa only [withDensityᵥ_zero] using hv)

omit [NormedSpace ℝ D] [FiniteDimensional ℝ D] [CompleteSpace F]
  [SFinite μ] [SFinite ν] in
/-- A compact continuous tensor weight turns local integrability into integrability. -/
theorem LocallyIntegrable.integrable_continuous_tensor_smul
    {f : D × E → F} (hf : LocallyIntegrable f (μ.prod ν))
    {g : D → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {h : E → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable (fun z ↦ (g z.1 * h z.2) • f z) (μ.prod ν) := by
  apply hf.integrable_smul_left_of_hasCompactSupport
    ((hg.comp continuous_fst).mul (hh.comp continuous_snd))
  apply HasCompactSupport.of_support_subset_isCompact (hgc.prod hhc)
  intro z hz
  have hz' : g z.1 ≠ 0 ∧ h z.2 ≠ 0 := mul_ne_zero_iff.mp hz
  exact ⟨subset_tsupport g hz'.1, subset_tsupport h hz'.2⟩

/-- Locally integrable functions are determined by compact smooth tensor tests. -/
theorem LocallyIntegrable.ae_eq_zero_of_integral_contDiff_tensor_smul_eq_zero
    {f : D × E → F} (hf : LocallyIntegrable f (μ.prod ν))
    (htest : ∀ (g : D → ℝ) (h : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ContDiff ℝ ∞ h → HasCompactSupport h →
      ∫ t, ∫ x, (g t * h x) • f (t, x) ∂ν ∂μ = 0) : f =ᵐ[μ.prod ν] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hf
  intro K hK
  obtain ⟨ψ, _, hψ, _, _⟩ := TestFunction.exists_eq_one_on_compact_finiteDimensional
    isOpen_univ (hK.image continuous_fst) (subset_univ _)
  obtain ⟨χ, _, hχ, _, _⟩ := TestFunction.exists_eq_one_on_compact_finiteDimensional
    isOpen_univ (hK.image continuous_snd) (subset_univ _)
  let w : D × E → ℝ := fun z ↦ ψ.toFun z.1 * χ.toFun z.2
  have hw := hf.integrable_continuous_tensor_smul
    ψ.contDiff.continuous ψ.hasCompactSupport χ.contDiff.continuous χ.hasCompactSupport
  have hzero : (fun z ↦ w z • f z) =ᵐ[μ.prod ν] 0 := by
    apply hw.ae_eq_zero_of_integral_contDiff_tensor_smul_eq_zero
    intro g h hg hgc hh hhc
    have ht := htest (g * ψ.toFun) (h * χ.toFun)
      (hg.mul ψ.contDiff) hgc.mul_right (hh.mul χ.contDiff) hhc.mul_right
    simpa only [w, smul_smul, Pi.mul_apply, mul_mul_mul_comm, TestFunction.toFun_eq_coe] using ht
  calc
    ∫ z in K, f z ∂μ.prod ν = ∫ z in K, w z • f z ∂μ.prod ν := by
      apply setIntegral_congr_fun hK.measurableSet
      intro z hz
      simp only [w, hψ z.1 (mem_image_of_mem Prod.fst hz),
        hχ z.2 (mem_image_of_mem Prod.snd hz), one_mul, one_smul]
    _ = 0 := integral_eq_zero_of_ae (ae_restrict_of_ae hzero)

/-- Equal compact smooth tensor pairings identify locally integrable functions. -/
theorem LocallyIntegrable.ae_eq_of_integral_contDiff_tensor_smul_eq
    {f f' : D × E → F} (hf : LocallyIntegrable f (μ.prod ν))
    (hf' : LocallyIntegrable f' (μ.prod ν))
    (htest : ∀ (g : D → ℝ) (h : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ContDiff ℝ ∞ h → HasCompactSupport h →
      ∫ t, ∫ x, (g t * h x) • f (t, x) ∂ν ∂μ =
        ∫ t, ∫ x, (g t * h x) • f' (t, x) ∂ν ∂μ) : f =ᵐ[μ.prod ν] f' := by
  have hzero : (f - f') =ᵐ[μ.prod ν] 0 := by
    apply (hf.sub hf').ae_eq_zero_of_integral_contDiff_tensor_smul_eq_zero
    intro g h hg hgc hh hhc
    have hi := hf.integrable_continuous_tensor_smul hg.continuous hgc hh.continuous hhc
    have hi' := hf'.integrable_continuous_tensor_smul hg.continuous hgc hh.continuous hhc
    have hisub := (hf.sub hf').integrable_continuous_tensor_smul
      hg.continuous hgc hh.continuous hhc
    rw [← integral_prod _ hisub]
    simp only [Pi.sub_apply, smul_sub]
    rw [MeasureTheory.integral_sub hi hi', integral_prod _ hi, integral_prod _ hi',
      htest g h hg hgc hh hhc, sub_self]
  filter_upwards [hzero] with z hz
  exact sub_eq_zero.mp hz

end MeasureTheory
