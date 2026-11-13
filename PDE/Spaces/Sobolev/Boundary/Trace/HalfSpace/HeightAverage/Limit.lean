/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.HeightAverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Convergence of height averages

Uniform control of the finite-p slice error controls the error of the height
average with constant one for functions with values in a real Banach space.
Consequently, convergence of positive-height slices implies convergence of the
Lp height averages to the same boundary datum.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem eLpNorm_integral_probability_le_of_slice_bound
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (μ : Measure X) (ν : Measure T) [SFinite μ] [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : X × T → F} (hf : AEStronglyMeasurable f (μ.prod ν))
    {C : ℝ≥0∞} (hC : ∀ᵐ t ∂ν, eLpNorm (fun x ↦ f (x, t)) p μ ≤ C) :
    eLpNorm (fun x ↦ ∫ t, f (x, t) ∂ν) p μ ≤ C := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  apply (eLpNorm_integral_probability_le μ ν hp hpt hf).trans
  have hpoint : ∀ᵐ t ∂ν, (∫⁻ x, ‖f (x, t)‖ₑ ^ p.toReal ∂μ) ≤ C ^ p.toReal := by
    filter_upwards [hf.prodMk_right, hC] with t ht hCt
    have hpow := ENNReal.rpow_le_rpow hCt hpr.le
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt ht,
      ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one] at hpow
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf,
    lintegral_prod_symm _ (hf.enorm.pow_const _)]
  calc
    _ ≤ (∫⁻ _t, C ^ p.toReal ∂ν) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpoint) (by positivity)
    _ = C := by simp [← ENNReal.rpow_mul, hpr.ne']

variable [CompleteSpace F]

/-- A bound for all slice errors on `(0, ε]` bounds the height-average error
with the same constant. -/
theorem eLpNorm_heightAverage_sub_le_of_bound
    (p : ℝ) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    {f : ℝ^(n + 1) → F} {g : ℝ^n → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊))
    (hg : MemLp g (ENNReal.ofReal p) volume) {C : ℝ≥0∞}
    (hC : ∀ t ∈ Ioc 0 ε,
      eLpNorm (fun x ↦ f (joinTangentialNormal (x, t)) - g x)
        (ENNReal.ofReal p) volume ≤ C) :
    eLpNorm (fun x ↦ heightAverage ε f x - g x) (ENNReal.ofReal p) volume ≤ C := by
  let μ : Measure (ℝ^n) := volume
  let η : Measure ℝ := (ENNReal.ofReal ε)⁻¹ • volume.restrict (Ioc 0 ε)
  have hε0 : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have : IsProbabilityMeasure η := ⟨by
    simp [η, Measure.smul_apply, Real.volume_Ioc, ENNReal.inv_mul_cancel hε0]⟩
  have hsmall : μ.prod (volume.restrict (Ioc 0 ε)) ≤ μ.prod positiveNormalMeasure :=
    Measure.prod_mono le_rfl (Measure.restrict_mono (fun _ h ↦ h.1) le_rfl)
  have hprod := hf.comp_measurePreserving measurePreserving_joinTangentialNormal_upper
  have hscaled : MemLp (f ∘ joinTangentialNormal) (ENNReal.ofReal p) (μ.prod η) := by
    rw [show μ.prod η = (ENNReal.ofReal ε)⁻¹ •
      μ.prod (volume.restrict (Ioc 0 ε)) by exact Measure.prod_smul_right _]
    exact (hprod.mono_measure hsmall).smul_measure (ENNReal.inv_ne_top.mpr hε0)
  have hdiff : AEStronglyMeasurable
      (fun z : ℝ^n × ℝ ↦ f (joinTangentialNormal z) - g z.1) (μ.prod η) :=
    hscaled.aestronglyMeasurable.sub
      (hg.comp_measurePreserving measurePreserving_fst).aestronglyMeasurable
  have hformula : (fun x ↦ heightAverage ε f x - g x) =ᵐ[μ]
      fun x ↦ ∫ t, (f (joinTangentialNormal (x, t)) - g x) ∂η := by
    filter_upwards [ae_integrable_height p hp ε hf] with x hx
    have hxη : Integrable (fun t ↦ f (joinTangentialNormal (x, t))) η :=
      hx.smul_measure (ENNReal.inv_ne_top.mpr hε0)
    rw [integral_sub hxη (integrable_const _)]
    simp [heightAverage, η, integral_smul_measure, ENNReal.toReal_ofReal hε.le]
  rw [eLpNorm_congr_ae hformula]
  apply eLpNorm_integral_probability_le_of_slice_bound μ η
    (by simpa using ENNReal.ofReal_le_ofReal hp) ENNReal.ofReal_ne_top hdiff
  exact Measure.ae_smul_measure ((ae_restrict_iff' measurableSet_Ioc).2
    (Eventually.of_forall hC)) _

/-- Convergence of the positive-height slices in finite Lp implies convergence
of their height averages to the same datum. -/
theorem tendsto_eLpNorm_heightAverage_sub
    (p : ℝ) (hp : 1 ≤ p) {f : ℝ^(n + 1) → F} {g : ℝ^n → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊))
    (hg : MemLp g (ENNReal.ofReal p) volume)
    (hlim : Tendsto (fun t : ℝ ↦ eLpNorm
      (fun x ↦ f (joinTangentialNormal (x, t)) - g x) (ENNReal.ofReal p) volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ ↦ eLpNorm (fun x ↦ heightAverage ε f x - g x)
      (ENNReal.ofReal p) volume) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hlim ⊢
  intro C hC
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hlim C hC)
  apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
  refine ⟨δ, hδ, fun ε hε ↦ eLpNorm_heightAverage_sub_le_of_bound p hp ε hε.1 hf hg ?_⟩
  intro t ht
  exact hbound ⟨ht.1, ht.2.trans hε.2⟩

/-- The bounded height-average operator converges on Lp classes whenever the
positive-height slices converge to the boundary datum in Lp. -/
theorem tendsto_heightAverageLp_of_slice_tendsto
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    {f : ℝ^(n + 1) → F} {g : ℝ^n → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊))
    (hg : MemLp g (ENNReal.ofReal p) volume)
    (hlim : Tendsto (fun t : ℝ ↦ eLpNorm
      (fun x ↦ f (joinTangentialNormal (x, t)) - g x) (ENNReal.ofReal p) volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hεlim : Tendsto ε l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun i ↦ heightAverageLp n p hp (ε i) (hε i) (hf.toLp f))
      l (𝓝 (hg.toLp g)) := by
  have havg := (tendsto_eLpNorm_heightAverage_sub p hp hf hg hlim).comp hεlim
  have hnorm : ∀ i, ‖heightAverageLp n p hp (ε i) (hε i) (hf.toLp f) - hg.toLp g‖ =
      (eLpNorm (fun x ↦ heightAverage (ε i) f x - g x) (ENNReal.ofReal p) volume).toReal := by
    intro i
    rw [Lp.norm_def]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans
      ((heightAverageLp_eq_integral_of_ae_eq n p hp (ε i) (hε i)
        (hf.toLp f) hf.coeFn_toLp).sub hg.coeFn_toLp)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm, hnorm, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp havg

end SobolevSpace.Trace.HalfSpace
