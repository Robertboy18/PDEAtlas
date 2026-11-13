/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Convolution.FractionalEnergy.Dilation
public import PDE.Analysis.Convolution.FractionalEnergy.KernelBound

/-!
# Fractional energy of signed compact kernels

A zero-mean real compact kernel turns its Banach-valued convolution into an average
of increments.
Hölder, translation, dilation, and integration over positive heights bound its
power energy by the fractional displacement energy with exponent `dim E + p - 1`.
-/

@[expose] public section

open MeasureTheory Set Module
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem integral_smul_comp_sub_smul_congr_ae
    (μ : Measure E) [μ.IsAddHaarMeasure] (ψ : E → ℝ)
    {g gm : E → F} (hge : g =ᵐ[μ] gm) (x : E) {t : ℝ} (ht : t ≠ 0) :
    (∫ z, ψ z • g (x - t • z) ∂μ) = ∫ z, ψ z • gm (x - t • z) ∂μ := by
  have hq : QuasiMeasurePreserving (fun z : E ↦ x - t • z) μ μ := by
    simpa only [Function.comp_def, neg_smul, ← sub_eq_add_neg] using
      (measurePreserving_add_left μ x).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul μ (neg_ne_zero.mpr ht))
  apply integral_congr_ae
  filter_upwards [hq.ae hge] with z hz
  rw [hz]

private theorem stronglyMeasurable_signedKernel
    (μ : Measure E) [μ.IsAddHaarMeasure] [SFinite μ]
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ) (hg : AEStronglyMeasurable g μ) :
    StronglyMeasurable fun tx : ℝ × E ↦
      tx.1⁻¹ • ∫ z, ψ z • g (tx.2 - tx.1 • z) ∂μ := by
  let gm := hg.mk g
  have hgm : StronglyMeasurable gm := hg.stronglyMeasurable_mk
  have hm : StronglyMeasurable fun v : (ℝ × E) × E ↦
      ψ v.2 • gm (v.1.2 - v.1.1 • v.2) :=
    (hψ.measurable.comp measurable_snd).stronglyMeasurable.smul
      (hgm.comp_measurable (by fun_prop))
  have hj : StronglyMeasurable fun tx : ℝ × E ↦
      tx.1⁻¹ • ∫ z, ψ z • gm (tx.2 - tx.1 • z) ∂μ :=
    measurable_fst.inv.stronglyMeasurable.smul hm.integral_prod_right'
  convert hj using 1
  funext tx
  by_cases ht : tx.1 = 0
  · simp [ht]
  rw [integral_smul_comp_sub_smul_congr_ae μ ψ hg.ae_eq_mk tx.2 ht]

variable [CompleteSpace F]

private theorem lintegral_signedKernel_rpow_le_of_stronglyMeasurable
    (μ : Measure E) [μ.IsAddHaarMeasure] [SFinite μ]
    {p R M : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ z, |ψ z| ≤ M) (hψzero : ∫ z, ψ z ∂μ = 0)
    (hg : LocallyIntegrable g μ) (hgm : StronglyMeasurable g) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
      ENNReal.ofReal (‖t⁻¹ • ∫ z, ψ z • g (x - t • z) ∂μ‖ ^ p) ∂μ) ≤
      ((μ (Metric.ball (0 : E) R)) ^ (p - 1) * ENNReal.ofReal (M ^ p)) *
        ENNReal.ofReal (R ^ ((finrank ℝ E : ℝ) + p - 1) /
          ((finrank ℝ E : ℝ) + p - 1)) *
        ∫⁻ h, ∫⁻ x, ENNReal.ofReal (‖h‖ ^ (-((finrank ℝ E : ℝ) + p - 1))) *
          ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ ∂μ := by
  let C := (μ (Metric.ball (0 : E) R)) ^ (p - 1) * ENNReal.ofReal (M ^ p)
  let f : E → ℝ≥0∞ := fun h ↦ ∫⁻ x, ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ
  have hm : Measurable fun z : E × E ↦
      ENNReal.ofReal (‖g (z.2 - z.1) - g z.2‖ ^ p) :=
    (((hgm.comp_measurable (measurable_snd.sub measurable_fst)).sub
      (hgm.comp_measurable measurable_snd)).norm.measurable.pow_const p).ennreal_ofReal
  have hf : Measurable f := hm.lintegral_prod_right'
  have hf0 : f 0 = 0 := by simp [f, (zero_lt_one.trans hp).ne']
  have hball : μ (Metric.ball (0 : E) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E) R).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  have hC : C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hp.le) hball)
      ENNReal.ofReal_ne_top
  have hswap (t : ℝ) :
      (∫⁻ x, ∫⁻ z in Metric.ball (0 : E) R,
        ENNReal.ofReal (‖g (x - t • z) - g x‖ ^ p) ∂μ ∂μ) =
        ∫⁻ z in Metric.ball (0 : E) R, f (t • z) ∂μ := by
    apply lintegral_lintegral_swap
    exact (hm.comp ((measurable_snd.const_smul t).prodMk measurable_fst)).aemeasurable
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, C *
        (ENNReal.ofReal (t ^ (-p)) * ∫⁻ z in Metric.ball (0 : E) R,
          ENNReal.ofReal (‖g (x - t • z) - g x‖ ^ p) ∂μ) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply lintegral_mono
      intro x
      exact ofReal_norm_signedKernel_rpow_le μ hp hψ hψc hψsupport hψbound hψzero hg x ht
    _ = C * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p)) *
        ∫⁻ z in Metric.ball (0 : E) R, f (t • z) ∂μ := by
      simp_rw [lintegral_const_mul' _ _ hC,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hswap]
    _ = _ := by
      rw [lintegral_dilation_ball_rpow_eq μ hp hR hf hf0]
      simp_rw [f, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact (mul_assoc _ _ _).symm

/-- A bounded continuous zero-mean kernel controls its full positive-height power energy by
the fractional displacement energy. No finiteness of the latter is assumed. -/
theorem lintegral_signedKernel_rpow_le
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {p R M : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ z, |ψ z| ≤ M) (hψzero : ∫ z, ψ z ∂μ = 0)
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
      ENNReal.ofReal (‖t⁻¹ • ∫ z, ψ z • g (x - t • z) ∂μ‖ ^ p) ∂μ) ≤
      ENNReal.ofReal ((μ.real (Metric.ball (0 : E) R)) ^ (p - 1) * M ^ p *
        (R ^ ((finrank ℝ E : ℝ) + p - 1) / ((finrank ℝ E : ℝ) + p - 1))) *
        ∫⁻ h, ∫⁻ x, ENNReal.ofReal (‖h‖ ^ (-((finrank ℝ E : ℝ) + p - 1))) *
          ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ ∂μ := by
  have hM : 0 ≤ M := (abs_nonneg (ψ 0)).trans (hψbound 0)
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R)
      (hψsupport.trans Metric.ball_subset_closedBall)
  have hg1 : LocallyIntegrable g μ := hg.locallyIntegrable (by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le)
  let gm := hg.aestronglyMeasurable.mk g
  have hgm : StronglyMeasurable gm := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hge : g =ᵐ[μ] gm := hg.aestronglyMeasurable.ae_eq_mk
  have key := lintegral_signedKernel_rpow_le_of_stronglyMeasurable μ hp hR hψ hψc hψsupport
    hψbound hψzero (hg1.congr hge) hgm
  have he (h : E) :
      (∫⁻ x, ENNReal.ofReal (‖gm (x - h) - gm x‖ ^ p) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [(measurePreserving_sub_right μ h).quasiMeasurePreserving.ae hge,
      hge] with x hx hx0
    rw [hx, hx0]
  have hball : μ (Metric.ball (0 : E) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E) R).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  have hv : (μ (Metric.ball (0 : E) R)) ^ (p - 1) =
      ENNReal.ofReal ((μ.real (Metric.ball (0 : E) R)) ^ (p - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg
      (measureReal_nonneg : 0 ≤ μ.real (Metric.ball (0 : E) R)) (sub_nonneg.mpr hp.le),
      ofReal_measureReal hball]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
        ENNReal.ofReal (‖t⁻¹ • ∫ z, ψ z • gm (x - t • z) ∂μ‖ ^ p) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply lintegral_congr
      intro x
      rw [integral_smul_comp_sub_smul_congr_ae μ ψ hge x (ne_of_gt ht)]
    _ ≤ _ := by
      convert key using 1
      rw [hv, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, he]

/-- Finite displacement energy gives integrability of the kernel's power over heights
and base points. -/
theorem integrable_norm_signedKernel_rpow
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {p R M : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ z, |ψ z| ≤ M) (hψzero : ∫ z, ψ z ∂μ = 0)
    (hg : MemLp g (ENNReal.ofReal p) μ)
    (henergy : (∫⁻ h, ∫⁻ x,
      ENNReal.ofReal (‖h‖ ^ (-((finrank ℝ E : ℝ) + p - 1))) *
        ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ ∂μ) < ⊤) :
    Integrable (fun tx : ℝ × E ↦
      ‖tx.1⁻¹ • ∫ z, ψ z • g (tx.2 - tx.1 • z) ∂μ‖ ^ p)
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
  have hm := stronglyMeasurable_signedKernel μ hψ hg.aestronglyMeasurable
  have hmp : Measurable fun tx : ℝ × E ↦
      ‖tx.1⁻¹ • ∫ z, ψ z • g (tx.2 - tx.1 • z) ∂μ‖ ^ p := hm.norm.measurable.pow_const p
  have hn : ∀ tx : ℝ × E,
      0 ≤ ‖tx.1⁻¹ • ∫ z, ψ z • g (tx.2 - tx.1 • z) ∂μ‖ ^ p := fun _ ↦
    Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨hmp.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hn)).mpr ?_⟩
  rw [lintegral_prod _ hmp.ennreal_ofReal.aemeasurable]
  exact (lintegral_signedKernel_rpow_le μ hp hR hψ hψsupport hψbound hψzero hg).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top henergy)

/-- The real power-energy bound, with finiteness supplied by the displacement integral. -/
theorem integral_norm_signedKernel_rpow_le
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {p R M : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ z, |ψ z| ≤ M) (hψzero : ∫ z, ψ z ∂μ = 0)
    (hg : MemLp g (ENNReal.ofReal p) μ)
    (henergy : (∫⁻ h, ∫⁻ x,
      ENNReal.ofReal (‖h‖ ^ (-((finrank ℝ E : ℝ) + p - 1))) *
        ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ ∂μ) < ⊤) :
    (∫ tx : ℝ × E, ‖tx.1⁻¹ • ∫ z, ψ z • g (tx.2 - tx.1 • z) ∂μ‖ ^ p
      ∂((volume.restrict (Ioi (0 : ℝ))).prod μ)) ≤
      (μ.real (Metric.ball (0 : E) R)) ^ (p - 1) * M ^ p *
        (R ^ ((finrank ℝ E : ℝ) + p - 1) / ((finrank ℝ E : ℝ) + p - 1)) *
        (∫⁻ h, ∫⁻ x, ENNReal.ofReal (‖h‖ ^ (-((finrank ℝ E : ℝ) + p - 1))) *
          ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) ∂μ ∂μ).toReal := by
  have hi := integrable_norm_signedKernel_rpow μ hp hR hψ hψsupport hψbound hψzero hg
    henergy
  have hn : ∀ tx : ℝ × E,
      0 ≤ ‖tx.1⁻¹ • ∫ z, ψ z • g (tx.2 - tx.1 • z) ∂μ‖ ^ p := fun _ ↦
    Real.rpow_nonneg (norm_nonneg _) _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn)
    hi.aestronglyMeasurable,
    lintegral_prod _ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top henergy.ne)
    (lintegral_signedKernel_rpow_le μ hp hR hψ hψsupport hψbound hψzero hg)
  have hM : 0 ≤ M := (abs_nonneg (ψ 0)).trans (hψbound 0)
  have hq : 0 < (finrank ℝ E : ℝ) + p - 1 := by
    have := Nat.cast_nonneg (α := ℝ) (finrank ℝ E)
    linarith
  have hC : 0 ≤ (μ.real (Metric.ball (0 : E) R)) ^ (p - 1) * M ^ p *
      (R ^ ((finrank ℝ E : ℝ) + p - 1) / ((finrank ℝ E : ℝ) + p - 1)) := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at h
  exact h

end MeasureTheory
