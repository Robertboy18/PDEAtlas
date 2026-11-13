/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bounded height averages on the upper half-space

Averaging a function in Lp with values in a real normed space over heights in `(0, ε]`
gives a boundary Lp function.
The bound is `ε ^ (-(1 / p))` for finite real `p ≥ 1`. The construction uses
representatives and the volume-preserving tangential-normal coordinates;
no choice of a pointwise boundary slice is required.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set Filter
open scoped ENNReal

variable {n : ℕ}

/-- Joining tangential coordinates and positive height preserves the restricted volume. -/
theorem measurePreserving_joinTangentialNormal_upper :
    MeasurePreserving (joinTangentialNormal (n := n))
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure)
      (volume.restrict ℝ^(n + 1)₊) := by
  let e := tangentialNormalMeasurableEquiv (n := n)
  let S : Set (ℝ^n × ℝ) := univ ×ˢ Ioi (0 : ℝ)
  have h := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).restrict_preimage_emb
    e.measurableEmbedding S
  have hpre : e ⁻¹' S = ℝ^(n + 1)₊ := by
    rw [show (e : ℝ^(n + 1) → ℝ^n × ℝ) = splitTangentialNormal from
      funext tangentialNormalMeasurableEquiv_apply]
    exact (upper_eq_preimage_split_snd_Ioi (n := n)).symm
  rw [hpre] at h
  have hj := h.symm e
  rw [show (e.symm : ℝ^n × ℝ → ℝ^(n + 1)) = joinTangentialNormal from
    funext tangentialNormalMeasurableEquiv_symm_apply] at hj
  simpa [Measure.volume_eq_prod, ← Measure.prod_restrict, S, positiveNormalMeasure] using hj

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrating over a probability parameter contracts the finite-p product seminorm. -/
theorem eLpNorm_integral_probability_le
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (μ : Measure X) (ν : Measure T) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : X × T → F} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    eLpNorm (fun x ↦ ∫ t, f (x, t) ∂ν) p μ ≤ eLpNorm f p (μ.prod ν) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpoint : ∀ᵐ x ∂μ, ‖∫ t, f (x, t) ∂ν‖ₑ ^ p.toReal ≤
      ∫⁻ t, ‖f (x, t)‖ₑ ^ p.toReal ∂ν := by
    filter_upwards [hf.prodMk_left] with x hx
    have hnorm : ‖∫ t, f (x, t) ∂ν‖ₑ ≤ eLpNorm (fun t ↦ f (x, t)) p ν :=
      (enorm_integral_le_lintegral_enorm _).trans
        (lintegral_enorm_le_eLpNorm_one.trans (eLpNorm_le_eLpNorm_of_exponent_le hp))
    have hpow := ENNReal.rpow_le_rpow hnorm hpr.le
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hx,
      ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one] at hpow
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.integral_prod_right',
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  exact (lintegral_mono_ae hpoint).trans_eq
    (lintegral_prod _ (hf.enorm.pow_const _)).symm

/-- The Bochner average over positive heights at most ε. -/
def heightAverage (ε : ℝ) (f : ℝ^(n + 1) → F) (x : ℝ^n) : F :=
  ε⁻¹ • ∫ t in Ioc 0 ε, f (joinTangentialNormal (x, t))

/-- Equal upper-half-space representatives have equal height averages almost everywhere. -/
theorem heightAverage_congr_ae (ε : ℝ) {f g : ℝ^(n + 1) → F}
    (hfg : f =ᵐ[volume.restrict ℝ^(n + 1)₊] g) :
    heightAverage ε f =ᵐ[volume] heightAverage ε g := by
  have hprod := measurePreserving_joinTangentialNormal_upper.quasiMeasurePreserving.ae_eq_comp hfg
  have hsmall : (volume : Measure (ℝ^n)).prod (volume.restrict (Ioc 0 ε)) ≤
      (volume : Measure (ℝ^n)).prod positiveNormalMeasure :=
    Measure.prod_mono le_rfl (Measure.restrict_mono (fun _ h ↦ h.1) le_rfl)
  filter_upwards [Measure.ae_ae_of_ae_prod (ae_mono hsmall hprod)] with x hx
  exact congrArg (ε⁻¹ • ·) (integral_congr_ae hx)

omit [NormedSpace ℝ F] in
/-- Finite-p functions have integrable fibers over every bounded positive height interval. -/
theorem ae_integrable_height (p : ℝ) (hp : 1 ≤ p) (ε : ℝ)
    {f : ℝ^(n + 1) → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊)) :
    ∀ᵐ x ∂(volume : Measure (ℝ^n)),
      Integrable (fun t ↦ f (joinTangentialNormal (x, t))) (volume.restrict (Ioc 0 ε)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hp))
  have hsmall : (volume : Measure (ℝ^n)).prod (volume.restrict (Ioc 0 ε)) ≤
      (volume : Measure (ℝ^n)).prod positiveNormalMeasure :=
    Measure.prod_mono le_rfl (Measure.restrict_mono (fun _ h ↦ h.1) le_rfl)
  have hprod := (hf.comp_measurePreserving
    measurePreserving_joinTangentialNormal_upper).mono_measure hsmall
  filter_upwards [hprod.aestronglyMeasurable.prodMk_left,
    (hprod.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top).prod_right_ae] with x hx hi
  exact ((integrable_norm_rpow_iff hx hp0 ENNReal.ofReal_ne_top).mp hi).integrable
    (by simpa using (ENNReal.ofReal_le_ofReal hp))

/-- The finite-p seminorm bound for the physical height average. -/
theorem eLpNorm_heightAverage_le (p : ℝ) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    {f : ℝ^(n + 1) → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊)) :
    eLpNorm (heightAverage ε f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ε ^ (-(1 / p)) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) := by
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
  have hformula : heightAverage ε f = fun x ↦ ∫ t, f (joinTangentialNormal (x, t)) ∂η := by
    funext x
    simp [heightAverage, η, integral_smul_measure, ENNReal.toReal_ofReal hε.le]
  rw [hformula]
  calc
    _ ≤ eLpNorm (f ∘ joinTangentialNormal) (ENNReal.ofReal p) (μ.prod η) :=
      eLpNorm_integral_probability_le μ η (by simpa using ENNReal.ofReal_le_ofReal hp)
        ENNReal.ofReal_ne_top hscaled.aestronglyMeasurable
    _ = ENNReal.ofReal ε ^ (-(1 / p)) *
        eLpNorm (f ∘ joinTangentialNormal) (ENNReal.ofReal p)
          (μ.prod (volume.restrict (Ioc 0 ε))) := by
      rw [show μ.prod η = (ENNReal.ofReal ε)⁻¹ •
        μ.prod (volume.restrict (Ioc 0 ε)) by exact Measure.prod_smul_right _,
        eLpNorm_smul_measure_of_ne_zero_of_ne_top
          (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hp)))
          ENNReal.ofReal_ne_top]
      simp [ENNReal.toReal_ofReal (le_trans zero_le_one hp), ENNReal.inv_rpow,
        ENNReal.rpow_neg, one_div]
    _ ≤ ENNReal.ofReal ε ^ (-(1 / p)) *
        eLpNorm (f ∘ joinTangentialNormal) (ENNReal.ofReal p) (μ.prod positiveNormalMeasure) := by
      gcongr
    _ = _ := by
      rw [eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        measurePreserving_joinTangentialNormal_upper]

/-- The physical height average of an upper-half-space Lp function belongs to boundary Lp. -/
theorem memLp_heightAverage (p : ℝ) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    {f : ℝ^(n + 1) → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊)) :
    MemLp (heightAverage ε f) (ENNReal.ofReal p) volume := by
  apply lt_of_le_of_lt (eLpNorm_heightAverage_le p hp ε hε hf)
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top)) hf.eLpNorm_lt_top

/-- Height averages respect addition almost everywhere on finite-p representatives. -/
theorem heightAverage_add_ae (p : ℝ) (hp : 1 ≤ p) (ε : ℝ)
    {f g : ℝ^(n + 1) → F}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊)) :
    heightAverage ε (f + g) =ᵐ[volume] heightAverage ε f + heightAverage ε g := by
  filter_upwards [ae_integrable_height p hp ε hf, ae_integrable_height p hp ε hg]
    with x hx hy
  simp only [heightAverage, Pi.add_apply, integral_add hx hy, smul_add]

/-- Scalar multiplication commutes with the physical height average. -/
theorem heightAverage_smul (ε c : ℝ) (f : ℝ^(n + 1) → F) :
    heightAverage ε (c • f) = c • heightAverage ε f := by
  funext x
  simp only [heightAverage, Pi.smul_apply, integral_smul]
  exact smul_comm _ _ _

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The bounded height average on upper-half-space Lp classes. -/
def heightAverageLp (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    Lp F (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) →L[ℝ]
      Lp F (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
  LinearMap.mkContinuous
    { toFun := fun U ↦ (memLp_heightAverage p hp ε hε (Lp.memLp U)).toLp _
      map_add' := fun U V ↦ by
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
        exact (heightAverage_congr_ae ε (Lp.coeFn_add U V)).trans
          (heightAverage_add_ae p hp ε (Lp.memLp U) (Lp.memLp V))
      map_smul' := fun c U ↦ by
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
        exact (heightAverage_congr_ae ε (Lp.coeFn_smul c U)).trans
          (EventuallyEq.of_eq (heightAverage_smul ε c U)) }
    (ε ^ (-(1 / p))) (fun U ↦ by
      change ‖(memLp_heightAverage p hp ε hε (Lp.memLp U)).toLp _‖ ≤ _
      rw [Lp.norm_toLp, Lp.norm_def]
      have hfin : ENNReal.ofReal ε ^ (-(1 / p)) *
          eLpNorm U (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≠ ∞ :=
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
            ENNReal.ofReal_ne_top) (Lp.memLp U).eLpNorm_ne_top
      simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal hε.le] using
          ENNReal.toReal_mono hfin (eLpNorm_heightAverage_le p hp ε hε (Lp.memLp U)))

/-- The Lp class produced by height averaging has the literal integral representative. -/
theorem coeFn_heightAverageLp (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    (U : Lp F (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊)) :
    (heightAverageLp n p hp ε hε U : ℝ^n → F) =ᵐ[volume]
      fun x ↦ ε⁻¹ • ∫ t in Ioc 0 ε, U (joinTangentialNormal (x, t)) :=
  (memLp_heightAverage p hp ε hε (Lp.memLp U)).coeFn_toLp

/-- The physical height-average formula holds for any representative of the input Lp class. -/
theorem heightAverageLp_eq_integral_of_ae_eq
    (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    (U : Lp F (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊))
    {f : ℝ^(n + 1) → F}
    (hf : (U : ℝ^(n + 1) → F) =ᵐ[volume.restrict ℝ^(n + 1)₊] f) :
    (heightAverageLp n p hp ε hε U : ℝ^n → F) =ᵐ[volume]
      fun x ↦ ε⁻¹ • ∫ t in Ioc 0 ε, f (joinTangentialNormal (x, t)) :=
  (coeFn_heightAverageLp n p hp ε hε U).trans (heightAverage_congr_ae ε hf)

/-- Height averaging has operator norm at most `ε ^ (-(1 / p))`. -/
theorem norm_heightAverageLp_le (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ‖heightAverageLp (F := F) n p hp ε hε‖ ≤ ε ^ (-(1 / p)) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg hε.le _) _

end SobolevSpace.Trace.HalfSpace
