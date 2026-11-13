/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.AreaFormula.LinearApproximation
public import PDE.Analysis.MeasureTheory.AreaFormula.Localization
public import PDE.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The area formula for injective C¹ immersions

The Euclidean Hausdorff measure of an injectively parametrized set is the integral
of the volume factor of its derivative. Locally, strict differentiability compares
the parametrization with its injective linear derivative. Continuity of the volume
factor then gives two-sided estimates for the weighted measure. Localization and
a limit of the multiplicative error prove exact equality, including for infinite
measure and zero-dimensional parameter spaces.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [MeasurableSpace F] [BorelSpace F]

/-- The C¹ area formula on a measurable subset of an open parameter domain.
The derivative need only be injective on the subset being integrated. -/
theorem euclideanHausdorffMeasure_image_eq_lintegral_normDet_of_contDiffOn
    {V s : Set E} {f : E → F} (hV : IsOpen V) (hf : ContDiffOn ℝ 1 f V)
    (hs : MeasurableSet s) (hsV : s ⊆ V) (hinj : InjOn f s)
    (hderiv : ∀ x ∈ s, Function.Injective (fderiv ℝ f x)) :
    Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).toLinearMap.normDet := by
  let J : E → ℝ := fun x ↦ (fderiv ℝ f x).toLinearMap.normDet
  let μ : Measure E := volume.withDensity (fun x ↦ ENNReal.ofReal (J x))
  let ν : Measure F := Measure.euclideanHausdorffMeasure (Module.finrank ℝ E)
  have hJ : ContinuousOn J V :=
    ContinuousLinearMap.continuous_normDet.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hV le_rfl)
  have hcomparison : ∀ c : ℝ≥0, 1 < c →
      ν (f '' s) ≤ (c : ℝ≥0∞) ^ (Module.finrank ℝ E + 1) * μ s ∧
      μ s ≤ (c : ℝ≥0∞) ^ (Module.finrank ℝ E + 1) * ν (f '' s) := by
    intro c hc
    apply measure_image_comparison_of_locally hs (hf.continuousOn.mono hsV) hinj
    intro x hx
    have hxV := hsV hx
    have hJxpos : 0 < J x := (LinearMap.normDet_nonneg _).lt_of_ne fun hzero ↦
      (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hzero.symm)
        (LinearMap.ker_eq_bot.mpr (hderiv x hx))
    have hJxlt : J x < c * J x := lt_mul_of_one_lt_left hJxpos (show (1 : ℝ) < c from hc)
    have hJat : ContinuousAt J x := (hJ x hxV).continuousAt (hV.mem_nhds hxV)
    have hbounds : ∀ᶠ y in 𝓝 x, J x ≤ c * J y ∧ J y ≤ c * J x :=
      ((continuousAt_const.eventually_lt (continuousAt_const.mul hJat) hJxlt).and
        (hJat.eventually_lt continuousAt_const hJxlt)).mono fun y hy ↦ ⟨hy.1.le, hy.2.le⟩
    obtain ⟨u, hu, harea⟩ :=
      ((hf x hxV).contDiffAt (hV.mem_nhds hxV)).hasStrictFDerivAt one_ne_zero
        |>.exists_nhds_area_comparison (hderiv x hx) hc
    refine ⟨u ∩ {y | J x ≤ c * J y ∧ J y ≤ c * J x},
      inter_mem hu hbounds, fun t ht htmeas ↦ ?_⟩
    have htJ : ∀ y ∈ t, J x ≤ c * J y ∧ J y ≤ c * J x := fun y hy ↦ (ht hy).2.2
    have hμt : μ t = ∫⁻ y in t, ENNReal.ofReal (J y) := withDensity_apply _ htmeas
    have hlinear_le : ENNReal.ofReal (J x) * volume t ≤ c * μ t := by
      rw [hμt, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← setLIntegral_const]
      exact setLIntegral_mono' htmeas fun y hy ↦ by
        simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal (htJ y hy).1
    have hμ_le : μ t ≤ c * (ENNReal.ofReal (J x) * volume t) := by
      rw [hμt, ← mul_assoc, ← setLIntegral_const]
      exact setLIntegral_mono' htmeas fun y hy ↦ by
        simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal (htJ y hy).2
    obtain ⟨hupper, hlower⟩ := harea t fun y hy ↦ (ht hy).2.1
    refine ⟨hupper.trans ?_, hμ_le.trans ?_⟩
    · calc _ ≤ (c : ℝ≥0∞) ^ Module.finrank ℝ E * (c * μ t) := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc]
    · calc _ ≤ c * ((c : ℝ≥0∞) ^ Module.finrank ℝ E * ν (f '' t)) := by gcongr
        _ = _ := by rw [pow_succ]; ac_rfl
  have hlimit (a : ℝ≥0∞) : Tendsto (fun c : ℝ≥0 ↦ (c : ℝ≥0∞) ^ (Module.finrank ℝ E + 1) * a)
      (𝓝[>] 1) (𝓝 a) := by
    have hp : Tendsto (fun c : ℝ≥0 ↦ (c : ℝ≥0∞) ^ (Module.finrank ℝ E + 1)) (𝓝[>] 1) (𝓝 1) := by
      have hcoe : Tendsto (fun c : ℝ≥0 ↦ (c : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        ENNReal.tendsto_coe.2 (tendsto_id.mono_left nhdsWithin_le_nhds)
      simpa only [one_pow] using ENNReal.Tendsto.pow hcoe (n := Module.finrank ℝ E + 1)
    simpa using ENNReal.Tendsto.mul_const hp (Or.inl one_ne_zero) (b := a)
  have heq : ν (f '' s) = μ s := le_antisymm
    (ge_of_tendsto (hlimit _) (eventually_mem_nhdsWithin.mono fun c hc ↦ (hcomparison c hc).1))
    (ge_of_tendsto (hlimit _) (eventually_mem_nhdsWithin.mono fun c hc ↦ (hcomparison c hc).2))
  exact heq.trans (withDensity_apply _ hs)

/-- The Jacobian-weighted parameter measure pushes forward to Hausdorff
measure restricted to the image of an injective C¹ immersion. -/
theorem map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure
    {V : Set E} {f : E → F} (hV : IsOpen V) (hf : ContDiffOn ℝ 1 f V)
    (hinj : InjOn f V) (hderiv : ∀ x ∈ V, Function.Injective (fderiv ℝ f x)) :
    Measure.map f ((volume.restrict V).withDensity
      (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).toLinearMap.normDet)) =
        (Measure.euclideanHausdorffMeasure (Module.finrank ℝ E)).restrict (f '' V) := by
  have hfae : AEMeasurable f (volume.restrict V) :=
    hf.continuousOn.aemeasurable hV.measurableSet
  have hfweighted := hfae.mono_ac
    (withDensity_absolutelyContinuous (volume.restrict V)
      (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).toLinearMap.normDet))
  apply Measure.ext
  intro t ht
  have hpre : MeasurableSet (f ⁻¹' t ∩ V) := by
    have hsub : MeasurableSet ((fun x : V ↦ f x) ⁻¹' t) :=
      ht.preimage hf.continuousOn.domRestrict.measurable
    have himage := (MeasurableEmbedding.subtype_coe hV.measurableSet).measurableSet_image.mpr
      hsub
    convert himage using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists,
      exists_and_right, exists_eq_right]
    tauto
  have hpre₀ := hfae.nullMeasurableSet_preimage ht
  rw [Measure.map_apply_of_aemeasurable hfweighted ht, withDensity_apply₀ _ hpre₀,
    Measure.restrict_restrict₀ hpre₀, Measure.restrict_apply ht,
    ← euclideanHausdorffMeasure_image_eq_lintegral_normDet_of_contDiffOn
      hV hf hpre inter_subset_right (hinj.mono inter_subset_right)
      (fun x hx ↦ hderiv x hx.2), image_preimage_inter]

/-- The signed Bochner area formula for a C¹ immersion, expressed with the
derivative and Hausdorff measure. -/
theorem integral_image_eq_integral_normDet_smul_of_contDiffOn
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Set E} {f : E → F} (hV : IsOpen V) (hf : ContDiffOn ℝ 1 f V)
    (hinj : InjOn f V) (hderiv : ∀ x ∈ V, Function.Injective (fderiv ℝ f x))
    (g : F → G)
    (hg : AEStronglyMeasurable g
      ((Measure.euclideanHausdorffMeasure (Module.finrank ℝ E)).restrict (f '' V))) :
    ∫ y in f '' V, g y ∂Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) =
      ∫ x in V, (fderiv ℝ f x).toLinearMap.normDet • g (f x) := by
  have hmap := map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure
    hV hf hinj hderiv
  have hfae : AEMeasurable f (volume.restrict V) :=
    hf.continuousOn.aemeasurable hV.measurableSet
  have hfweighted := hfae.mono_ac
    (withDensity_absolutelyContinuous (volume.restrict V)
      (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).toLinearMap.normDet))
  rw [← hmap] at hg ⊢
  rw [integral_map hfweighted hg, integral_withDensity_eq_integral_toReal_smul₀]
  · congr 1
    funext x
    rw [ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)]
  · exact (ENNReal.continuous_ofReal.comp_continuousOn
      (ContinuousLinearMap.continuous_normDet.comp_continuousOn
        (hf.continuousOn_fderiv_of_isOpen hV le_rfl))).aemeasurable hV.measurableSet
  · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top

/-- Integrability on the image of a C¹ immersion is exactly integrability of the
Jacobian-weighted pullback. In particular, the area formula transports absolute
integrability as well as signed integrals. -/
theorem integrableOn_image_iff_integrableOn_normDet_smul_of_contDiffOn
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Set E} {f : E → F} (hV : IsOpen V) (hf : ContDiffOn ℝ 1 f V)
    (hinj : InjOn f V) (hderiv : ∀ x ∈ V, Function.Injective (fderiv ℝ f x))
    {g : F → G}
    (hg : AEStronglyMeasurable g
      ((Measure.euclideanHausdorffMeasure (Module.finrank ℝ E)).restrict (f '' V))) :
    IntegrableOn g (f '' V) (Measure.euclideanHausdorffMeasure (Module.finrank ℝ E)) ↔
      IntegrableOn (fun x ↦ (fderiv ℝ f x).toLinearMap.normDet • g (f x)) V := by
  have hmap := map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure
    hV hf hinj hderiv
  have hfae : AEMeasurable f (volume.restrict V) :=
    hf.continuousOn.aemeasurable hV.measurableSet
  have hfweighted := hfae.mono_ac
    (withDensity_absolutelyContinuous (volume.restrict V)
      (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).toLinearMap.normDet))
  have hJae : AEMeasurable
      (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).toLinearMap.normDet) (volume.restrict V) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
    (ContinuousLinearMap.continuous_normDet.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hV le_rfl))).aemeasurable hV.measurableSet
  unfold IntegrableOn
  rw [← hmap] at hg ⊢
  rw [integrable_map_measure hg hfweighted,
    integrable_withDensity_iff_integrable_smul₀' hJae
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _), Function.comp_apply]

end MeasureTheory
