/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.SpaceTime.TensorProduct
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.Integration.LocallyIntegrable
import PDE.Analysis.MeasureTheory.SpaceTime
import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Weak spatial derivatives of compact time averages

Testing a spacetime weak derivative with a tensor test and applying Fubini
identifies the spatial weak derivative of its time average.
Only local integrability is required: the time weight has compact support,
and the spatial tests localize the remaining integral.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

namespace SobolevSpace.Slices

open MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions

variable {n : ℕ}

private theorem measurePreserving_timeSpaceCons :
    MeasurePreserving (timeSpaceContinuousLinearEquiv n).symm
      (volume.prod volume) volume := by
  rw [← Measure.volume_eq_prod ℝ (ℝ^n)]
  exact MeasurePreserving.symm
    (timeSpaceContinuousLinearEquiv n).toHomeomorph.toMeasurableEquiv
    PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv

private theorem locallyIntegrable_timeSpaceCons {f : ℝ^(n + 1) → ℝ}
    (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons p.1 p.2))
      (volume.prod volume) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (measurePreserving_timeSpaceCons.integrableOn_image
    (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph.measurableEmbedding).mp
      (hf.integrableOn_isCompact
        (hK.image (timeSpaceContinuousLinearEquiv n).symm.continuous))

/-- A compact time average of a locally integrable spacetime field is
locally integrable in the spatial variables. -/
theorem locallyIntegrable_timeAverage {f : ℝ^(n + 1) → ℝ}
    (hf : LocallyIntegrable f volume) (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    LocallyIntegrable (fun x ↦ ∫ t, ψ t * f (timeSpaceCons t x)) volume := by
  simpa only [smul_eq_mul] using
    (locallyIntegrable_timeSpaceCons hf).integral_smul_left
      ψ.contDiff.continuous ψ.hasCompactSupport

/-- A nonnegative compact time weight of mass one preserves an almost-everywhere
bound. The field only needs to satisfy the bound where the weight is nonzero. -/
theorem ae_norm_timeAverage_le {f : ℝ^(n + 1) → ℝ} {C : ℝ}
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (hψ : ∀ t, 0 ≤ ψ t)
    (hmass : ∫ t, ψ t = 1)
    (hC : ∀ᵐ p ∂volume, ψ (p 0) ≠ 0 → ‖f p‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖∫ t, ψ t * f (timeSpaceCons t x)‖ ≤ C := by
  have hp := measurePreserving_timeSpaceCons.quasiMeasurePreserving.ae hC
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp
  have hi : Integrable ψ volume :=
    ψ.contDiff.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with x hx
  have hb : ∀ᵐ t ∂volume, ‖ψ t * f (timeSpaceCons t x)‖ ≤ ψ t * C := by
    filter_upwards [hx] with t ht
    by_cases hz : ψ t = 0
    · simp only [hz, zero_mul, norm_zero, le_refl]
    · rw [norm_mul, Real.norm_of_nonneg (hψ t)]
      apply mul_le_mul_of_nonneg_left _ (hψ t)
      exact ht hz
  simpa only [integral_mul_const, hmass, one_mul] using
    norm_integral_le_of_norm_le (hi.mul_const C) hb

/-- A uniform approximation on the nonzero time weight passes to the
average. Local integrability supplies measurable time fibers almost everywhere;
no pointwise measurability of all fibers is assumed. -/
theorem ae_norm_timeAverage_sub_le {f : ℝ^(n + 1) → ℝ}
    (hf : LocallyIntegrable f volume) {v : ℝ^n → ℝ} {C : ℝ}
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (hψ : ∀ t, 0 ≤ ψ t)
    (hmass : ∫ t, ψ t = 1)
    (hC : ∀ᵐ p ∂volume, ψ (p 0) ≠ 0 → ‖f p - v (spatialPart p)‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖(∫ t, ψ t * f (timeSpaceCons t x)) - v x‖ ≤ C := by
  have hdelta := ae_norm_timeAverage_le ψ hψ hmass hC
  have hp := measurePreserving_timeSpaceCons.quasiMeasurePreserving.ae hC
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp
  have hms := (locallyIntegrable_timeSpaceCons hf).aestronglyMeasurable.prodMk_right
  have hi : Integrable ψ volume :=
    ψ.contDiff.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  filter_upwards [hdelta, Measure.ae_ae_of_ae_prod hs, hms] with x hx hbound hmeas
  have hb : ∀ᵐ t ∂volume,
      ‖ψ t * f (timeSpaceCons t x)‖ ≤ ψ t * (C + ‖v x‖) := by
    filter_upwards [hbound] with t ht
    by_cases hz : ψ t = 0
    · simp only [hz, zero_mul, norm_zero, le_refl]
    · rw [norm_mul, Real.norm_of_nonneg (hψ t)]
      apply mul_le_mul_of_nonneg_left _ (hψ t)
      have hd : ‖f (timeSpaceCons t x) - v x‖ ≤ C := by
        simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply,
          spatialPart_timeSpaceCons, timeSpaceCons_zero, Prod.swap] using ht hz
      calc
        ‖f (timeSpaceCons t x)‖ ≤ ‖f (timeSpaceCons t x) - v x‖ + ‖v x‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ C + ‖v x‖ := add_le_add hd le_rfl
  have hif : Integrable (fun t ↦ ψ t * f (timeSpaceCons t x)) volume :=
    (hi.mul_const (C + ‖v x‖)).mono'
      (hi.aestronglyMeasurable.mul hmeas) hb
  have heq : (∫ t, ψ t * (f (timeSpaceCons t x) - v x)) =
      (∫ t, ψ t * f (timeSpaceCons t x)) - v x := by
    simp only [mul_sub]
    rw [integral_sub hif (hi.mul_const _), integral_mul_const, hmass, one_mul]
  rw [← heq]
  simpa only [spatialPart_timeSpaceCons] using hx

private theorem integral_timeAverage_mul_test {f : ℝ^(n + 1) → ℝ}
    (hf : LocallyIntegrable f volume) (ψ : 𝓓((⊤ : Opens ℝ), ℝ))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x, (∫ t, ψ t * f (timeSpaceCons t x)) * φ x) =
      ∫ t, ψ t * ∫ x, f (timeSpaceCons t x) * φ x := by
  have hi := hf.integrable_smul_right_of_hasCompactSupport
    (TestFunction.timeSpaceTensor ψ φ).contDiff.continuous
    (TestFunction.timeSpaceTensor ψ φ).hasCompactSupport
  have hip := measurePreserving_timeSpaceCons.integrable_comp_of_integrable hi
  simp only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply,
    TestFunction.timeSpaceTensor_timeSpaceCons, smul_eq_mul] at hip
  have heq := integral_integral_swap
    (f := fun t x ↦ f (timeSpaceCons t x) * (ψ t * φ x)) hip
  have hfactor (t : ℝ) (x : ℝ^n) :
      f (timeSpaceCons t x) * (ψ t * φ x) =
        ψ t * (f (timeSpaceCons t x) * φ x) := mul_left_comm _ _ _
  calc
    (∫ x, (∫ t, ψ t * f (timeSpaceCons t x)) * φ x) =
        ∫ x, ∫ t, f (timeSpaceCons t x) * (ψ t * φ x) := by
      simp only [hfactor, ← mul_assoc, integral_mul_const]
    _ = ∫ t, ∫ x, f (timeSpaceCons t x) * (ψ t * φ x) := heq.symm
    _ = ∫ t, ψ t * ∫ x, f (timeSpaceCons t x) * φ x := by
      simp only [hfactor, integral_const_mul]

/-- Compact averaging in time commutes with every weak spatial
partial derivative. The average is the Lebesgue integral. -/
theorem _root_.SobolevSpace.HasWeakDerivativeOn.timeAverage
    {f g : ℝ^(n + 1) → ℝ} (i : Fin n)
    (h : HasWeakDerivativeOn univ [i.succ] f g)
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    HasWeakDerivativeOn univ [i]
      (fun x ↦ ∫ t, ψ t * f (timeSpaceCons t x))
      (fun x ↦ ∫ t, ψ t * g (timeSpaceCons t x)) := by
  have hf := locallyIntegrableOn_univ.mp h.locallyIntegrable_f
  have hg := locallyIntegrableOn_univ.mp h.locallyIntegrable_g
  refine ⟨(locallyIntegrable_timeAverage hf ψ).locallyIntegrableOn univ,
    (locallyIntegrable_timeAverage hg ψ).locallyIntegrableOn univ, ?_⟩
  intro φ _hφ
  let D : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) φ
  have hD (x : ℝ^n) : D x = (∂[i] φ.toFun) x := by
    simp only [D, TestFunction.lineDerivCLM_apply_eq_fderiv, partialDeriv,
      TestFunction.toFun_eq_coe]
  let Φ := TestFunction.timeSpaceTensor ψ φ
  have hi0 := h.integrable_mul_iteratedPartialDeriv Φ (subset_univ _)
  have hj0 := h.integrable_mul_testFunction Φ (subset_univ _)
  have heq := h Φ (subset_univ _)
  simp only [domainMeasure, Measure.restrict_univ] at hi0 hj0 heq
  have hi := measurePreserving_timeSpaceCons.integrable_comp_of_integrable hi0
  have hj := measurePreserving_timeSpaceCons.integrable_comp_of_integrable hj0
  rw [← measurePreserving_timeSpaceCons.integral_comp
    (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph.measurableEmbedding,
    ← measurePreserving_timeSpaceCons.integral_comp
    (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph.measurableEmbedding] at heq
  simp only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply,
    TestFunction.toFun_eq_coe, iteratedPartialDeriv, Φ,
    TestFunction.partialDeriv_timeSpaceTensor_succ,
    TestFunction.timeSpaceTensor_timeSpaceCons] at hi hj heq
  rw [integral_prod _ hi, integral_prod _ hj] at heq
  have hfactor (v : ℝ^(n + 1) → ℝ) (w : ℝ^n → ℝ) (t : ℝ) :
      (∫ x, v (timeSpaceCons t x) * (ψ t * w x)) =
        ψ t * ∫ x, v (timeSpaceCons t x) * w x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ ↦ mul_left_comm _ _ _)
  simp only [hfactor] at heq
  have hleft := integral_timeAverage_mul_test hf ψ D
  simp only [hD] at hleft
  simp only [domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
    List.length_singleton, pow_one, neg_one_mul]
  rw [hleft]
  simp only [TestFunction.toFun_eq_coe]
  rw [integral_timeAverage_mul_test hg ψ φ]
  simpa only [List.length_singleton, pow_one, neg_one_mul,
    TestFunction.toFun_eq_coe] using heq

end SobolevSpace.Slices
