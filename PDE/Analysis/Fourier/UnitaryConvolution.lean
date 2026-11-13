/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Convolution
public import PDE.Analysis.Fourier.L2Reconstruction
public import PDE.Analysis.Fourier.UnitaryNormalization

/-!
# Convolution in the unitary angular-frequency convention

For any two complex `L²` functions, their convolution equals `(2π)^(dim(E)/2)`
times the inverse unitary Fourier integral of the product of their transforms.
That product is integrable by Hölder, so this identity holds at every point.

The convolution belongs to `L²` exactly when the product of the transforms does.
Under either condition its `L²` Fourier transform is `(2π)^(dim(E)/2)` times that
product. The domain conditions are needed because an `L²` convolution need
not belong to `L²`. The inverse formula and domain equivalence impose no global
`L¹` assumption on either input.

If the first input is also integrable, the final two lemmas supply the `L²`
membership and the forward formula. This includes the corrected convolution
theorem for two inputs in `L¹ ∩ L²`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped Convolution

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The reciprocal normalization factor is the coefficient in the unitary
Fourier convolution formula. -/
theorem inv_unitaryFourierFactor :
    (unitaryFourierFactor E)⁻¹ = (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  rw [unitaryFourierFactor, ← Real.rpow_neg (by positivity)]
  congr 1
  ring

private theorem fourierInvIntegral_comp_smul (f : E → ℂ) {a : ℝ}
    (ha : a ≠ 0) (x : E) :
    𝓕⁻ (fun ξ ↦ f (a • ξ)) x =
      |(a ^ Module.finrank ℝ E)⁻¹| • 𝓕⁻ f (a⁻¹ • x) := by
  rw [Real.fourierInv_eq_fourier_neg, fourierIntegral_comp_smul f ha,
    Real.fourierInv_eq_fourier_neg, smul_neg]

private theorem fourierInvIntegral_const_smul (c : ℝ) (f : E → ℂ) (x : E) :
    𝓕⁻ (c • f) x = c • 𝓕⁻ f x := by
  simp only [Real.fourierInv_eq', Pi.smul_apply, smul_comm _ c, integral_smul]


/-- The product of two unitary `L²` Fourier transforms is integrable. -/
theorem integrable_unitaryFourier_mul_L2 (u v : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun ξ ↦ unitaryFourier u ξ * unitaryFourier v ξ) :=
  (Lp.memLp (unitaryFourier u)).integrable_mul (Lp.memLp (unitaryFourier v))

/-- For arbitrary `L²` inputs, the actual convolution is the normalized inverse
integral of the Fourier product, with coefficient `(2π)^(dim(E)/2)`. This equality
is pointwise and does not assert square-integrability of the convolution. -/
theorem convolution_eq_unitaryFourierInvIntegral_mul_L2
    (u v : Lp ℂ 2 (volume : Measure E)) :
    (u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ) =
      (unitaryFourierFactor E)⁻¹ •
        unitaryFourierInvIntegral (fun ξ ↦ unitaryFourier u ξ * unitaryFourier v ξ) := by
  have ha : 2 * Real.pi ≠ 0 := by positivity
  have hc : unitaryFourierFactor E ≠ 0 := ne_of_gt unitaryFourierFactor_pos
  let Q : E → ℂ := fun ξ ↦ (𝓕 u : Lp ℂ 2 volume) ξ * (𝓕 v : Lp ℂ 2 volume) ξ
  have hprod : (fun ξ ↦ unitaryFourier u ξ * unitaryFourier v ξ) =ᵐ[volume]
      (unitaryFourierFactor E * unitaryFourierFactor E) •
        (fun ξ ↦ Q ((2 * Real.pi)⁻¹ • ξ)) := by
    filter_upwards [coe_unitaryFourier u, coe_unitaryFourier v] with ξ hu hv
    rw [hu, hv, smul_mul_smul_comm]
    rfl
  have hnormalize (x : E) :
      unitaryFourierInvIntegral (fun ξ ↦ unitaryFourier u ξ * unitaryFourier v ξ) x =
        unitaryFourierFactor E • 𝓕⁻ Q x := by
    rw [unitaryFourierInvIntegral_eq, Real.fourierInv_congr_ae hprod,
      fourierInvIntegral_const_smul, fourierInvIntegral_comp_smul Q (inv_ne_zero ha)]
    simp only [inv_inv, smul_smul, mul_inv_cancel₀ ha, one_smul, mul_assoc,
      unitaryFourierFactor_sq_cancel]
  funext x
  rw [Pi.smul_apply, hnormalize, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact congrFun (convolution_eq_fourierInv_mul_L2 u v) x

/-- If an `L²` class represents the convolution, its unitary Fourier transform is
`(2π)^(dim(E)/2)` times the Fourier product. Square-integrability of the product
is a consequence, not a premise. -/
theorem unitaryFourier_eq_of_convolution_eq_ae
    (u v w : Lp ℂ 2 (volume : Measure E))
    (hw : (u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ) =ᵐ[volume] w) :
    (unitaryFourier w : E → ℂ) =ᵐ[volume]
      fun ξ ↦ (unitaryFourierFactor E)⁻¹ • (unitaryFourier u ξ * unitaryFourier v ξ) := by
  have hc : unitaryFourierFactor E ≠ 0 := ne_of_gt unitaryFourierFactor_pos
  have hraw := fourier_eq_of_fourierInvIntegral_eq_ae (integrable_fourier_mul_L2 u v) w
    (by rwa [← convolution_eq_fourierInv_mul_L2])
  have hcomp := (Measure.quasiMeasurePreserving_smul volume
    (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)).ae_eq_comp hraw
  filter_upwards [coe_unitaryFourier w, coe_unitaryFourier u, coe_unitaryFourier v,
    hcomp] with ξ hwξ huξ hvξ hξ
  simp only [Function.comp_apply] at hξ
  rw [hwξ, hξ, huξ, hvξ, smul_mul_smul_comm, smul_smul, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

/-- A convolution of `L²` functions belongs to `L²` exactly when the product of
their unitary Fourier transforms does. Neither condition is automatic. -/
theorem memLp_convolution_iff_unitaryFourier_mul_L2
    (u v : Lp ℂ 2 (volume : Measure E)) :
    MemLp ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ)) 2 volume ↔
      MemLp (fun ξ ↦ unitaryFourier u ξ * unitaryFourier v ξ) 2 volume := by
  constructor
  · intro h
    let w := h.toLp ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ))
    have hfourier := unitaryFourier_eq_of_convolution_eq_ae u v w h.coeFn_toLp.symm
    have hc : unitaryFourierFactor E ≠ 0 := ne_of_gt unitaryFourierFactor_pos
    have heq : unitaryFourierFactor E • (unitaryFourier w : E → ℂ) =ᵐ[volume]
        fun ξ ↦ unitaryFourier u ξ * unitaryFourier v ξ := by
      filter_upwards [hfourier] with ξ hξ
      simp only [Pi.smul_apply, hξ, smul_smul, mul_inv_cancel₀ hc, one_smul]
    exact (memLp_congr_ae heq).mp ((Lp.memLp (unitaryFourier w)).const_smul _)
  · intro h
    rw [convolution_eq_unitaryFourierInvIntegral_mul_L2]
    exact (memLp_unitaryFourierInvIntegral (integrable_unitaryFourier_mul_L2 u v) h).const_smul _

/-- The forward unitary Fourier convolution formula on its `L²` domain. The
membership proof forms the class of the actual convolution. -/
theorem unitaryFourier_convolution_L2 (u v : Lp ℂ 2 (volume : Measure E))
    (h : MemLp ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ)) 2 volume) :
    (unitaryFourier (h.toLp _) : E → ℂ) =ᵐ[volume]
      fun ξ ↦ (unitaryFourierFactor E)⁻¹ • (unitaryFourier u ξ * unitaryFourier v ξ) :=
  unitaryFourier_eq_of_convolution_eq_ae u v (h.toLp _) h.coeFn_toLp.symm

/-- The convolution of two `L²` functions belongs to `L²` if the first input is
integrable. The Fourier transform of that input is bounded, so the Fourier
product belongs to `L²`. -/
theorem memLp_convolution_L2_of_integrable_left
    (u v : Lp ℂ 2 (volume : Measure E)) (hu : Integrable (u : E → ℂ)) :
    MemLp ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ)) 2 volume := by
  have htop : MemLp (unitaryFourier u : E → ℂ) ⊤ volume := by
    refine memLp_top_of_bound (Lp.aestronglyMeasurable _)
      (unitaryFourierFactor E * ∫ x, ‖u x‖) ?_
    filter_upwards [unitaryFourierIntegral_eq_L2_ae hu u Filter.EventuallyEq.rfl]
      with ξ hξ
    rw [← hξ, unitaryFourierIntegral_eq, norm_smul, Real.norm_eq_abs,
      abs_of_pos unitaryFourierFactor_pos]
    exact mul_le_mul_of_nonneg_left
      (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
        volume (innerₗ E) (u : E → ℂ) ((2 * Real.pi)⁻¹ • ξ))
      unitaryFourierFactor_pos.le
  exact (memLp_convolution_iff_unitaryFourier_mul_L2 u v).mpr
    (htop.fun_mul (Lp.memLp (unitaryFourier v)))

/-- The forward unitary Fourier convolution formula holds for two `L²` inputs
when the first is integrable, with `L²` membership supplied by the preceding
lemma. In particular, this covers two inputs in `L¹ ∩ L²`. -/
theorem unitaryFourier_convolution_L2_of_integrable_left
    (u v : Lp ℂ 2 (volume : Measure E)) (hu : Integrable (u : E → ℂ)) :
    (unitaryFourier ((memLp_convolution_L2_of_integrable_left u v hu).toLp _) : E → ℂ)
      =ᵐ[volume] fun ξ ↦ (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) •
        (unitaryFourier u ξ * unitaryFourier v ξ) := by
  simpa only [inv_unitaryFourierFactor] using
    unitaryFourier_convolution_L2 u v (memLp_convolution_L2_of_integrable_left u v hu)

end PDE.Analysis.Fourier
