/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Compatibility
public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation

/-!
# The unitary angular-frequency Fourier convention

The unitary convention uses the kernels `exp (±I ⟪x, ξ⟫)` and the factor
`(2π)^(-dim(E)/2)`. Frequency dilation relates these integrals to Mathlib's
Fourier transform. The same dilation on `L²` gives their almost-everywhere
representatives, with the Jacobian exactly canceling the normalization factor.

This is the convention of Evans, §4.3.1(a): `unitaryFourierIntegral` and
`unitaryFourierInvIntegral` are his definitions (1) and (2), and his Theorem 1 (Plancherel's
theorem) is `memLp_unitaryFourierIntegral` with `eLpNorm_unitaryFourierIntegral` and their
inverse versions. Evans then extends the transform to `L²` by density; we define
`unitaryFourier` as a rescaled frequency dilation (`Lp.compSMul`) of Mathlib's Fourier
transform on `L²`, and `unitaryFourierIntegral_eq_L2_ae` shows that the two agree on
`L¹ ∩ L²`. The norm identity `norm_unitaryFourier` comes from Mathlib's
`MeasureTheory.Lp.norm_fourier_eq`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.1(a), the definitions (1)-(2) and Theorem 1
  (Plancherel's theorem), p. 187, and the definition of the Fourier transform on `L²`, p. 189.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap InnerProductSpace ENNReal

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A scalar change of variables in the Fourier integral, in any finite dimension. -/
theorem fourierIntegral_comp_smul (f : E → F) {a : ℝ} (ha : a ≠ 0) (ξ : E) :
    𝓕 (fun x ↦ f (a • x)) ξ =
      |(a ^ Module.finrank ℝ E)⁻¹| • 𝓕 f (a⁻¹ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← Measure.integral_comp_smul volume]
  congr 1
  funext x
  rw [real_inner_smul_left, inner_smul_right]
  simp [ha]

private def schwartzDilation (a : ℝ) (ha : a ≠ 0) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha))

omit [CompleteSpace F] in
private theorem compSMul_toLp (a : ℝ) (ha : a ≠ 0) (f : 𝓢(E, F)) :
    Lp.compSMul volume 2 a ha (f.toLp 2) = (schwartzDilation a ha f).toLp 2 := by
  apply Lp.ext
  have hcomp : (fun x : E ↦ (f.toLp 2 : E → F) (a • x)) =ᵐ[volume]
      fun x ↦ f (a • x) :=
    (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp (f.coeFn_toLp 2)
  filter_upwards [Lp.coeFn_compSMul (volume : Measure E) 2 a ha (f.toLp 2),
    hcomp, (schwartzDilation a ha f).coeFn_toLp 2] with x h₁ h₂ h₃
  rw [h₁, h₃]
  simpa only [schwartzDilation, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
    Units.val_mk0] using h₂

omit [CompleteSpace F] in
private theorem fourier_schwartzDilation (a : ℝ) (ha : a ≠ 0) (f : 𝓢(E, F)) :
    𝓕 (schwartzDilation a ha f) =
      |(a ^ Module.finrank ℝ E)⁻¹| •
        schwartzDilation a⁻¹ (inv_ne_zero ha) (𝓕 f) := by
  ext ξ
  exact fourierIntegral_comp_smul f ha ξ

/-- Fourier dilation on `L²`, extended from the integral identity by Schwartz density. -/
theorem fourier_compSMul (a : ℝ) (ha : a ≠ 0) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (Lp.compSMul volume 2 a ha f) =
      |(a ^ Module.finrank ℝ E)⁻¹| •
        Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha) (𝓕 f) := by
  let p : Lp F 2 (volume : Measure E) → Prop := fun g ↦
    𝓕 (Lp.compSMul volume 2 a ha g) =
      |(a ^ Module.finrank ℝ E)⁻¹| •
        Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha) (𝓕 g)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      (continuous_fourier.comp (Lp.compSMul volume 2 a ha).continuous)
      (((Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha)).continuous.comp
        continuous_fourier).const_smul |(a ^ Module.finrank ℝ E)⁻¹|)
  intro g
  change 𝓕 (Lp.compSMul volume 2 a ha (g.toLp 2)) =
    |(a ^ Module.finrank ℝ E)⁻¹| •
      Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha) (𝓕 (g.toLp 2))
  rw [compSMul_toLp, SchwartzMap.toLp_fourier_eq, fourier_schwartzDilation,
    SchwartzMap.toLp_fourier_eq, compSMul_toLp]
  exact (SchwartzMap.toLpCLM ℝ F 2 volume).map_smul _ _

variable (E) in
/-- The unitary normalization factor for angular frequencies. -/
def unitaryFourierFactor : ℝ :=
  (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalization factor is positive, including in dimension zero. -/
theorem unitaryFourierFactor_pos : 0 < unitaryFourierFactor E :=
  Real.rpow_pos_of_pos (by positivity) _

/-- The Fourier integral with the unitary angular-frequency convention. -/
def unitaryFourierIntegral (f : E → F) (ξ : E) : F :=
  unitaryFourierFactor E •
    ∫ x, Complex.exp (-(↑⟪x, ξ⟫_ℝ : ℂ) * Complex.I) • f x

/-- The inverse Fourier integral with the unitary angular-frequency convention. -/
def unitaryFourierInvIntegral (f : E → F) (ξ : E) : F :=
  unitaryFourierFactor E •
    ∫ x, Complex.exp ((↑⟪x, ξ⟫_ℝ : ℂ) * Complex.I) • f x

omit [CompleteSpace F] in
/-- Conversion from Mathlib's Fourier integral to angular frequencies. -/
theorem unitaryFourierIntegral_eq (f : E → F) (ξ : E) :
    unitaryFourierIntegral f ξ =
      unitaryFourierFactor E • 𝓕 f ((2 * Real.pi)⁻¹ • ξ) := by
  rw [unitaryFourierIntegral, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  rw [inner_smul_right]
  push_cast
  field_simp

omit [CompleteSpace F] in
/-- Conversion from Mathlib's inverse Fourier integral to angular frequencies. -/
theorem unitaryFourierInvIntegral_eq (f : E → F) (ξ : E) :
    unitaryFourierInvIntegral f ξ =
      unitaryFourierFactor E • 𝓕⁻ f ((2 * Real.pi)⁻¹ • ξ) := by
  rw [unitaryFourierInvIntegral, Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  rw [inner_smul_right]
  push_cast
  field_simp

/-- The unitary angular-frequency Fourier transform on `L²`. -/
def unitaryFourier (f : Lp F 2 (volume : Measure E)) : Lp F 2 (volume : Measure E) :=
  unitaryFourierFactor E •
    Lp.compSMul volume 2 (2 * Real.pi)⁻¹ (by positivity) (𝓕 f)

/-- The inverse unitary angular-frequency Fourier transform on `L²`. -/
def unitaryFourierInv (f : Lp F 2 (volume : Measure E)) : Lp F 2 (volume : Measure E) :=
  unitaryFourierFactor E •
    Lp.compSMul volume 2 (2 * Real.pi)⁻¹ (by positivity) (𝓕⁻ f)

/-- The normalized `L²` Fourier representative is a scaled frequency dilation. -/
theorem coe_unitaryFourier (f : Lp F 2 (volume : Measure E)) :
    (unitaryFourier f : E → F) =ᵐ[volume]
      fun ξ ↦ unitaryFourierFactor E • (𝓕 f : Lp F 2 volume) ((2 * Real.pi)⁻¹ • ξ) := by
  have ha : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  filter_upwards [Lp.coeFn_smul (unitaryFourierFactor E)
    (Lp.compSMul volume 2 (2 * Real.pi)⁻¹ ha (𝓕 f)),
    Lp.coeFn_compSMul volume 2 (2 * Real.pi)⁻¹ ha (𝓕 f)] with ξ h₁ h₂
  simpa only [unitaryFourier, Pi.smul_apply, h₂] using h₁

/-- The normalized inverse `L²` representative is a scaled frequency dilation. -/
theorem coe_unitaryFourierInv (f : Lp F 2 (volume : Measure E)) :
    (unitaryFourierInv f : E → F) =ᵐ[volume]
      fun ξ ↦ unitaryFourierFactor E • (𝓕⁻ f : Lp F 2 volume) ((2 * Real.pi)⁻¹ • ξ) := by
  have ha : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  filter_upwards [Lp.coeFn_smul (unitaryFourierFactor E)
    (Lp.compSMul volume 2 (2 * Real.pi)⁻¹ ha (𝓕⁻ f)),
    Lp.coeFn_compSMul volume 2 (2 * Real.pi)⁻¹ ha (𝓕⁻ f)] with ξ h₁ h₂
  simpa only [unitaryFourierInv, Pi.smul_apply, h₂] using h₁

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem unitaryFourierFactor_norm_cancel :
    unitaryFourierFactor E *
      |(((2 * Real.pi)⁻¹) ^ Module.finrank ℝ E)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal = 1 := by
  have h : 0 < 2 * Real.pi := by positivity
  rw [inv_pow, inv_inv, abs_of_pos (pow_pos h _)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [unitaryFourierFactor, ← Real.rpow_natCast_mul h.le, ← Real.rpow_add h]
  convert Real.rpow_zero (2 * Real.pi) using 1
  congr 1
  ring

/-- Plancherel's norm identity in the unitary angular-frequency convention. -/
@[simp] theorem norm_unitaryFourier (f : Lp F 2 (volume : Measure E)) :
    ‖unitaryFourier f‖ = ‖f‖ := by
  rw [unitaryFourier, norm_smul, Real.norm_eq_abs,
    abs_of_pos unitaryFourierFactor_pos, Lp.norm_compSMul, ← mul_assoc,
    unitaryFourierFactor_norm_cancel, one_mul, Lp.norm_fourier_eq]

/-- The inverse transform has the same norm identity. -/
@[simp] theorem norm_unitaryFourierInv (f : Lp F 2 (volume : Measure E)) :
    ‖unitaryFourierInv f‖ = ‖f‖ := by
  rw [unitaryFourierInv, norm_smul, Real.norm_eq_abs,
    abs_of_pos unitaryFourierFactor_pos, Lp.norm_compSMul, ← mul_assoc,
    unitaryFourierFactor_norm_cancel, one_mul]
  exact (Lp.fourierTransformₗᵢ E F).symm.norm_map f

/-- On `L¹ ∩ L²`, the normalized Fourier integral represents the normalized `L²` transform. -/
theorem unitaryFourierIntegral_eq_L2_ae {g : E → F} (hg : Integrable g)
    (G : Lp F 2 (volume : Measure E)) (hG : g =ᵐ[volume] G) :
    unitaryFourierIntegral g =ᵐ[volume] unitaryFourier G := by
  have ha : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hcomp := (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp
    (fourierIntegral_eq_L2_ae hg G hG)
  filter_upwards [hcomp, coe_unitaryFourier G] with ξ h₁ h₂
  simpa only [unitaryFourierIntegral_eq, h₂, Function.comp_apply] using
    congrArg (unitaryFourierFactor E • ·) h₁

/-- On `L¹ ∩ L²`, the normalized inverse integral represents the normalized inverse on `L²`. -/
theorem unitaryFourierInvIntegral_eq_L2_ae {g : E → F} (hg : Integrable g)
    (G : Lp F 2 (volume : Measure E)) (hG : g =ᵐ[volume] G) :
    unitaryFourierInvIntegral g =ᵐ[volume] unitaryFourierInv G := by
  have ha : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hcomp := (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp
    (fourierInvIntegral_eq_L2_ae hg G hG)
  filter_upwards [hcomp, coe_unitaryFourierInv G] with ξ h₁ h₂
  simpa only [unitaryFourierInvIntegral_eq, h₂, Function.comp_apply] using
    congrArg (unitaryFourierFactor E • ·) h₁

/-- The normalized Fourier integral of a function in `L¹ ∩ L²` belongs to `L²`. -/
theorem memLp_unitaryFourierIntegral {f : E → F} (h₁ : Integrable f)
    (h₂ : MemLp f 2 volume) : MemLp (unitaryFourierIntegral f) 2 volume :=
  (memLp_congr_ae
    (unitaryFourierIntegral_eq_L2_ae h₁ (h₂.toLp f) h₂.coeFn_toLp.symm)).mpr
      (Lp.memLp _)

/-- The normalized inverse integral of a function in `L¹ ∩ L²` belongs to `L²`. -/
theorem memLp_unitaryFourierInvIntegral {f : E → F} (h₁ : Integrable f)
    (h₂ : MemLp f 2 volume) : MemLp (unitaryFourierInvIntegral f) 2 volume :=
  (memLp_congr_ae
    (unitaryFourierInvIntegral_eq_L2_ae h₁ (h₂.toLp f) h₂.coeFn_toLp.symm)).mpr
      (Lp.memLp _)

/-- Plancherel's identity for the normalized Fourier integral of a function in `L¹ ∩ L²`. -/
theorem eLpNorm_unitaryFourierIntegral {f : E → F} (h₁ : Integrable f)
    (h₂ : MemLp f 2 volume) :
    eLpNorm (unitaryFourierIntegral f) 2 volume = eLpNorm f 2 volume := by
  rw [eLpNorm_congr_ae
    (unitaryFourierIntegral_eq_L2_ae h₁ (h₂.toLp f) h₂.coeFn_toLp.symm),
    ← Lp.enorm_def, ← ofReal_norm, norm_unitaryFourier, ofReal_norm, Lp.enorm_toLp]

/-- Plancherel's identity for the normalized inverse integral of a function in `L¹ ∩ L²`. -/
theorem eLpNorm_unitaryFourierInvIntegral {f : E → F} (h₁ : Integrable f)
    (h₂ : MemLp f 2 volume) :
    eLpNorm (unitaryFourierInvIntegral f) 2 volume = eLpNorm f 2 volume := by
  rw [eLpNorm_congr_ae
    (unitaryFourierInvIntegral_eq_L2_ae h₁ (h₂.toLp f) h₂.coeFn_toLp.symm),
    ← Lp.enorm_def, ← ofReal_norm, norm_unitaryFourierInv, ofReal_norm, Lp.enorm_toLp]

omit [CompleteSpace F] in
private theorem compSMul_complex_smul (a : ℝ) (ha : a ≠ 0) (z : ℂ)
    (f : Lp F 2 (volume : Measure E)) :
    Lp.compSMul volume 2 a ha (z • f) = z • Lp.compSMul volume 2 a ha f := by
  apply Lp.ext
  have hcomp := (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp
    (Lp.coeFn_smul z f)
  filter_upwards [hcomp, Lp.coeFn_compSMul volume 2 a ha (z • f),
    Lp.coeFn_compSMul volume 2 a ha f,
    Lp.coeFn_smul z (Lp.compSMul volume 2 a ha f)] with x h₁ h₂ h₃ h₄
  simpa only [h₂, h₄, Pi.smul_apply, h₃, Function.comp_apply] using h₁

/-- The normalized Fourier transform is a complex-linear isometry. -/
def unitaryFourierIsometry : Lp F 2 (volume : Measure E) →ₗᵢ[ℂ] Lp F 2 (volume : Measure E) where
  toFun := unitaryFourier
  map_add' f g := by
    have hadd : 𝓕 (f + g) = (𝓕 f + 𝓕 g : Lp F 2 (volume : Measure E)) :=
      (Lp.fourierTransformₗᵢ E F).map_add f g
    unfold unitaryFourier
    rw [hadd, map_add, smul_add]
  map_smul' z f := by
    have hsmul : 𝓕 (z • f) = (z • 𝓕 f : Lp F 2 (volume : Measure E)) :=
      (Lp.fourierTransformₗᵢ E F).map_smul z f
    unfold unitaryFourier
    rw [hsmul, compSMul_complex_smul, smul_comm]
    rfl
  norm_map' := norm_unitaryFourier

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The square of the unitary Fourier factor cancels the Jacobian `|(2π)^{-d}|⁻¹`. -/
theorem unitaryFourierFactor_sq_cancel :
    unitaryFourierFactor E *
      (unitaryFourierFactor E * |(((2 * Real.pi)⁻¹) ^ Module.finrank ℝ E)⁻¹|) = 1 := by
  have h : 0 < 2 * Real.pi := by positivity
  rw [inv_pow, inv_inv, abs_of_pos (pow_pos h _), unitaryFourierFactor,
    ← Real.rpow_natCast, ← Real.rpow_add h, ← Real.rpow_add h]
  convert Real.rpow_zero (2 * Real.pi) using 1
  congr 1
  ring

/-- The normalized Fourier transform undoes its normalized inverse on all of `L²`. -/
@[simp] theorem unitaryFourier_unitaryFourierInv (f : Lp F 2 (volume : Measure E)) :
    unitaryFourier (unitaryFourierInv f) = f := by
  have ha : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hsmul (g : Lp F 2 (volume : Measure E)) :
      𝓕 (unitaryFourierFactor E • g) = unitaryFourierFactor E • 𝓕 g :=
    (fourierCLM ℂ (Lp F 2 (volume : Measure E))).map_smul_of_tower _ _
  unfold unitaryFourier unitaryFourierInv
  rw [hsmul, fourier_compSMul, fourier_fourierInv_eq, map_smul, map_smul,
    ← Lp.compSMul_mul]
  simp only [mul_inv_cancel₀ ha, Lp.compSMul_one,
    smul_smul, unitaryFourierFactor_sq_cancel, one_smul]

/-- The normalized inverse undoes the normalized Fourier transform on all of `L²`. -/
@[simp] theorem unitaryFourierInv_unitaryFourier (f : Lp F 2 (volume : Measure E)) :
    unitaryFourierInv (unitaryFourier f) = f := by
  apply (unitaryFourierIsometry (E := E) (F := F)).injective
  exact unitaryFourier_unitaryFourierInv (unitaryFourier f)

/-- The unitary angular-frequency Fourier transform as a complex-linear isometry equivalence. -/
def unitaryFourierEquiv : Lp F 2 (volume : Measure E) ≃ₗᵢ[ℂ] Lp F 2 (volume : Measure E) where
  toLinearEquiv :=
    { (unitaryFourierIsometry (E := E) (F := F)).toLinearMap with
      invFun := unitaryFourierInv
      left_inv := unitaryFourierInv_unitaryFourier
      right_inv := unitaryFourier_unitaryFourierInv }
  norm_map' := norm_unitaryFourier

end PDE.Analysis.Fourier
