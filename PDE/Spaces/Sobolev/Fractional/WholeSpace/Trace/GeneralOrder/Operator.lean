/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.FrequencyRestriction
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.BesselRestriction

/-!
# General-order Hilbert Sobolev trace and lifting

For every `s > 1/2`, the normalized fiber integral transports through the
Bessel and Fourier isometries to a bounded map `H^s → H^(s-1/2)`.
Multiplication by `sqrt (J(s))` fixes the physical Fourier normalization.
The explicit kernel lifting is a right inverse with exact norm
`‖v‖ / sqrt (J(s))`. Agreement with physical restriction requires the
kernel cancellation and the Fourier slice identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace

namespace SobolevSpace.Fractional.Trace.GeneralOrder

open SobolevSpace.Trace.HalfSpace

variable {s : ℝ}

/-- The general-order kernel lifting in ambient Euclidean frequency coordinates. -/
def frequencyLiftEuclideanLI (n : ℕ) (hs : 1 / 2 < s) :
    Lp ℂ 2 (volume : Measure ℝ^n) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ^(n + 1)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ tangentialNormalMeasurableEquiv
    measurePreserving_tangentialNormalMeasurableEquiv).comp (frequencyLiftLI n hs)

theorem frequencyLiftEuclideanLI_apply_ae (n : ℕ) (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    frequencyLiftEuclideanLI n hs v =ᵐ[volume]
      fun x ↦ frequencyLiftFun s v (splitTangentialNormal x) := by
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).quasiMeasurePreserving
  simpa [frequencyLiftEuclideanLI, Lp.compMeasurePreservingₗᵢ, Lp.compMeasurePreservingₗ,
    frequencyLiftLI, tangentialNormalMeasurableEquiv_apply] using
    (Lp.coeFn_compMeasurePreserving (frequencyLift hs v)
      measurePreserving_tangentialNormalMeasurableEquiv).trans
      (hm.ae (frequencyLift_apply_ae hs v))

theorem splitFrequencyLI_frequencyLiftEuclideanLI (n : ℕ) (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    splitFrequencyLI n (frequencyLiftEuclideanLI n hs v) = frequencyLift hs v := by
  apply Lp.ext
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
  filter_upwards [splitFrequencyLI_apply_ae n (frequencyLiftEuclideanLI n hs v),
    hm.quasiMeasurePreserving.ae (frequencyLiftEuclideanLI_apply_ae n hs v),
    frequencyLift_apply_ae hs v] with p h1 h2 h3
  simp only [tangentialNormalMeasurableEquiv_symm_apply, split_joinTangentialNormal] at h2
  rw [h1, h2, h3]

/-- Isometric lifting in the Bessel spaces. -/
def besselLiftLI (n : ℕ) (hs : 1 / 2 < s) :
    H^{s - 1 / 2}(ℝ^n) →ₗᵢ[ℂ] H^{s}(ℝ^(n + 1)) :=
  (toLpₗᵢ (ℝ^(n + 1)) ℂ s 2).symm.toLinearIsometry.comp
    ((Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).symm.toLinearIsometry.comp
      ((frequencyLiftEuclideanLI n hs).comp
        ((Lp.fourierTransformₗᵢ (ℝ^n) ℂ).toLinearIsometry.comp
          (toLpₗᵢ (ℝ^n) ℂ (s - 1 / 2) 2).toLinearIsometry)))

theorem fourier_toLp_besselLiftLI (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n)) :
    𝓕 (toLp (besselLiftLI n hs v)) = frequencyLiftEuclideanLI n hs (𝓕 (toLp v)) := by
  simp only [besselLiftLI, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [← toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply, toLpₗᵢ_apply]
  exact (Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).apply_symm_apply _

/-- Contractive restriction in normalized Bessel Fourier coordinates. -/
def besselRestrictionCLM (n : ℕ) (hs : 1 / 2 < s) :
    H^{s}(ℝ^(n + 1)) →L[ℂ] H^{s - 1 / 2}(ℝ^n) :=
  (toLpₗᵢ (ℝ^n) ℂ (s - 1 / 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    frequencyRestriction n hs ∘L (splitFrequencyLI n).toContinuousLinearMap ∘L
    (Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (toLpₗᵢ (ℝ^(n + 1)) ℂ s 2).toContinuousLinearEquiv.toContinuousLinearMap

theorem fourier_toLp_besselRestrictionCLM (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1))) :
    𝓕 (toLp (besselRestrictionCLM n hs u)) =
      frequencyRestriction n hs (splitFrequencyLI n (𝓕 (toLp u))) := by
  simp only [besselRestrictionCLM, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
  rw [← toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply, toLpₗᵢ_apply]
  exact (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).apply_symm_apply _

theorem norm_besselRestrictionCLM_apply_le (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1))) : ‖besselRestrictionCLM n hs u‖ ≤ ‖u‖ := by
  rw [← norm_fourier_toLp_eq, fourier_toLp_besselRestrictionCLM]
  calc
    _ ≤ ‖splitFrequencyLI n (𝓕 (toLp u))‖ := norm_frequencyRestriction_apply_le n hs _
    _ = ‖u‖ := by rw [LinearIsometry.norm_map, norm_fourier_toLp_eq]

theorem besselRestrictionCLM_besselLiftLI (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n)) : besselRestrictionCLM n hs (besselLiftLI n hs v) = v := by
  apply injective_toLp (ℝ^n) ℂ (s - 1 / 2) 2
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (toLp (besselRestrictionCLM n hs (besselLiftLI n hs v))) = 𝓕 (toLp v)
  rw [fourier_toLp_besselRestrictionCLM, fourier_toLp_besselLiftLI,
    splitFrequencyLI_frequencyLiftEuclideanLI, frequencyRestriction_frequencyLift]

/-- The general-order hyperplane trace with its physical normalization. -/
def wholeSpaceTraceCLM (n : ℕ) (hs : 1 / 2 < s) :
    H^{s}(ℝ^(n + 1)) →L[ℂ] H^{s - 1 / 2}(ℝ^n) :=
  (traceConstant s : ℂ) • besselRestrictionCLM n hs

/-- The explicit bounded right inverse of the general-order trace. -/
def wholeSpaceLiftingCLM (n : ℕ) (hs : 1 / 2 < s) :
    H^{s - 1 / 2}(ℝ^n) →L[ℂ] H^{s}(ℝ^(n + 1)) :=
  (traceConstant s : ℂ)⁻¹ • (besselLiftLI n hs).toContinuousLinearMap

theorem fourier_toLp_wholeSpaceTraceCLM (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1))) :
    𝓕 (toLp (wholeSpaceTraceCLM n hs u)) =
      (traceConstant s : ℂ) • frequencyRestriction n hs
        (splitFrequencyLI n (𝓕 (toLp u))) := by
  rw [wholeSpaceTraceCLM, smul_apply, toLp_smul, fourier_smul,
    fourier_toLp_besselRestrictionCLM]

/-- Weighted Fourier coordinates of the explicit right inverse. -/
theorem fourier_toLp_wholeSpaceLiftingCLM (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n)) :
    𝓕 (toLp (wholeSpaceLiftingCLM n hs v)) =
      (traceConstant s : ℂ)⁻¹ • frequencyLiftEuclideanLI n hs (𝓕 (toLp v)) := by
  rw [wholeSpaceLiftingCLM, smul_apply, toLp_smul, fourier_smul]
  exact congrArg (fun w ↦ (traceConstant s : ℂ)⁻¹ • w) (fourier_toLp_besselLiftLI n hs v)

/-- The trace estimate is dimension independent and uses a proved finite integral. -/
theorem norm_wholeSpaceTraceCLM_apply_le (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1))) :
    ‖wholeSpaceTraceCLM n hs u‖ ≤ traceConstant s * ‖u‖ := by
  rw [wholeSpaceTraceCLM, smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (traceConstant_pos hs)]
  exact mul_le_mul_of_nonneg_left (norm_besselRestrictionCLM_apply_le n hs u)
    (traceConstant_pos hs).le

theorem norm_wholeSpaceLiftingCLM (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n)) :
    ‖wholeSpaceLiftingCLM n hs v‖ = (traceConstant s)⁻¹ * ‖v‖ := by
  simp only [wholeSpaceLiftingCLM, smul_apply, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (traceConstant_pos hs),
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]

theorem wholeSpaceTraceCLM_wholeSpaceLiftingCLM (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n)) :
    wholeSpaceTraceCLM n hs (wholeSpaceLiftingCLM n hs v) = v := by
  have hc : (traceConstant s : ℂ) ≠ 0 := by exact_mod_cast (traceConstant_pos hs).ne'
  simp only [wholeSpaceTraceCLM, wholeSpaceLiftingCLM, smul_apply,
    map_smul, LinearIsometry.coe_toContinuousLinearMap,
    besselRestrictionCLM_besselLiftLI, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem wholeSpaceTraceCLM_surjective (n : ℕ) (hs : 1 / 2 < s) :
    Function.Surjective (wholeSpaceTraceCLM n hs) :=
  fun v ↦ ⟨wholeSpaceLiftingCLM n hs v, wholeSpaceTraceCLM_wholeSpaceLiftingCLM n hs v⟩

end SobolevSpace.Fractional.Trace.GeneralOrder
