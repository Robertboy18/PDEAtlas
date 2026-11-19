/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.Operator

/-!
# Real Bessel hyperplane trace and lifting

The normal-frequency integral preserves Hermitian symmetry. Consequently the
bounded hyperplane trace and its explicit lifting restrict to the
real Bessel spaces, with the same norm bounds and right-inverse identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace ComplexConjugate Sobolev

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

/-- Integrating against the real even normal kernel preserves Hermitian symmetry. -/
theorem normalRestriction_splitFrequency_isHermitian (n : ℕ)
    {v : Lp ℂ 2 (volume : Measure ℝ^(n + 1))} (hv : IsHermitianL2 v) :
    IsHermitianL2 (normalRestriction n (splitFrequencyLI n v)) := by
  let A := splitFrequencyLI n v
  have hA : ∀ᵐ p ∂(volume : Measure ℝ^n).prod (volume : Measure ℝ),
      conj (A (-p)) = A p := by
    rw [← Measure.volume_eq_prod]
    have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
    have hmneg : MeasurePreserving (fun p : ℝ^n × ℝ ↦ -p) volume volume := by
      convert (Measure.measurePreserving_neg (volume : Measure ℝ^n)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ)) using 1
      rfl
    have hneg := hmneg.quasiMeasurePreserving.ae (splitFrequencyLI_apply_ae n v)
    filter_upwards [hneg, splitFrequencyLI_apply_ae n v,
      hm.quasiMeasurePreserving.ae (isHermitianL2_ae hv)] with p h1 h2 h3
    change conj (splitFrequencyLI n v (-p)) = splitFrequencyLI n v p
    rw [h1, h2]
    have hj : joinTangentialNormal (-p) = -joinTangentialNormal p :=
      (tangentialNormalContinuousLinearEquiv (n := n)).symm.map_neg p
    rw [hj]
    simpa only [tangentialNormalMeasurableEquiv_symm_apply] using h3
  apply Lp.ext
  filter_upwards [coeFn_reflL2 (star (normalRestriction n A)),
    ae_neg (Lp.coeFn_star (normalRestriction n A)),
    ae_neg (normalRestriction_apply_ae A), normalRestriction_apply_ae A,
    Measure.ae_ae_of_ae_prod hA] with ξ h1 h2 h3 h4 h5
  rw [h1, h2]
  change conj (normalRestriction n A (-ξ)) = normalRestriction n A ξ
  rw [h3, h4]
  change conj (∫ t, normalKernel (tangentialScale (-ξ)) t • A (-ξ, t)) =
    ∫ t, normalKernel (tangentialScale ξ) t • A (ξ, t)
  have hs : tangentialScale (-ξ) = tangentialScale ξ := by
    apply NNReal.eq
    simp only [tangentialScale, norm_neg]
  rw [hs, ← integral_conj, ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [h5] with t ht
  simp only [normalKernel_neg, Complex.real_smul, map_mul, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ ↦ (normalKernel (tangentialScale ξ) t : ℂ) * z) ht

/-- The normalized complex trace preserves the real Bessel subspace. -/
theorem besselNormalRestrictionCLM_mem_real (n : ℕ) (u : H^{1}(ℝ^(n + 1); ℝ)) :
    besselNormalRestrictionCLM n u ∈ hsRealSubmodule n (1 / 2) := by
  rw [mem_HsRealSubmodule_iff, isRealL2_iff_isHermitian_fourier,
    fourier_toLp_besselNormalRestrictionCLM]
  apply normalRestriction_splitFrequency_isHermitian
  exact (isRealL2_iff_isHermitian_fourier _).1 (mem_HsRealSubmodule_iff.1 u.property)

/-- Physical normalization also preserves real-valued Bessel elements. -/
theorem wholeSpaceTraceCLM_mem_real (n : ℕ) (u : H^{1}(ℝ^(n + 1); ℝ)) :
    wholeSpaceTraceCLM n u ∈ hsRealSubmodule n (1 / 2) := by
  change Real.sqrt Real.pi • besselNormalRestrictionCLM n u ∈ _
  exact (hsRealSubmodule n (1 / 2)).smul_mem _ (besselNormalRestrictionCLM_mem_real n u)

/-- The hyperplane trace on real Bessel spaces. -/
def wholeSpaceTraceRealCLM (n : ℕ) :
    H^{1}(ℝ^(n + 1); ℝ) →L[ℝ] H^{1 / 2}(ℝ^n; ℝ) :=
  (((wholeSpaceTraceCLM n).restrictScalars ℝ).comp
    (hsRealSubmodule (n + 1) 1).subtypeL).codRestrict
      (hsRealSubmodule n (1 / 2)) (wholeSpaceTraceCLM_mem_real n)

/-- The explicit bounded real lifting of hyperplane data. -/
def wholeSpaceLiftingRealCLM (n : ℕ) :
    H^{1 / 2}(ℝ^n; ℝ) →L[ℝ] H^{1}(ℝ^(n + 1); ℝ) :=
  (Real.sqrt Real.pi)⁻¹ • (besselNormalLiftRealLI n).toContinuousLinearMap

/-- The real trace has the same analytic bound as the complex trace. -/
theorem norm_wholeSpaceTraceRealCLM_apply_le (n : ℕ) (u : H^{1}(ℝ^(n + 1); ℝ)) :
    ‖wholeSpaceTraceRealCLM n u‖ ≤ Real.sqrt Real.pi * ‖u‖ :=
  norm_wholeSpaceTraceCLM_apply_le n u.val

/-- Forgetting realness in the real lifting gives the complex lifting. -/
theorem wholeSpaceLiftingRealCLM_val (n : ℕ) (v : H^{1 / 2}(ℝ^n; ℝ)) :
    (wholeSpaceLiftingRealCLM n v).val = wholeSpaceLiftingCLM n v := by
  change ((Real.sqrt Real.pi)⁻¹ : ℝ) • besselNormalLiftLI n v =
    (Real.sqrt Real.pi : ℂ)⁻¹ • besselNormalLiftLI n v
  rw [← Complex.ofReal_inv]
  rfl

/-- The real lifting has the explicit norm given by the normal kernel. -/
theorem norm_wholeSpaceLiftingRealCLM (n : ℕ) (v : H^{1 / 2}(ℝ^n; ℝ)) :
    ‖wholeSpaceLiftingRealCLM n v‖ = (Real.sqrt Real.pi)⁻¹ * ‖v‖ := by
  change ‖(wholeSpaceLiftingRealCLM n v).val‖ = _
  rw [wholeSpaceLiftingRealCLM_val, norm_wholeSpaceLiftingCLM]
  rfl

/-- Every real fractional boundary element has the constructed whole-space lift. -/
theorem wholeSpaceTraceRealCLM_wholeSpaceLiftingRealCLM (n : ℕ)
    (v : H^{1 / 2}(ℝ^n; ℝ)) :
    wholeSpaceTraceRealCLM n (wholeSpaceLiftingRealCLM n v) = v := by
  apply Subtype.ext
  change wholeSpaceTraceCLM n (wholeSpaceLiftingRealCLM n v).val = v.val
  rw [wholeSpaceLiftingRealCLM_val, wholeSpaceTraceCLM_wholeSpaceLiftingCLM]

end SobolevSpace.Fractional.Trace
