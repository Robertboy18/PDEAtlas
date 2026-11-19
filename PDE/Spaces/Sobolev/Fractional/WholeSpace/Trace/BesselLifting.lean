/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalIntegral
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal

/-!
# Normal-frequency lifting in Bessel spaces

The isometric lifting in normalized Fourier coordinates transports to the
Bessel spaces. The kernel is real and even under simultaneous
reflection of tangential and normal frequencies, so the lifting preserves
the real subspaces. This provides the analytic lifting construction;
its normalization as a physical trace right inverse also uses the Fourier
slice theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal NNReal BesselPotentialSpace ComplexConjugate

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

/-- The normal-frequency lifting in the ambient Euclidean coordinate convention. -/
def normalLiftEuclideanLI (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ^n) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ^(n + 1)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ tangentialNormalMeasurableEquiv
    measurePreserving_tangentialNormalMeasurableEquiv).comp (normalLiftLI n)

/-- Pointwise coordinates of the Euclidean lifting. -/
theorem normalLiftEuclideanLI_apply_ae (n : ℕ) (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    normalLiftEuclideanLI n v =ᵐ[volume]
      fun x ↦ normalLiftFun v (splitTangentialNormal x) := by
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).quasiMeasurePreserving
  simpa [normalLiftEuclideanLI, Lp.compMeasurePreservingₗᵢ, Lp.compMeasurePreservingₗ,
    normalLiftLI, tangentialNormalMeasurableEquiv_apply] using
    (Lp.coeFn_compMeasurePreserving (normalLift v)
    measurePreserving_tangentialNormalMeasurableEquiv).trans
    (hm.ae (normalLift_apply_ae v))

/-- Hermitian symmetry expressed on almost-everywhere Fourier representatives. -/
theorem isHermitianL2_ae {n : ℕ} {v : Lp ℂ 2 (volume : Measure ℝ^n)}
    (hv : IsHermitianL2 v) : ∀ᵐ ξ ∂volume, conj (v (-ξ)) = v ξ := by
  have h := coeFn_reflL2 (star v)
  rw [hv] at h
  filter_upwards [h, ae_neg (Lp.coeFn_star v)] with ξ h1 h2
  rw [h1, h2]
  rfl

/-- The Euclidean normal lifting preserves the Fourier symmetry of real functions. -/
theorem normalLiftEuclideanLI_isHermitian (n : ℕ)
    {v : Lp ℂ 2 (volume : Measure ℝ^n)} (hv : IsHermitianL2 v) :
    IsHermitianL2 (normalLiftEuclideanLI n v) := by
  apply Lp.ext
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).quasiMeasurePreserving
  have hvprod := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ^n))
    (ν := (volume : Measure ℝ))).ae (isHermitianL2_ae hv)
  have hsplit (x : ℝ^(n + 1)) :
      splitTangentialNormal (-x) = -splitTangentialNormal x :=
    (tangentialNormalContinuousLinearEquiv (n := n)).map_neg x
  filter_upwards [coeFn_reflL2 (star (normalLiftEuclideanLI n v)),
    ae_neg (Lp.coeFn_star (normalLiftEuclideanLI n v)),
    ae_neg (normalLiftEuclideanLI_apply_ae n v), normalLiftEuclideanLI_apply_ae n v,
    hm.ae hvprod] with x h1 h2 h3 h4 h5
  rw [h1, h2]
  change conj (normalLiftEuclideanLI n v (-x)) = normalLiftEuclideanLI n v x
  rw [h3, h4]
  simp only [normalLiftFun, hsplit, Prod.fst_neg, Prod.snd_neg]
  have hs : tangentialScale (-(splitTangentialNormal x).1) =
      tangentialScale (splitTangentialNormal x).1 := by
    apply NNReal.eq
    simp only [tangentialScale, norm_neg]
  simp only [tangentialNormalMeasurableEquiv_apply] at h5
  rw [hs, normalKernel_neg]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, h5]

/-- Isometric normal lifting from complex boundary `H^{1/2}` to whole-space `H¹`. -/
def besselNormalLiftLI (n : ℕ) : H^{(1 / 2 : ℝ)}(ℝ^n) →ₗᵢ[ℂ] H^{(1 : ℝ)}(ℝ^(n + 1)) :=
  (toLpₗᵢ (ℝ^(n + 1)) ℂ 1 2).symm.toLinearIsometry.comp
    ((Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).symm.toLinearIsometry.comp
      ((normalLiftEuclideanLI n).comp
        ((Lp.fourierTransformₗᵢ (ℝ^n) ℂ).toLinearIsometry.comp
          (toLpₗᵢ (ℝ^n) ℂ (1 / 2) 2).toLinearIsometry)))

/-- Bessel Fourier coordinates of the normal lifting. -/
theorem fourier_toLp_besselNormalLiftLI (n : ℕ) (v : H^{(1 / 2 : ℝ)}(ℝ^n)) :
    𝓕 (toLp (besselNormalLiftLI n v)) = normalLiftEuclideanLI n (𝓕 (toLp v)) := by
  simp only [besselNormalLiftLI, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [← toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [toLpₗᵢ_apply]
  exact (Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).apply_symm_apply _

/-- The Bessel normal lifting maps the real boundary space into real ambient `H¹`. -/
theorem besselNormalLiftLI_mem_real (n : ℕ) (v : HsSpaceReal n (1 / 2)) :
    besselNormalLiftLI n v ∈ hsRealSubmodule (n + 1) 1 := by
  rw [mem_HsRealSubmodule_iff, isRealL2_iff_isHermitian_fourier,
    fourier_toLp_besselNormalLiftLI]
  apply normalLiftEuclideanLI_isHermitian
  exact (isRealL2_iff_isHermitian_fourier _).1 (mem_HsRealSubmodule_iff.1 v.property)

private theorem real_smul_bessel {n : ℕ} {s : ℝ} (c : ℝ) (v : H^{s}(ℝ^n)) :
    c • v = (c : ℂ) • v := rfl

/-- The real Bessel-space normal lifting, with norm exactly preserved. -/
def besselNormalLiftRealLI (n : ℕ) :
    HsSpaceReal n (1 / 2) →ₗᵢ[ℝ] HsSpaceReal (n + 1) 1 where
  toFun v := ⟨besselNormalLiftLI n v, besselNormalLiftLI_mem_real n v⟩
  map_add' v w := by
    apply Subtype.ext
    exact map_add (besselNormalLiftLI n) v.val w.val
  map_smul' c v := by
    apply Subtype.ext
    change besselNormalLiftLI n (c • v.val) = c • besselNormalLiftLI n v.val
    simp only [real_smul_bessel, map_smul]
  norm_map' v := (besselNormalLiftLI n).norm_map v.val

end SobolevSpace.Fractional.Trace
