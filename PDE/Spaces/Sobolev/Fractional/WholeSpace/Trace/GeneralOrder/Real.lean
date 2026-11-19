/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.Operator

/-!
# General-order trace and lifting on real Hilbert Sobolev spaces

The kernel is real and invariant under simultaneous tangential and normal
reflection. Its lifting and integral therefore preserve Hermitian Fourier
symmetry. The constructed operators restrict to `HsSpaceReal`,
with the same bounds and right-inverse identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace ComplexConjugate Sobolev

namespace SobolevSpace.Fractional.Trace.GeneralOrder

open SobolevSpace.Trace.HalfSpace

variable {s : ℝ}

theorem frequencyLiftEuclideanLI_isHermitian (n : ℕ) (hs : 1 / 2 < s)
    {v : Lp ℂ 2 (volume : Measure ℝ^n)} (hv : IsHermitianL2 v) :
    IsHermitianL2 (frequencyLiftEuclideanLI n hs v) := by
  apply Lp.ext
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).quasiMeasurePreserving
  have hvprod := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ^n))
    (ν := (volume : Measure ℝ))).ae (isHermitianL2_ae hv)
  have hsplit (x : ℝ^(n + 1)) :
      splitTangentialNormal (-x) = -splitTangentialNormal x :=
    (tangentialNormalContinuousLinearEquiv (n := n)).map_neg x
  filter_upwards [coeFn_reflL2 (star (frequencyLiftEuclideanLI n hs v)),
    ae_neg (Lp.coeFn_star (frequencyLiftEuclideanLI n hs v)),
    ae_neg (frequencyLiftEuclideanLI_apply_ae n hs v),
    frequencyLiftEuclideanLI_apply_ae n hs v, hm.ae hvprod] with x h1 h2 h3 h4 h5
  rw [h1, h2]
  change conj (frequencyLiftEuclideanLI n hs v (-x)) = frequencyLiftEuclideanLI n hs v x
  rw [h3, h4]
  simp only [frequencyLiftFun, hsplit, Prod.fst_neg, Prod.snd_neg, frequencyKernel_neg]
  simp only [tangentialNormalMeasurableEquiv_apply] at h5
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, h5]

theorem frequencyRestriction_splitFrequency_isHermitian (n : ℕ) (hs : 1 / 2 < s)
    {v : Lp ℂ 2 (volume : Measure ℝ^(n + 1))} (hv : IsHermitianL2 v) :
    IsHermitianL2 (frequencyRestriction n hs (splitFrequencyLI n v)) := by
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
  filter_upwards [coeFn_reflL2 (star (frequencyRestriction n hs A)),
    ae_neg (Lp.coeFn_star (frequencyRestriction n hs A)),
    ae_neg (frequencyRestriction_apply_ae hs A), frequencyRestriction_apply_ae hs A,
    Measure.ae_ae_of_ae_prod hA] with ξ h1 h2 h3 h4 h5
  rw [h1, h2]
  change conj (frequencyRestriction n hs A (-ξ)) = frequencyRestriction n hs A ξ
  rw [h3, h4]
  change conj (∫ t, frequencyKernel s (-ξ) t • A (-ξ, t)) =
    ∫ t, frequencyKernel s ξ t • A (ξ, t)
  rw [← integral_conj, ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [h5] with t ht
  simp only [frequencyKernel_neg, Complex.real_smul, map_mul, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ ↦ (frequencyKernel s ξ t : ℂ) * z) ht

theorem besselLiftLI_mem_real (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n; ℝ)) :
    besselLiftLI n hs v ∈ hsRealSubmodule (n + 1) s := by
  rw [mem_HsRealSubmodule_iff, isRealL2_iff_isHermitian_fourier, fourier_toLp_besselLiftLI]
  apply frequencyLiftEuclideanLI_isHermitian
  exact (isRealL2_iff_isHermitian_fourier _).1 (mem_HsRealSubmodule_iff.1 v.property)

theorem besselRestrictionCLM_mem_real (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1); ℝ)) :
    besselRestrictionCLM n hs u ∈ hsRealSubmodule n (s - 1 / 2) := by
  rw [mem_HsRealSubmodule_iff, isRealL2_iff_isHermitian_fourier,
    fourier_toLp_besselRestrictionCLM]
  apply frequencyRestriction_splitFrequency_isHermitian
  exact (isRealL2_iff_isHermitian_fourier _).1 (mem_HsRealSubmodule_iff.1 u.property)

theorem wholeSpaceTraceCLM_mem_real (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1); ℝ)) :
    wholeSpaceTraceCLM n hs u ∈ hsRealSubmodule n (s - 1 / 2) := by
  change traceConstant s • besselRestrictionCLM n hs u ∈ _
  exact (hsRealSubmodule n (s - 1 / 2)).smul_mem _ (besselRestrictionCLM_mem_real n hs u)

theorem wholeSpaceLiftingCLM_mem_real (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n; ℝ)) :
    wholeSpaceLiftingCLM n hs v ∈ hsRealSubmodule (n + 1) s := by
  change (traceConstant s : ℂ)⁻¹ • besselLiftLI n hs v ∈ _
  rw [← Complex.ofReal_inv]
  exact (hsRealSubmodule (n + 1) s).smul_mem _ (besselLiftLI_mem_real n hs v)

/-- The bounded trace on the real Sobolev spaces, for every `s > 1/2`. -/
def wholeSpaceTraceRealCLM (n : ℕ) (hs : 1 / 2 < s) :
    H^{s}(ℝ^(n + 1); ℝ) →L[ℝ] H^{s - 1 / 2}(ℝ^n; ℝ) :=
  (((wholeSpaceTraceCLM n hs).restrictScalars ℝ).comp
    (hsRealSubmodule (n + 1) s).subtypeL).codRestrict
      (hsRealSubmodule n (s - 1 / 2)) (wholeSpaceTraceCLM_mem_real n hs)

/-- The explicitly constructed bounded real right inverse. -/
def wholeSpaceLiftingRealCLM (n : ℕ) (hs : 1 / 2 < s) :
    H^{s - 1 / 2}(ℝ^n; ℝ) →L[ℝ] H^{s}(ℝ^(n + 1); ℝ) :=
  (((wholeSpaceLiftingCLM n hs).restrictScalars ℝ).comp
    (hsRealSubmodule n (s - 1 / 2)).subtypeL).codRestrict
      (hsRealSubmodule (n + 1) s) (wholeSpaceLiftingCLM_mem_real n hs)

theorem norm_wholeSpaceTraceRealCLM_apply_le (n : ℕ) (hs : 1 / 2 < s)
    (u : H^{s}(ℝ^(n + 1); ℝ)) :
    ‖wholeSpaceTraceRealCLM n hs u‖ ≤ traceConstant s * ‖u‖ :=
  norm_wholeSpaceTraceCLM_apply_le n hs u.val

theorem norm_wholeSpaceLiftingRealCLM (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n; ℝ)) :
    ‖wholeSpaceLiftingRealCLM n hs v‖ = (traceConstant s)⁻¹ * ‖v‖ :=
  norm_wholeSpaceLiftingCLM n hs v.val

theorem wholeSpaceTraceRealCLM_wholeSpaceLiftingRealCLM (n : ℕ) (hs : 1 / 2 < s)
    (v : H^{s - 1 / 2}(ℝ^n; ℝ)) :
    wholeSpaceTraceRealCLM n hs (wholeSpaceLiftingRealCLM n hs v) = v := by
  apply Subtype.ext
  exact wholeSpaceTraceCLM_wholeSpaceLiftingCLM n hs v.val

theorem wholeSpaceTraceRealCLM_surjective (n : ℕ) (hs : 1 / 2 < s) :
    Function.Surjective (wholeSpaceTraceRealCLM n hs) :=
  fun v ↦ ⟨wholeSpaceLiftingRealCLM n hs v,
    wholeSpaceTraceRealCLM_wholeSpaceLiftingRealCLM n hs v⟩

end SobolevSpace.Fractional.Trace.GeneralOrder
