/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.ConeTest
public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.TimeLocalization

/-!
# Comparison on smooth backward cones

The initial-boundary Kato inequality bounds terminal time averages of the entropy
distance on a shrinking interval.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- A compact time weight makes the cone-weighted density integrable up to time zero. -/
theorem integrableOn_time_cone_mul {u : ℝ^2 → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace)) (c a b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {τ : ℝ → ℝ} (hτ : Continuous τ) (hcτ : HasCompactSupport τ) :
    IntegrableOn (fun p : ℝ^2 ↦ τ (p 0) * (coneWeight c a b δ p * u p)) forwardHalfSpace := by
  simpa only [IntegrableOn, smul_eq_mul, Function.comp_def, Pi.mul_apply,
    EuclideanSpace.coe_proj, mul_assoc] using hu.integrable_smul_left_of_hasCompactSupport
      ((hτ.comp (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).continuous).mul
        (contDiff_coneWeight c a b δ).continuous) (hasCompactSupport_time_mul_coneWeight hcτ hδ)

/-- The cone-weighted spatial integral is integrable on every finite positive time interval. -/
theorem integrableOn_coneIntegral {u : ℝ^2 → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (c a b : ℝ) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]) (Ioo 0 T) := by
  let τ := finalTimeCutoff (T + 3) 1
  have hi := integrableOn_sliceIntegral (integrableOn_time_cone_mul hu c a b hδ
    (contDiff_finalTimeCutoff (T + 3) 1).continuous
    (hasCompactSupport_finalTimeCutoff (T + 3) zero_lt_one))
  apply (hi.mono_set Ioo_subset_Ioi_self).congr_fun _ measurableSet_Ioo
  intro t ht
  have hτ : τ t = 1 := by
    dsimp [τ]
    rw [finalTimeCutoff_eq ht.1.le, initialTimeCutoff_one zero_lt_one (by linarith [ht.2])]
  change (∫ x : ℝ, τ t * (coneWeight c a b δ !₂[t, x] * u !₂[t, x])) = _
  simp only [hτ, one_mul]

/-- A nonnegative time weight leaves only its time derivative in the cone comparison. -/
theorem cone_time_inequality {u q : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) →
      0 ≤ ∫ p, InteriorWeakForm.integrand u q φ p)
    {c : ℝ} (hflux : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |q p| ≤ c * u p)
    (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) (τ : ℝ → ℝ)
    (hτ : ContDiff ℝ 1 τ) (hcτ : HasCompactSupport τ) (hτ0 : ∀ t, 0 ≤ τ t) :
    0 ≤ (∫ p : ℝ^2 in forwardHalfSpace, deriv τ (p 0) * (coneWeight c a b δ p * u p)) + τ 0 * ∫ x :
      ℝ, coneWeight c a b δ !₂[0, x] * u₀ x := by
  have h := initial_boundary_inequality hu hq htrace hineq
    (coneTest c a b hδ τ hτ hcτ) (fun p ↦ mul_nonneg (hτ0 _) (coneWeight_nonneg _ _ _ _ _))
  have hi := integrableOn_time_cone_mul hu c a b hδ (hτ.continuous_deriv le_rfl) hcτ.deriv
  have hle : (∫ p : ℝ^2 in forwardHalfSpace,
      InteriorWeakForm.integrand u q (coneTest c a b hδ τ hτ hcτ) p) ≤
      ∫ p : ℝ^2 in forwardHalfSpace, deriv τ (p 0) * (coneWeight c a b δ p * u p) := by
    apply integral_mono_ae (integrableOn_initialWeakIntegrand hu hq _) hi
    filter_upwards [hflux] with p hp
    exact integrand_coneTest_le u q c a b hδ τ hτ hcτ p (hτ0 _) hp
  have hzero : (∫ x : ℝ, coneTest c a b hδ τ hτ hcτ !₂[0, x] * u₀ x) =
      τ 0 * ∫ x : ℝ, coneWeight c a b δ !₂[0, x] * u₀ x := by
    change (∫ x : ℝ, τ 0 * coneWeight c a b δ !₂[0, x] * u₀ x) = _
    simp only [mul_assoc, integral_const_mul]
  rw [hzero] at h
  linarith

/-- The terminal kernel average of the cone-weighted density is bounded by its initial value. -/
theorem terminal_cone_inequality {u q : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) →
      0 ≤ ∫ p, InteriorWeakForm.integrand u q φ p)
    {c : ℝ} (hflux : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |q p| ≤ c * u p)
    (a b : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (T : ℝ) :
    (∫ t : ℝ in Ioo 0 T, deriv (initialTimeCutoff ε) (T - t) *
      ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]) ≤
        initialTimeCutoff ε T * ∫ x : ℝ, coneWeight c a b δ !₂[0, x] * u₀ x := by
  let τ := finalTimeCutoff T ε
  have ht := contDiff_finalTimeCutoff T ε
  have hc := hasCompactSupport_finalTimeCutoff T hε
  have h := cone_time_inequality hu hq htrace hineq hflux a b hδ τ ht hc
    (finalTimeCutoff_nonneg T ε)
  have hi := integrableOn_time_cone_mul hu c a b hδ (ht.continuous_deriv le_rfl) hc.deriv
  rw [integral_forwardHalfSpace_eq hi] at h
  change 0 ≤ (∫ t : ℝ in Ioi 0, ∫ x : ℝ, deriv τ t * (coneWeight c a b δ !₂[t, x] * u !₂[t, x])) +
      τ 0 * ∫ x : ℝ, coneWeight c a b δ !₂[0, x] * u₀ x at h
  have hs : (fun t : ℝ ↦ ∫ x : ℝ, deriv τ t * (coneWeight c a b δ !₂[t, x] * u !₂[t, x])) =
      fun t : ℝ ↦ deriv τ t * ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x] :=
    funext (fun t ↦ integral_const_mul _ _)
  rw [hs] at h
  have heq' : (∫ t : ℝ in Ioi 0, deriv τ t * ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]) =
      ∫ t : ℝ in Ioi 0, -(deriv (initialTimeCutoff ε) (T - t) *
        ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [τ]
    rw [deriv_finalTimeCutoff ht.le T ε, neg_mul]
  have heq : (∫ t : ℝ in Ioi 0, deriv τ t * ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]) =
      -(∫ t : ℝ in Ioo 0 T, deriv (initialTimeCutoff ε) (T - t) *
        ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]) := by
    rw [heq', ← integral_neg]
    apply (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioi Ioo_subset_Ioi_self ?_)
    intro t ht
    have htT : T ≤ t := by
      exact le_of_not_gt (fun h ↦ ht.2 ⟨ht.1, h⟩)
    rw [deriv_initialTimeCutoff_eq_zero hε (by
      intro hm
      linarith [hm.1]), zero_mul, neg_zero]
  rw [heq] at h
  dsimp only [τ] at h
  rw [finalTimeCutoff_eq le_rfl, sub_zero] at h
  linarith

/-- Cone-weighted comparison holds for almost every positive time. -/
theorem ae_coneIntegral_le {u q : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) →
      0 ≤ ∫ p, InteriorWeakForm.integrand u q φ p)
    {c : ℝ} (hflux : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |q p| ≤ c * u p)
    (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ T : ℝ, 0 < T → (∫ x : ℝ, coneWeight c a b δ !₂[T, x] * u !₂[T, x]) ≤ ∫ x : ℝ,
      coneWeight c a b δ !₂[0, x] * u₀ x := by
  let F := fun t : ℝ ↦ ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x]
  have hN (N : ℕ) : ∀ᵐ T : ℝ, T ∈ Ioo 0 (N : ℝ) →
      F T ≤ ∫ x : ℝ, coneWeight c a b δ !₂[0, x] * u₀ x := by
    let G := (Ioo 0 (N : ℝ)).indicator F
    have hG : Integrable G := (integrableOn_coneIntegral hu c a b hδ N).integrable_indicator
      measurableSet_Ioo
    filter_upwards [ae_tendsto_integral_terminal_kernel hG.locallyIntegrable] with T hT hTN
    have heq : G T = F T := indicator_of_mem hTN F
    have hlim := hT hTN.1
    rw [heq] at hlim
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (half_pos hTN.1))] with ε hε hε'
    have h := terminal_cone_inequality hu hq htrace hineq hflux a b hδ hε T
    rw [initialTimeCutoff_one hε (by
      have he : ε < T / 2 := hε'
      linarith), one_mul] at h
    convert h using 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have htN : t ∈ Ioo 0 (N : ℝ) := ⟨ht.1, ht.2.trans hTN.2⟩
    change deriv (initialTimeCutoff ε) (T - t) * G t = deriv (initialTimeCutoff ε) (T - t) * F t
    rw [show G t = F t from indicator_of_mem htN F]
  filter_upwards [ae_all_iff.mpr hN] with T hT hpos
  obtain ⟨N, hN⟩ := exists_nat_gt T
  exact hT N ⟨hpos, hN⟩

/-- If a specified cone integral has a strong left limit, the comparison holds at that limit. -/
theorem coneIntegral_le_of_left_trace {u q : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) →
      0 ≤ ∫ p, InteriorWeakForm.integrand u q φ p)
    {c : ℝ} (hflux : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |q p| ≤ c * u p)
    (a b : ℝ) {δ T A : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hlim : Tendsto (fun t : ℝ ↦ ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x])
      (𝓝[<] T) (𝓝 A)) :
    A ≤ ∫ x : ℝ, coneWeight c a b δ !₂[0, x] * u₀ x := by
  apply le_of_tendsto (tendsto_integral_terminal_kernel hT
    (integrableOn_coneIntegral hu c a b hδ T) hlim)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (half_pos hT))] with ε hε hε'
  have h := terminal_cone_inequality hu hq htrace hineq hflux a b hδ hε T
  rwa [initialTimeCutoff_one hε (by
    have he : ε < T / 2 := hε'
    linarith), one_mul] at h

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
