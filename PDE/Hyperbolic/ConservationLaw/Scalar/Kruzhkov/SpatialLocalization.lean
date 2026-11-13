/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.ConeComparison

/-!
# Localization to shrinking spatial intervals

Fubini gives integrable spatial slices at almost every positive time. Dominated
convergence removes the two spatial transition layers, yielding local comparison
on the interval bounded by the inward characteristic cones.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- An integrable spacetime function has integrable spatial slices almost everywhere. -/
theorem ae_integrable_slice {f : ℝ^2 → ℝ} (hf : IntegrableOn f forwardHalfSpace) :
    ∀ᵐ t : ℝ, 0 < t → Integrable (fun x : ℝ ↦ f !₂[t, x]) := by
  have hp := (measurePreserving_spaceTimePair.integrableOn_comp_preimage
    spaceTimePair.measurableEmbedding).2 hf
  rw [preimage_forwardHalfSpace] at hp
  simp only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.volume_eq_prod] at hp
  exact (ae_restrict_iff' measurableSet_Ioi).1
    (by simpa [Function.comp_def, spaceTimePair_apply] using hp.prod_right_ae)

/-- Local spacetime integrability gives locally integrable spatial slices almost everywhere. -/
theorem ae_locallyIntegrable_slice {u : ℝ^2 → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace)) :
    ∀ᵐ t : ℝ, 0 < t → LocallyIntegrable (fun x : ℝ ↦ u !₂[t, x]) volume := by
  have hN (N : ℕ) : ∀ᵐ t : ℝ, t ∈ Ioo 0 (N : ℝ) →
      IntegrableOn (fun x : ℝ ↦ u !₂[t, x]) (Icc (-(N : ℝ)) N) := by
    let τ := finalTimeCutoff ((N : ℝ) + 3) 1
    have hi := integrableOn_time_cone_mul hu 0 (-(N : ℝ) - 1) (N + 1) zero_lt_one
      (contDiff_finalTimeCutoff ((N : ℝ) + 3) 1).continuous
      (hasCompactSupport_finalTimeCutoff ((N : ℝ) + 3) zero_lt_one)
    filter_upwards [ae_integrable_slice hi] with t ht htN
    apply (ht htN.1).integrableOn.congr_fun _ measurableSet_Icc
    intro x hx
    have hτ : τ t = 1 := by
      dsimp [τ]
      rw [finalTimeCutoff_eq htN.1.le, initialTimeCutoff_one zero_lt_one (by linarith [htN.2])]
    have hW : coneWeight 0 (-(N : ℝ) - 1) (N + 1) 1 !₂[t, x] = 1 := by
      apply coneWeight_one zero_lt_one
      simpa using hx
    change τ t * (coneWeight 0 (-(N : ℝ) - 1) (N + 1) 1 !₂[t, x] * u !₂[t, x]) = _
    rw [hτ, hW, one_mul, one_mul]
  filter_upwards [ae_all_iff.mpr hN] with t ht hpos
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (max t R)
  apply (ht N ⟨hpos, (le_max_left _ _).trans_lt hN⟩).mono_set
  intro x hx
  have h := (hR x hx).trans ((le_max_right _ _).trans hN.le)
  simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using h

/-- Removing the spatial transition layers recovers the integral on the shrinking interval. -/
theorem tendsto_integral_coneWeight {f : ℝ → ℝ} (c a b T : ℝ)
    (hf : IntegrableOn f (Icc (a + c * T) (b - c * T)))
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x : ℝ, coneWeight c a b (δ n) !₂[T, x] * f x) atTop
      (𝓝 (∫ x : ℝ in Icc (a + c * T) (b - c * T), f x)) := by
  have heq (n : ℕ) : (∫ x : ℝ, coneWeight c a b (δ n) !₂[T, x] * f x) =
      ∫ x : ℝ in Icc (a + c * T) (b - c * T),
        coneWeight c a b (δ n) !₂[T, x] * f x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [coneWeight_zero (hδ n) _ (by simpa using hx), zero_mul]
  simp_rw [heq]
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
  · intro n
    exact (((contDiff_coneWeight c a b (δ n)).continuous.comp
      (by fun_prop : Continuous (fun x : ℝ ↦ !₂[T, x]))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable)
  · exact hf.norm
  · intro n
    filter_upwards with x
    rw [norm_mul, Real.norm_of_nonneg (coneWeight_nonneg _ _ _ _ _)]
    exact (mul_le_mul_of_nonneg_right (coneWeight_le_one _ _ _ _ _)
      (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (a + c * T)), ae_restrict_of_ae (volume.ae_ne (b - c * T))]
      with x hx hl hr
    have hl' : 0 < x - (a + c * T) := sub_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm hl))
    have hr' : 0 < b - c * T - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hr)
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim.eventually (Iio_mem_nhds hl'),
      hlim.eventually (Iio_mem_nhds hr')] with n hn hn'
    rw [coneWeight_one (hδ n) _ (by
      constructor <;> dsimp <;> linarith), one_mul]

/-- The initial-boundary distributional inequality implies local contraction
on every shrinking interval for almost every positive time. -/
theorem ae_local_comparison {u q : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) → 0 ≤ ∫ p,
      InteriorWeakForm.integrand u q φ p)
    {c : ℝ} (hflux : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |q p| ≤ c * u p) (a b : ℝ) :
    ∀ᵐ T : ℝ, 0 < T → (∫ x : ℝ in Icc (a + c * T) (b - c * T), u !₂[T, x]) ≤ ∫ x : ℝ in Icc a b,
      u₀ x := by
  let δ : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hN := ae_all_iff.mpr (fun n ↦ ae_coneIntegral_le hu hq htrace hineq hflux a b (hδ n))
  filter_upwards [hN, ae_locallyIntegrable_slice hu] with T hT hi hpos
  have hleft := tendsto_integral_coneWeight c a b T
    ((hi hpos).integrableOn_isCompact isCompact_Icc) hδ hlim
  have hright := tendsto_integral_coneWeight c a b 0
    (htrace.initial_locallyIntegrable.integrableOn_isCompact isCompact_Icc) hδ hlim
  simp only [mul_zero, add_zero, sub_zero] at hright
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun n ↦ hT n hpos))

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
