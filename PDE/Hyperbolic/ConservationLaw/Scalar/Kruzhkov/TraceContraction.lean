/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Uniqueness

/-!
# Contraction at prescribed strong left traces

At a specified positive time, a strong local `L¹` left trace determines the value of
the entropy distance. We reduce this to the initial-trace statement
by reflecting time about the endpoint. The cone comparison therefore applies to
such traces at every prescribed time, including times exceptional for arbitrary
spacetime representatives.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

namespace Kruzhkov

/-- Reflecting time turns an inward cone into an outward cone with shifted endpoints. -/
theorem coneWeight_time_reflection (c a b δ T s x : ℝ) :
    coneWeight (-c) (a + c * T) (b - c * T) δ !₂[s, x] = coneWeight c a b δ !₂[T - s, x] := by
  unfold coneWeight
  congr 1 <;> congr 1 <;> dsimp <;> ring

/-- A strong local left trace determines every smooth cone pairing at its endpoint. -/
theorem coneIntegral_left_trace {u : ℝ^2 → ℝ} {uT : ℝ → ℝ} {T : ℝ}
    (huT : HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ u !₂[T - p 0, p 1]) uT)
    (c a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, coneWeight c a b δ !₂[t, x] * u !₂[t, x])
      (𝓝[<] T) (𝓝 (∫ x : ℝ, coneWeight c a b δ !₂[T, x] * uT x)) := by
  let τ := finalTimeCutoff 3 1
  let φ := coneTest (-c) (a + c * T) (b - c * T) hδ τ
    (contDiff_finalTimeCutoff 3 1) (hasCompactSupport_finalTimeCutoff 3 zero_lt_one)
  have hτ (s : ℝ) (hs : s ∈ Ico 0 1) : τ s = 1 := by
    dsimp [τ]
    rw [finalTimeCutoff_eq hs.1, initialTimeCutoff_one zero_lt_one (by linarith [hs.2])]
  have hφ (s x : ℝ) : φ !₂[s, x] =
      τ s * coneWeight c a b δ !₂[T - s, x] := by
    change τ s * coneWeight (-c) (a + c * T) (b - c * T) δ !₂[s, x] = _
    rw [coneWeight_time_reflection]
  have h := huT.tendsto_integral_test_smul φ
  change Tendsto (fun s : ℝ ↦ ∫ x : ℝ, φ !₂[s, x] * u !₂[T - s, x])
    (𝓝[>] 0) (𝓝 (∫ x : ℝ, φ !₂[0, x] * uT x)) at h
  have hzero : (∫ x : ℝ, φ !₂[0, x] * uT x) =
      ∫ x : ℝ, coneWeight c a b δ !₂[T, x] * uT x := by
    simp_rw [hφ, hτ 0 (by norm_num), one_mul, sub_zero]
  rw [hzero] at h
  have hnear : Tendsto (fun s : ℝ ↦ ∫ x : ℝ, coneWeight c a b δ !₂[T - s, x] * u !₂[T - s, x])
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, coneWeight c a b δ !₂[T, x] * uT x)) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with s hs hs'
    change (∫ x : ℝ, φ !₂[s, x] * u !₂[T - s, x]) = _
    simp_rw [hφ, hτ s ⟨hs.le, hs'⟩, one_mul]
  have hreflect : Tendsto (fun t : ℝ ↦ T - t) (𝓝[<] T) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq, sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ T) (𝓝[<] T) (𝓝 T)).sub
        ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 T) (𝓝 T)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr ht
  simpa only [Function.comp_def, sub_sub_cancel] using hnear.comp hreflect

/-- Local comparison holds at every prescribed positive-time strong left trace. -/
theorem local_comparison_of_left_trace {u q : ℝ^2 → ℝ} {u₀ uT : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) → 0 ≤ ∫ p,
      InteriorWeakForm.integrand u q φ p)
    {c : ℝ} (hflux : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |q p| ≤ c * u p) {T : ℝ} (hT : 0 < T)
    (huT : HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ u !₂[T - p 0, p 1]) uT) (a b : ℝ) :
    (∫ x : ℝ in Icc (a + c * T) (b - c * T), uT x) ≤ ∫ x : ℝ in Icc a b, u₀ x := by
  let δ : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft := tendsto_integral_coneWeight c a b T
    (huT.initial_locallyIntegrable.integrableOn_isCompact isCompact_Icc) hδ hlim
  have hright := tendsto_integral_coneWeight c a b 0
    (htrace.initial_locallyIntegrable.integrableOn_isCompact isCompact_Icc) hδ hlim
  simp only [mul_zero, add_zero, sub_zero] at hright
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards with n
  exact coneIntegral_le_of_left_trace hu hq htrace hineq hflux a b (hδ n) hT
    (coneIntegral_left_trace huT c a b (hδ n))

end Kruzhkov

open Kruzhkov

/-- Finite-speed local contraction at a prescribed strong local `L¹` left trace.
Applying this to the solutions' time slices requires those slices to be the strong traces. -/
theorem IsEntropySolutionWithInitialTrace.local_l1_contraction_of_left_trace {flux : ℝ → ℝ}
    {u v : ℝ^2 → ℝ} {u₀ v₀ uT vT : ℝ → ℝ} (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux v₀ v) (hf : ContDiff ℝ 1 flux) {M c : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M)
    (hc : ∀ r ∈ Icc (-M) M, ‖deriv flux r‖ ≤ c) {T : ℝ} (hT : 0 < T)
    (huT : HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ u !₂[T - p 0, p 1]) uT)
    (hvT : HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ v !₂[T - p 0, p 1]) vT) (a b : ℝ) :
    (∫ x : ℝ in Icc a b, |uT x - vT x|) ≤
      ∫ x : ℝ in Icc (a - c * T) (b + c * T), |u₀ x - v₀ x| := by
  have hui := locallyIntegrable_of_ae_bound
    hu.interior.weak.u_locallyIntegrable.aestronglyMeasurable hbu
  have hvi := locallyIntegrable_of_ae_bound
    hv.interior.weak.u_locallyIntegrable.aestronglyMeasurable hbv
  have hflux := ae_entropyFlux_bound hf hbu hbv hc
  simpa only [sub_add_cancel, add_sub_cancel_right] using
    local_comparison_of_left_trace (locallyIntegrable_entropyDistance hui hvi)
    (locallyIntegrable_entropyFlux hf.continuous.measurable hui hvi hflux)
    (entropyDistance_initialTrace hu.initialTrace hv.initialTrace)
    (comparison_inequality hu.interior hv.interior hf hbu hbv) hflux hT
    (entropyDistance_initialTrace huT hvT) (a - c * T) (b + c * T)

/-- For identical initial data, prescribed strong left traces agree at every positive time. -/
theorem IsEntropySolutionWithInitialTrace.unique_left_trace {flux : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    {u₀ uT vT : ℝ → ℝ} (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux u₀ v) (hf : ContDiff ℝ 1 flux) {M : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) {T : ℝ} (hT : 0 < T)
    (huT : HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ u !₂[T - p 0, p 1]) uT)
    (hvT : HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ v !₂[T - p 0, p 1]) vT) :
    uT =ᵐ[volume] vT := by
  obtain ⟨c, hc⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := deriv flux) (s := Icc (-M) M) hf.continuous_deriv_one.continuousOn
  have hN (N : ℕ) : ∀ᵐ x : ℝ, x ∈ Icc (-(N : ℝ)) N → uT x = vT x := by
    have h := hu.local_l1_contraction_of_left_trace hv hf hbu hbv hc hT huT hvT (-(N : ℝ)) N
    have hz : (∫ x : ℝ in Icc (-(N : ℝ)) N, |uT x - vT x|) = 0 :=
      le_antisymm (by simpa using h) (integral_nonneg (fun _ ↦ abs_nonneg _))
    have hi := ((huT.initial_locallyIntegrable.integrableOn_isCompact
      (isCompact_Icc (a := -(N : ℝ)) (b := N))).sub
        (hvT.initial_locallyIntegrable.integrableOn_isCompact isCompact_Icc)).norm
    apply (ae_restrict_iff' measurableSet_Icc).1
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ abs_nonneg _) hi).1 hz] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)
  filter_upwards [ae_all_iff.mpr hN] with x hx
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  exact hx N (by simpa only [mem_Icc, ← abs_le] using hN.le)

/-- Representatives which attain their strong local left traces agree in space almost
everywhere at every positive time. No such claim is made for arbitrary representatives. -/
theorem IsEntropySolutionWithInitialTrace.unique_at_all_positive_times {flux : ℝ → ℝ}
    {u v : ℝ^2 → ℝ} {u₀ : ℝ → ℝ} (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux u₀ v) (hf : ContDiff ℝ 1 flux) {M : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M)
    (huT : ∀ T : ℝ, 0 < T →
      HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ u !₂[T - p 0, p 1]) (fun x : ℝ ↦ u !₂[T, x]))
    (hvT : ∀ T : ℝ, 0 < T →
      HasInitialTraceLocallyL1 (fun p : ℝ^2 ↦ v !₂[T - p 0, p 1]) (fun x : ℝ ↦ v !₂[T, x])) :
    ∀ T : ℝ, 0 < T → (fun x : ℝ ↦ u !₂[T, x]) =ᵐ[volume] (fun x : ℝ ↦ v !₂[T, x]) :=
  fun T hT ↦ hu.unique_left_trace hv hf hbu hbv hT (huT T hT) (hvT T hT)

end PDE.Hyperbolic.ConservationLaw.Scalar
