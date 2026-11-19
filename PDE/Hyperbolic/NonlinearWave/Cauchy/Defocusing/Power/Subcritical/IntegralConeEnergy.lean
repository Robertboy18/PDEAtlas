/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ConeEnergy
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralEnergyBounds
public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralRegularization
public import PDE.Hyperbolic.NonlinearWave.Regularization.ConeEnergy
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import CAS.ExactTactic

/-!
# Cone energy bounds for the C¹ integral lifespan

The spatially tested equation and common compact support supply the finite-cone identity for the
field. Nonnegative cap energy and conserved whole-space energy bound each strict truncated flux.
Integrable annular exhaustion passes this bound to the full retarded graph, including both endpoint
limits.

The resulting H¹ trace has a gradient bound from initial energy and a scaled L² bound from energy
and initial displacement. The integral lifespan and its Cauchy data give all the hypotheses. There
is no pointwise C² assumption. The cone identity is the flux identity (3) of Evans, §12.1.2, and the
two trace bounds are the conclusions of (22)-(24) in the proof of Theorem 3 of §12.3.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i), equation (3); §12.3.3, proof
  of Theorem 3, equations (22)-(24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Every strict finite cone in the compact-data integral lifespan
obeys the original-field energy identity. -/
theorem IsIntegralTrajectoryBefore.ballIntegral_energy_add_truncatedCone_flux {r b L T s τ : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hTL : T < L) (hs : 0 < s)
    (hsτ : s ≤ τ) (hτT : τ < T) (c : ℝ^3) :
    let U : ℝ^4 → ℝ := fun p ↦ u (timeSpaceContinuousLinearEquiv 3 p)
    ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential r) U (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation (Real.signedPowerPotential r) U c p
          ∂Measure.euclideanHausdorffMeasure 3) =
      ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
        (Real.signedPowerPotential r) U (timeSpaceCons s x)) c (T - s) := by
  obtain ⟨K, hK, hsupp⟩ := hu.exists_compact_support_pos_strip hr hb
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs hTL
  apply ballIntegral_energy_add_truncatedCone_flux_of_tested_wave
    hK (hu.contDiffOn_pos_strip hb hTL) hsupp (Real.contDiff_one_signedPowerPotential hr)
    (by rw [(Real.hasDerivAt_signedPowerPotential hr 0).deriv, Real.signedPower_zero])
    (fun t ht ψ hψ hψs ↦ ?_) c hs hsτ hτT hτT
  simpa only [(Real.hasDerivAt_signedPowerPotential hr _).deriv] using
    hu.tested_equation hr hb hg hh hψ hψs ⟨ht.1, ht.2.trans hTL⟩

/-- Bounds on inner truncated annuli pass to the full ball for an integrable
function. The omitted center is a null set. -/
private theorem integral_ball_le_of_annuli {f : ℝ^3 → ℝ} (c : ℝ^3) {T E : ℝ} (hT : 0 < T)
    (hi : IntegrableOn f (ball c T))
    (hb : ∀ δ : ℝ, 0 < δ → δ ≤ T / 2 → (∫ x in ball c (T - δ) \ ball c δ, f x) ≤ E) :
    (∫ x in ball c T, f x) ≤ E := by
  let δ (n : ℕ) : ℝ := (T / 2) * (1 / 2 : ℝ) ^ n
  have hδpos (n : ℕ) : 0 < δ n := mul_pos (half_pos hT) (pow_pos (by norm_num) n)
  have hδanti : Antitone δ := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num) hij) (half_pos hT).le
  have hδle (n : ℕ) : δ n ≤ T / 2 := by
    simpa only [δ, pow_zero, mul_one] using hδanti (Nat.zero_le n)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num)).const_mul (T / 2)
  let A (n : ℕ) := ball c (T - δ n) \ ball c (δ n)
  have hmono : Monotone A := by
    intro i j hij
    exact sdiff_subset_sdiff (ball_subset_ball (sub_le_sub_left (hδanti hij) T))
      (ball_subset_ball (hδanti hij))
  have hcover : (⋃ n, A n) = ball c T \ {c} := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      refine ⟨ball_subset_ball (sub_le_self T (hδpos n).le) hn.1, ?_⟩
      intro hxc
      have hxc' : x = c := mem_singleton_iff.mp hxc
      exact hn.2 (hxc' ▸ mem_ball_self (hδpos n))
    · rintro ⟨hx, hxc⟩
      have hxT : dist x c < T := hx
      have hxc' : x ≠ c := fun h ↦ hxc (mem_singleton_iff.mpr h)
      obtain ⟨n, hnT, hn0⟩ := ((hδlim.eventually_lt_const (sub_pos.mpr hxT)).and
          (hδlim.eventually_lt_const (dist_pos.mpr hxc'))).exists
      refine mem_iUnion.mpr ⟨n, ?_, ?_⟩
      · change dist x c < T - δ n
        linarith
      · change ¬dist x c < δ n
        exact not_lt.mpr hn0.le
  have hlim := tendsto_setIntegral_of_monotone
    (fun n ↦ measurableSet_ball.diff measurableSet_ball) hmono
    (hi.mono_set (by rw [hcover]; exact sdiff_subset))
  have heq : (∫ x in ⋃ n, A n, f x) = ∫ x in ball c T, f x := by
    rw [hcover]
    exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton c))
  rw [heq] at hlim
  exact le_of_tendsto' hlim (fun n ↦ hb (δ n) (hδpos n) (hδle n))

/-- First-order regularity makes the null flux continuous before substituting
its unit normal. -/
private theorem continuous_nullFlux_of_contDiff_one {V : ℝ → ℝ} {u : ℝ^4 → ℝ} (hV : Continuous V)
    (hu : ContDiff ℝ 1 u) :
    Continuous (Function.uncurry (semilinearWaveNullFlux V u)) := by
  have ht := hu.continuous_partialDeriv 0
  have hg := (contDiff_classicalWaveSpatialGradient (m := 0) hu).continuous
  exact (continuous_const.mul ((((ht.comp continuous_fst).smul continuous_snd).sub
    (hg.comp continuous_fst)).norm.pow 2)).add (hV.comp (hu.continuous.comp continuous_fst))

/-- Uniform bounds on strict truncated cones control the full H¹ retarded
trace gradient. Integrability comes from the C¹ trace and the bounded normal. -/
private theorem norm_gradient_retardedTrace_sq_le_of_truncated_flux {V : ℝ → ℝ} {u : ℝ^4 → ℝ}
    (hV : Continuous V) (hV0 : ∀ z, 0 ≤ V z) (hu : ContDiff ℝ 1 u) (c : ℝ^3) {T E : ℝ} (hT : 0 < T)
    (hflux : ∀ s τ : ℝ, 0 < s → s ≤ τ → τ < T → (1 / Real.sqrt 2) *
      (∫ p in truncatedConeLateralSurface c T s τ, semilinearWaveConeDissipation V u c p
      ∂Measure.euclideanHausdorffMeasure 3) ≤ E)
    (U : H¹(ball c T))
    (hgrad : (∇ U : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 (ball c T)] retardedGradient u c T) :
    ‖∇ U‖ ^ 2 ≤ 2 * E := by
  have hH := continuous_nullFlux_of_contDiff_one hV hu
  have hm : Measurable (semilinearWaveConeDissipation V u c) := measurable_coneNormalTrace hH c
  have hD : IntegrableOn
      (fun x ↦ semilinearWaveConeDissipation V u c (backwardConeGraph c T x)) (ball c T) :=
    integrableOn_coneNormalTrace_graph hH c T T
  have hb : (∫ x in ball c T,
      semilinearWaveConeDissipation V u c (backwardConeGraph c T x)) ≤ E := by
    apply integral_ball_le_of_annuli c hT hD
    intro δ hδ hδT
    have h := hflux δ (T - δ) hδ (by linarith) (by linarith)
    rw [integral_truncatedConeLateralSurface c (by linarith : T - δ ≤ T) _ hm,
      sub_sub_cancel, ← mul_assoc] at h
    have hscale : (1 / Real.sqrt 2) * Real.sqrt 2 = 1 := by cas
    simpa only [hscale, one_mul] using h
  have hG : Integrable (fun x ↦ ‖∇ U x‖ ^ 2) (domainMeasure 3 (ball c T)) :=
    (Lp.memLp (∇ U)).norm.integrable_sq
  have hle : (1 / 2 : ℝ) * ‖∇ U‖ ^ 2 ≤
      ∫ x in ball c T, semilinearWaveConeDissipation V u c (backwardConeGraph c T x) := by
    rw [Lp.norm_sq_eq_integral_norm_sq, ← integral_const_mul]
    apply integral_mono_ae (hG.const_mul _) hD
    filter_upwards [hgrad] with x hx
    rw [hx, coneDissipation_eq_retardedGradient]
    exact le_add_of_nonneg_right (hV0 _)
  linarith

/-- The signed-power lifespan bounds every strict truncated flux by
its conserved whole-space initial energy. -/
theorem IsIntegralTrajectoryBefore.truncatedCone_flux_le_initial_energy {r b L R T s τ : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) (hTL : T < L) (hs : 0 < s)
    (hsτ : s ≤ τ) (hτT : τ < T) (c : ℝ^3) :
    let U : ℝ^4 → ℝ := fun p ↦ u (timeSpaceContinuousLinearEquiv 3 p)
    (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
      semilinearWaveConeDissipation (Real.signedPowerPotential r) U c p
        ∂Measure.euclideanHausdorffMeasure 3) ≤
      semilinearWaveSpatialEnergy (Real.signedPowerPotential r) U 0 := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  have hgs : HasCompactSupport g := hu.hasCompactSupport_initial_position hsupp
  let U : ℝ^4 → ℝ := fun p ↦ u (timeSpaceContinuousLinearEquiv 3 p)
  have hT : 0 < T := hs.trans_le hsτ |>.trans hτT
  have hc := hu.ballIntegral_energy_add_truncatedCone_flux hr hb hg hh hgs hhs hTL hs hsτ hτT c
  have hi := hu.spatialEnergy_eq_of_support hr hb hg hh hvel hsupp hT hTL
    s ⟨hs.le, (hsτ.trans_lt hτT).le⟩
  have hn : 0 ≤ ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential r) U (timeSpaceCons τ x)) c (T - τ) :=
    integral_nonneg fun _ ↦ semilinearWaveEnergyDensity_nonneg _
      (Real.signedPowerPotential_nonneg hr) U _
  have he : ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential r) U (timeSpaceCons s x)) c (T - s) ≤
      semilinearWaveSpatialEnergy (Real.signedPowerPotential r) U 0 := by
    exact (setIntegral_le_integral (s := ball c (T - s)) hi.1
      (Filter.Eventually.of_forall fun _ ↦ semilinearWaveEnergyDensity_nonneg _
        (Real.signedPowerPotential_nonneg hr) U _)).trans_eq hi.2
  dsimp only at hc ⊢
  linarith

/-- The flux density depends only on the field's first derivative germ. -/
private theorem coneDissipation_eq_of_eventuallyEq {V : ℝ → ℝ} {u v : ℝ^4 → ℝ} {p : ℝ^4}
    (h : u =ᶠ[𝓝 p] v) (c : ℝ^3) :
    semilinearWaveConeDissipation V u c p = semilinearWaveConeDissipation V v c p := by
  have hg : classicalWaveSpatialGradient u p = classicalWaveSpatialGradient v p := by
    ext j
    exact partialDeriv_eq_of_fderiv_eq h.fderiv_eq j.succ
  simp only [semilinearWaveConeDissipation, semilinearWaveNullFlux,
    partialDeriv_eq_of_fderiv_eq h.fderiv_eq 0, hg, h.eq_of_nhds]

/-- The constructed C¹ field supplies a retarded H¹ trace with a uniform
scaled bound from its initial energy and displacement. The cone endpoints
are obtained by integrable annular exhaustion, not a C² upgrade. -/
theorem IsIntegralTrajectoryBefore.exists_centered_trace_bound {r b L R : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) {T A E G : ℝ} (hT : 0 < T)
    (hTL : T < L) (hTA : T ≤ A) (hE : 0 ≤ E) (hG : 0 ≤ G) (hinit : ∀ x : ℝ^3, ‖u (0, x)‖ ≤ G)
    (henergy : 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential r)
      (fun p : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 p)) 0 ≤ E ^ 2)
    (c : ℝ^3) :
    ∃ W : H¹(ball (0 : ℝ^3) T), baseRepresentative W =ᵐ[domainMeasure 3 (ball 0 T)] (fun x ↦ u (T -
      ‖x‖, c + x)) ∧
      ‖∇ W‖ ≤ E ∧ ‖wkpBaseCoordinateCLM W‖ / T ≤ E + G * √(A * volume.real (ball (0 : ℝ^3) 1)) := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  have hgs : HasCompactSupport g := hu.hasCompactSupport_initial_position hsupp
  obtain ⟨v, hv, he⟩ := hu.regular.exists_contDiff_eventuallyEq_on_band
    (ContinuousLinearMap.fst ℝ ℝ (ℝ^3)) (s := 0) (τ := T) (by linarith) hTL
  let e := timeSpaceContinuousLinearEquiv 3
  let U : ℝ^4 → ℝ := fun p ↦ u (e p)
  let V : ℝ^4 → ℝ := fun p ↦ v (e p)
  have hV : ContDiff ℝ 1 V := hv.comp e.contDiff
  have hl (s : ℝ) (hs : s ∈ Icc 0 T) (x : ℝ^3) : U =ᶠ[𝓝 (timeSpaceCons s x)] V :=
    (he (s, x) hs).comp_tendsto e.continuousAt
  have hflux (s τ : ℝ) (hs : 0 < s) (hsτ : s ≤ τ) (hτT : τ < T) :
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation (Real.signedPowerPotential r) V c p
          ∂Measure.euclideanHausdorffMeasure 3) ≤
        semilinearWaveSpatialEnergy (Real.signedPowerPotential r) U 0 := by
    have heq : (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation (Real.signedPowerPotential r) U c p
          ∂Measure.euclideanHausdorffMeasure 3) = ∫ p in truncatedConeLateralSurface c T s τ,
          semilinearWaveConeDissipation (Real.signedPowerPotential r) V c p
            ∂Measure.euclideanHausdorffMeasure 3 := by
      apply setIntegral_congr_fun (isCompact_truncatedConeLateralSurface c T s τ).measurableSet
      intro p hp
      have hpt : p 0 ∈ Icc 0 T := ⟨hs.le.trans hp.1, hp.2.1.trans hτT.le⟩
      have hpUV : U =ᶠ[𝓝 p] V := by
        simpa only [timeSpaceCons_spatialPart] using hl (p 0) hpt (spatialPart p)
      exact coneDissipation_eq_of_eventuallyEq hpUV c
    rw [← heq]
    exact hu.truncatedCone_flux_le_initial_energy hr hb hg hh hvel hsupp hTL hs hsτ hτT c
  obtain ⟨Q, hQ, hgrad⟩ := exists_h1_retardedTrace hV c T T
  have hgradQ := norm_gradient_retardedTrace_sq_le_of_truncated_flux
    (Real.contDiff_one_signedPowerPotential hr).continuous
    (Real.signedPowerPotential_nonneg hr) hV c hT hflux Q hgrad
  obtain ⟨W, hW, _, hgW⟩ := exists_centered_retardedTrace Q hQ
  have hWu : baseRepresentative W =ᵐ[domainMeasure 3 (ball 0 T)]
      fun x ↦ u (T - ‖x‖, c + x) := by
    filter_upwards [hW, ae_restrict_mem measurableSet_ball] with x hx hxT
    have ht : T - ‖x‖ ∈ Icc 0 T :=
      ⟨(sub_pos.mpr (by simpa only [mem_ball, dist_zero_right] using hxT)).le,
        sub_le_self _ (norm_nonneg _)⟩
    exact hx.trans (he (T - ‖x‖, c + x) ht).eq_of_nhds.symm
  refine ⟨W, hWu, ?_, hu.norm_base_centered_retardedTrace_div_le hr hb hg hh
    hvel hsupp hT hTL hTA hE hG hinit henergy c W hWu⟩
  rw [hgW]
  nlinarith [norm_nonneg (∇ Q)]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
