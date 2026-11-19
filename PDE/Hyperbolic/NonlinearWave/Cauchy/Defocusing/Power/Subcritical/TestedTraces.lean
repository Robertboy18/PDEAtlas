/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.TrajectoryWeakEquation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableTrajectory
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity

/-!
# Initial time identities for signed-power trajectories

Compact spatial tests of a C¹ integral trajectory satisfy both endpoint time
identities with the original Cauchy data. The velocity identity uses the tested
PDE only at positive times; continuity supplies its initial value.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open PDE.Analysis.Evolution
open scoped Topology Laplacian Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A continuous field paired with a compact continuous spatial test depends
continuously on time, without a global bound on the field. -/
theorem continuous_integral_mul_spatial_test {H : ℝ × ℝ^3 → ℝ} (hH : Continuous H) {φ : ℝ^3 → ℝ}
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    Continuous (fun t ↦ ∫ x : ℝ^3, H (t, x) * φ x) := by
  have he (t : ℝ) : (∫ x in tsupport φ, H (t, x) * φ x) =
      ∫ x : ℝ^3, H (t, x) * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  simp_rw [← he]
  exact continuous_parametric_integral_of_continuous (hH.mul (hφ.comp continuous_snd)) hφs.isCompact

/-- Both spatially tested Cauchy variables have their integral
primitives through the initial time. The acceleration is assumed only after
spatial testing and only at positive times. -/
theorem integral_primitives_of_signedPower_tested_equation {r b L S : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    (hS : 0 ≤ S) (hSL : S < L) {u : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    {g h : ℝ^3 → ℝ} (hpos : ∀ x : ℝ^3, u (0, x) = g x)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : HasCompactSupport φ)
    (hwave : ∀ t ∈ Ioo 0 L, HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
      ((∫ x : ℝ^3, u (t, x) * laplacian φ x) - ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) :
    ContinuousOn (fun t ↦ ∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) (Icc 0 S) ∧
    ContinuousOn (fun t ↦ (∫ x : ℝ^3, u (t, x) * laplacian φ x) -
      ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) (Icc 0 S) ∧
    (∀ t ∈ Icc 0 S,
      (∫ s in 0..t, ∫ x : ℝ^3, fderiv ℝ u (s, x) (1, 0) * φ x) =
        (∫ x : ℝ^3, u (t, x) * φ x) - ∫ x : ℝ^3, g x * φ x) ∧
    ∀ t ∈ Icc 0 S,
      (∫ s in 0..t, (∫ x : ℝ^3, u (s, x) * laplacian φ x) -
        ∫ x : ℝ^3, Real.signedPower r (u (s, x)) * φ x) =
        (∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) -
          ∫ x : ℝ^3, h x * φ x := by
  obtain ⟨a, hSa, haL⟩ := exists_between hSL
  obtain ⟨U, hU, hUE⟩ := hu.exists_contDiff_eventuallyEq_on_band
    (ContinuousLinearMap.fst ℝ ℝ (ℝ^3)) (s := -b / 2) (τ := a) (by linarith) haL
  have hmem {t : ℝ} (ht : t ∈ Icc 0 S) : t ∈ Icc (-b / 2) a :=
    ⟨by linarith [ht.1], ht.2.trans hSa.le⟩
  have hv (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ^3) : u (t, x) = U (t, x) :=
    (hUE (t, x) (hmem ht)).eq_of_nhds
  have hdv (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ^3) :
      fderiv ℝ u (t, x) = fderiv ℝ U (t, x) := (hUE (t, x) (hmem ht)).fderiv_eq
  let A : ℝ → ℝ := fun s ↦ ∫ x : ℝ^3, U (s, x) * φ x
  let V : ℝ → ℝ := fun s ↦ ∫ x : ℝ^3, fderiv ℝ U (s, x) (1, 0) * φ x
  let G : ℝ → ℝ := fun s ↦ (∫ x : ℝ^3, U (s, x) * laplacian φ x) -
    ∫ x : ℝ^3, Real.signedPower r (U (s, x)) * φ x
  have hAc : Continuous A := continuous_integral_mul_spatial_test hU.continuous hφ.continuous hφs
  have hVc : Continuous V := continuous_integral_mul_spatial_test
    ((hU.continuous_fderiv one_ne_zero).clm_apply continuous_const) hφ.continuous hφs
  have hGc : Continuous G := (continuous_integral_mul_spatial_test hU.continuous
      hφ.continuous_coordinate_laplacian hφs.coordinate_laplacian).sub
    (continuous_integral_mul_spatial_test
      ((Real.continuous_signedPower (zero_lt_one.trans_le hr)).comp hU.continuous)
      hφ.continuous hφs)
  have hAderiv (t : ℝ) : HasDerivAt A (V t) t :=
    hasDerivAt_integral_mul_spatial_test hU hφ.continuous hφs t
  have hAeq (t : ℝ) (ht : t ∈ Icc 0 S) :
      (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x) =ᶠ[𝓝 t] A := by
    filter_upwards [Ioo_mem_nhds (show -b / 2 < t by linarith [ht.1]) (ht.2.trans_lt hSa)] with s hs
    apply integral_congr_ae
    filter_upwards [] with x
    rw [(hUE (s, x) ⟨hs.1.le, hs.2.le⟩).eq_of_nhds]
  have hfirst : deriv A = V := funext (fun t ↦ (hAderiv t).deriv)
  have hVderiv (t : ℝ) (ht : t ∈ Ioo 0 S) : HasDerivAt V (G t) t := by
    have he := (hwave t ⟨ht.1, ht.2.trans hSL⟩).congr_of_eventuallyEq
      (hAeq t ⟨ht.1.le, ht.2.le⟩).deriv.symm
    rw [hfirst] at he
    simpa only [G, hv t ⟨ht.1.le, ht.2.le⟩] using he
  have hA0 : A 0 = ∫ x : ℝ^3, g x * φ x := by
    simp only [A, ← hv 0 ⟨le_rfl, hS⟩, hpos]
  have hV0 : V 0 = ∫ x : ℝ^3, h x * φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have he : (fun t ↦ U (t, x)) =ᶠ[𝓝 0] fun t ↦ u (t, x) :=
      ((hUE (0, x) (hmem ⟨le_rfl, hS⟩)).comp_tendsto
        (continuousAt_id.prodMk continuousAt_const)).symm
    have hdu := (hvel x).congr_of_eventuallyEq he
    have hdU := ((hU.differentiable one_ne_zero (0, x)).hasFDerivAt).comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    simp only [hdU.unique hdu]
  have hvEq (t : ℝ) (ht : t ∈ Icc 0 S) :
      (∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) = V t := by
    simp only [V, hdv t ht]
  have hgEq (t : ℝ) (ht : t ∈ Icc 0 S) : ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
        ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) = G t := by
    simp only [G, hv t ht]
  refine ⟨hVc.continuousOn.congr (fun t ht ↦ hvEq t ht),
    hGc.continuousOn.congr (fun t ht ↦ hgEq t ht), ?_, ?_⟩
  · intro t ht
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      hAc.continuousOn (fun s _ ↦ hAderiv s) (hVc.intervalIntegrable 0 t)
    rw [hA0] at hft
    have hAt : (∫ x : ℝ^3, u (t, x) * φ x) = A t := by simp only [A, hv t ht]
    rw [hAt]
    rw [← hft]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hvEq s ⟨hs.1, hs.2.trans ht.2⟩
  · intro t ht
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      hVc.continuousOn (fun s hs ↦ hVderiv s ⟨hs.1, hs.2.trans_le ht.2⟩)
      (hGc.intervalIntegrable 0 t)
    rw [hV0, ← hvEq t ht] at hft
    rw [← hft]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hgEq s ⟨hs.1, hs.2.trans ht.2⟩

/-- The C¹ signed-power trajectory satisfies both endpoint time-test identities
with the original initial displacement and velocity. Tests may be nonzero at
initial time; only their final value is required to vanish. -/
theorem initial_time_identities_of_signedPower_tested_equation {r b L S : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) (hS : 0 ≤ S) (hSL : S < L) {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) {g h : ℝ^3 → ℝ}
    (hpos : ∀ x : ℝ^3, u (0, x) = g x) (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ)
    (hwave : ∀ t ∈ Ioo 0 L, HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
      ((∫ x : ℝ^3, u (t, x) * laplacian φ x) - ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t)
    (τ : TimeTest 0 S) :
    -(∫ t in 0..S, (∫ x : ℝ^3, u (t, x) * φ x) * τ.derivFun t) =
      (∫ t in 0..S, (∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) * τ.toFun t) +
        (∫ x : ℝ^3, g x * φ x) * τ.toFun 0 ∧
    -(∫ t in 0..S, (∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) * τ.derivFun t) =
      (∫ t in 0..S, ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
        ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) * τ.toFun t) +
          (∫ x : ℝ^3, h x * φ x) * τ.toFun 0 := by
  obtain ⟨hV, hG, hq, hp⟩ := integral_primitives_of_signedPower_tested_equation
    hr hb hS hSL hu hpos hvel hφ hφs hwave
  exact ⟨initial_identity_of_integrable_primitive hS τ (hV.intervalIntegrable_of_Icc hS) _ hq,
    initial_identity_of_integrable_primitive hS τ (hG.intervalIntegrable_of_Icc hS) _ hp⟩

/-- The signed-power integral equation implies the endpoint weak time
identities for every compact C² spatial test and every admissible time test. -/
theorem initial_time_identities_of_signedPower_integral_eq {r b L S : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    (hS : 0 ≤ S) (hSL : S < L) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (hpos : ∀ x : ℝ^3, u (0, x) = g x) (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (heq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = cauchyFreeField g h p +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ -Real.signedPower r
      (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2))
    {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) (τ : TimeTest 0 S) :
    -(∫ t in 0..S, (∫ x : ℝ^3, u (t, x) * φ x) * τ.derivFun t) =
      (∫ t in 0..S, (∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) * τ.toFun t) +
        (∫ x : ℝ^3, g x * φ x) * τ.toFun 0 ∧
    -(∫ t in 0..S, (∫ x : ℝ^3, fderiv ℝ u (t, x) (1, 0) * φ x) * τ.derivFun t) =
      (∫ t in 0..S, ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
        ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) * τ.toFun t) +
          (∫ x : ℝ^3, h x * φ x) * τ.toFun 0 :=
  initial_time_identities_of_signedPower_tested_equation hr hb hS hSL hu hpos hvel hφ hφs
    (fun _ ht ↦ hasDerivAt_deriv_integral_of_signedPower_integral_eq hr hb hg hh hu heq hφ hφs ht) τ

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
