/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Regularization.Approximation
public import PDE.Hyperbolic.Models.Wave.Regularization.Regularity
public import PDE.Hyperbolic.Models.Wave.Regularization.Residual
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralSupportData
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave

/-!
# Spatial regularization of the integral lifespan field

Every proper positive strip of the constructed signed-power trajectory has
joint C¹ regularity and common compact spatial support. Its tested PDE gives
joint C² spatial convolutions with the exact convolved negative signed power
as force. Normalized kernels approximate both the field and every fixed joint
directional derivative locally uniformly.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Common WaveEquation
open scoped Topology Convolution Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Restriction of the lifespan regularity to a proper positive strip. -/
theorem IsIntegralTrajectoryBefore.contDiffOn_pos_strip {r b L S : ℝ} (hb : 0 < b)
    {H u : ℝ × ℝ^3 → ℝ} (hu : IsIntegralTrajectoryBefore r b H L u) (hSL : S < L) :
    ContDiffOn ℝ 1 u (Ioo 0 S ×ˢ univ) := by
  exact hu.regular.mono fun _ hp ↦ ⟨(neg_lt_zero.mpr hb).trans hp.1.1, hp.1.2.trans hSL⟩

/-- The compact-data lifespan supplies one compact support on each
proper strip. This derives the support from the Cauchy data and the integral
equation, including after continuation. -/
theorem IsIntegralTrajectoryBefore.exists_compact_support_pos_strip {r b L S : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hSL : S < L) :
    ∃ K : Set (ℝ^3), IsCompact K ∧ ∀ t ∈ Ioo 0 S, ∀ x ∉ K, u (t, x) = 0 := by
  obtain ⟨Rg, _, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  have hHs (p : ℝ × ℝ^3) (hp : 0 ≤ p.1)
      (hx : max Rg Rh + p.1 < ‖p.2‖) : cauchyFreeField g h p = 0 := by
    exact WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      (hg.of_le (by norm_num)) hh.continuous (fun y hy ↦ hgR y ((le_max_left _ _).trans hy.le))
      (fun y hy ↦ hhR y ((le_max_right _ _).trans hy.le)) p.1 hp p.2 hx
  refine ⟨Metric.closedBall 0 (max Rg Rh + S), isCompact_closedBall _ _, ?_⟩
  intro t ht x hx
  apply image_eq_zero_of_notMem_tsupport (f := fun y : ℝ^3 ↦ u (t, y))
  exact fun hxt ↦ hx (hu.tsupport_subset_closedBall hr hb
    (contDiff_one_cauchyFreeField hg hh) hHs hSL ⟨ht.1.le, ht.2.le⟩ hxt)

/-- Spatial convolution of a signed-power integral trajectory is
jointly C² on each proper positive strip. -/
theorem IsIntegralTrajectoryBefore.contDiffOn_two_convolution {r b L S : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hSL : S < L) {κ : ℝ^3 → ℝ}
    (hκ : ContDiff ℝ 2 κ) (hκs : HasCompactSupport κ) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ^3 ↦ ((fun y ↦ u (p.1, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) p.2)
      (Ioo 0 S ×ˢ univ) := by
  have hu1 := hu.contDiffOn_pos_strip hb hSL
  obtain ⟨K, hK, hs⟩ := hu.exists_compact_support_pos_strip hr hb
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs hSL
  apply contDiffOn_two_convolution_of_tested_wave (F := fun p ↦ -Real.signedPower r (u p))
    isOpen_Ioo hK hu1 (((Real.continuous_signedPower (zero_lt_one.trans_le hr)).comp_continuousOn
      hu1.continuousOn).neg) hs
    (fun t ht x hx ↦ by simp only [hs t ht x hx, Real.signedPower_zero, neg_zero])
    (fun t ht φ hφ hφs ↦ ?_) hκ hκs
  simpa only [neg_mul, integral_neg, sub_eq_add_neg] using
    hu.tested_equation hr hb hg hh hφ hφs ⟨ht.1, ht.2.trans hSL⟩

/-- The smoothed trajectory solves the exact forced wave equation. Its force
is the convolution of the negative signed power of the original field. -/
theorem IsIntegralTrajectoryBefore.hasDerivAt_deriv_convolution {r b L : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) {κ : ℝ^3 → ℝ}
    (hκ : ContDiff ℝ 2 κ) (hκs : HasCompactSupport κ) {t : ℝ} (ht : t ∈ Ioo 0 L) (x : ℝ^3) :
    HasDerivAt (deriv (fun s ↦
        ((fun y ↦ u (s, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) x))
      (laplacian ((fun y ↦ u (t, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) x +
        ((fun y ↦ -Real.signedPower r (u (t, y))) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) x) t := by
  have hut : Continuous (fun y : ℝ^3 ↦ u (t, y)) :=
    hu.regular.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨(neg_lt_zero.mpr hb).trans ht.1, ht.2⟩)
  apply hasDerivAt_deriv_convolution_of_tested_wave hut.locallyIntegrable
    (fun φ hφ hφs ↦ ?_) hκ hκs x
  simpa only [neg_mul, integral_neg, sub_eq_add_neg] using hu.tested_equation hr hb hg hh hφ hφs ht

/-- Each joint directional derivative commutes with spatial convolution of
a trajectory on its positive lifespan. -/
theorem IsIntegralTrajectoryBefore.fderiv_convolution_apply {r b L S : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hSL : S < L) {κ : ℝ^3 → ℝ}
    (hκ : LocallyIntegrable κ volume) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ioo 0 S) (v : ℝ × ℝ^3) :
    fderiv ℝ (fun q : ℝ × ℝ^3 ↦ ((fun y ↦ u (q.1, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) q.2) p v =
      (((fun y ↦ fderiv ℝ u (p.1, y) v) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) p.2) := by
  obtain ⟨K, hK, hs⟩ := hu.exists_compact_support_pos_strip hr hb hg hh hgs hhs hSL
  exact fderiv_convolution_left_with_param_apply (ContinuousLinearMap.mul ℝ ℝ)
    isOpen_Ioo hK (hu.contDiffOn_pos_strip hb hSL) hs hκ hp v

private theorem convolution_normed_swap (u : ℝ × ℝ^3 → ℝ) (φ : ContDiffBump (0 : ℝ^3)) :
    (fun p : ℝ × ℝ^3 ↦ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y ↦ u (p.1, y)))
      p.2) = (fun p : ℝ × ℝ^3 ↦ ((fun y ↦ u (p.1, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] φ.normed
      volume) p.2) := by
  funext p
  rw [convolution_mul_swap, convolution_lsmul]
  simp only [smul_eq_mul, mul_comm]

/-- Normalized spatial convolutions of the lifespan field converge
locally uniformly on every proper positive strip. -/
theorem IsIntegralTrajectoryBefore.tendstoLocallyUniformlyOn_convolution {r b L S : ℝ} (hb : 0 < b)
    {H u : ℝ × ℝ^3 → ℝ} (hu : IsIntegralTrajectoryBefore r b H L u) (hSL : S < L) {ι : Type*}
    {φ : ι → ContDiffBump (0 : ℝ^3)} {l : Filter ι} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun i p ↦ ((fun y ↦ u (p.1, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (φ i).normed volume) p.2) u l (Ioo 0 S ×ˢ univ) := by
  exact (ContDiffBump.tendstoLocallyUniformlyOn_convolution_parameter (μ := volume)
    (hu.contDiffOn_pos_strip hb hSL).continuousOn hφ).congr
      (fun i p _ ↦ congrFun (convolution_normed_swap u (φ i)) p)

/-- Every fixed joint directional derivative of the normalized convolutions
converges locally uniformly to the derivative of the original C¹ field. -/
theorem IsIntegralTrajectoryBefore.tendstoLocallyUniformlyOn_fderiv_convolution_apply {r b L S : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hSL : S < L) {ι : Type*}
    {φ : ι → ContDiffBump (0 : ℝ^3)} {l : Filter ι} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (v : ℝ × ℝ^3) :
    TendstoLocallyUniformlyOn (fun i p ↦ fderiv ℝ (fun q : ℝ × ℝ^3 ↦
      ((fun y ↦ u (q.1, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] (φ i).normed volume) q.2) p v)
      (fun p ↦ fderiv ℝ u p v) l (Ioo 0 S ×ˢ univ) := by
  obtain ⟨K, hK, hs⟩ := hu.exists_compact_support_pos_strip hr hb hg hh hgs hhs hSL
  simpa only [convolution_normed_swap] using
    ContDiffBump.tendstoLocallyUniformlyOn_fderiv_convolution_parameter_apply
      (μ := volume) isOpen_Ioo hK (hu.contDiffOn_pos_strip hb hSL) hs hφ v


/-- The lifespan field supplies the support and regularity needed to
approximate all four canonical spacetime partial derivatives. -/
theorem IsIntegralTrajectoryBefore.tendstoLocallyUniformlyOn_partialDeriv_convolution {r b L S : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hSL : S < L) {ι : Type*}
    {φ : ι → ContDiffBump (0 : ℝ^3)} {l : Filter ι} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (j : Fin 4) :
    let e := timeSpaceContinuousLinearEquiv 3
    let U := fun i (p : ℝ^4) ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y ↦ u ((e p).1, y))) (e p).2
    TendstoLocallyUniformlyOn (fun i ↦ ∂[j] (U i)) (∂[j] (fun p ↦ u (e p)))
      l (spaceTimeCylinder univ (Ioo 0 S)) := by
  obtain ⟨K, hK, hs⟩ := hu.exists_compact_support_pos_strip hr hb hg hh hgs hhs hSL
  exact ContDiffBump.tendstoLocallyUniformlyOn_partialDeriv_convolution_timeSpace
    isOpen_Ioo hK (hu.contDiffOn_pos_strip hb hSL) hs hφ j

/-- The nonlinear equation residual of the smoothed lifespan field
converges locally uniformly to zero. -/
theorem IsIntegralTrajectoryBefore.tendstoLocallyUniformlyOn_convolution_wave_residual {r b L S : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ} (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) (hSL : S < L)
    {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ^3)} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    let U := fun i (p : ℝ × ℝ^3) ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y ↦ u (p.1, y))) p.2
    TendstoLocallyUniformlyOn
      (fun i p ↦ deriv (deriv (fun s ↦ U i (s, p.2))) p.1 -
        laplacian (fun y ↦ U i (p.1, y)) p.2 + Real.signedPower r (U i p))
      (fun _ ↦ 0) l (Ioo 0 S ×ˢ univ) := by
  exact WaveEquation.tendstoLocallyUniformlyOn_convolution_wave_residual
    (hu.contDiffOn_pos_strip hb hSL).continuousOn
    (Real.continuous_signedPower (zero_lt_one.trans_le hr))
    (fun t ht ψ hψ hψs ↦ hu.tested_equation hr hb hg hh hψ hψs ⟨ht.1, ht.2.trans hSL⟩) hφ

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
