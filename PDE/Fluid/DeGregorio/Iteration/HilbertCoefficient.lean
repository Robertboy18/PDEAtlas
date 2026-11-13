/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Characteristics
import CAS.ExactTactic

/-!
# The stretching coefficient for the bounded H² iteration class

The weak Sobolev coordinates construct a continuous representative of each
spectral Hilbert output, with a common square-root modulus of continuity.
Spatial difference quotients of the normalized velocity converge uniformly
to these representatives. Since the velocity is jointly continuous, so is
the stretching coefficient, even though the input curve is assumed continuous
only in L².
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology ENNReal Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem exists_hilbert_slice_of_hkBaseBall
    {g : DerivLp 1 2 univ} {B : NNReal} (hg : g ∈ hkBaseBall 1 2 univ B) :
    ∃ V : ℝ → ℝ, Continuous V ∧
      (realHilbertTransformL2 (oneDimensionalPushforwardL2 g) : ℝ → ℝ) =ᵐ[volume] V ∧
      (∀ x, ‖V x‖ ≤ 2 * (B : ℝ)) ∧
      (∀ x y, |V y - V x| ≤ (B : ℝ) * Real.sqrt |y - x|) := by
  obtain ⟨U, hU, hbase⟩ := hg
  let J : W^{1,2}((Set.univ : Set (ℝ^1))) := lowerOrderCLM (by decide : 1 ≤ 2) U
  have hJ : ‖J‖ ≤ B := (norm_lowerOrderCLM_apply_le _ U).trans hU
  have hb : realLineCoordinateCLM (baseIndex 1 1) J = oneDimensionalPushforwardL2 g := by
    apply congrArg oneDimensionalPushforwardL2
    change (J : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) = g
    simpa only [J, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
      wkpBaseCoordinateCLM_apply] using hbase
  let eta := realLineCoordinateCLM (singleDerivIndex 1 0) J
  have hweak := hasWeakTimeDerivativeOn_realLineCoordinates J
  rw [hb] at hweak
  have hpair := isHilbertPair_realHilbertTransformL2 (oneDimensionalPushforwardL2 g)
  have hHweak := hpair.hasWeakTimeDerivativeOn (isHilbertPair_realHilbertTransformL2 eta)
    hweak
  obtain ⟨V, hV, hVae, hVweak⟩ := hHweak.exists_continuous_ae_eq
  refine ⟨V, hV, hVae, ?_, ?_⟩
  · intro x
    have hbound := (hpair.congr_ae EventuallyEq.rfl hVae).norm_le_eLpNorm_add_weakDerivative
      hV (Lp.memLp eta) hweak x
    simp only [← Lp.norm_def] at hbound
    have h₀ := (norm_realLineCoordinateCLM_le (baseIndex 1 1) J).trans hJ
    rw [hb] at h₀
    have h₁ : ‖eta‖ ≤ B := (norm_realLineCoordinateCLM_le _ J).trans hJ
    have hBB : (B : ℝ) + B = 2 * B := by cas
    exact hbound.trans ((add_le_add h₀ h₁).trans_eq hBB)
  · intro x y
    have hosc := hVweak.enorm_sub_le_eLpNorm_mul_rpow hV (by norm_num : (1 : ℝ≥0∞) < 2)
      x y
    have hpow : SobolevSpace.morreyExponent 1 2 = (1 / 2 : ℝ) := by
      norm_num [SobolevSpace.morreyExponent]
    rw [hpow] at hosc
    have hfinite : eLpNorm (realHilbertTransformL2 eta) 2 volume *
        ENNReal.ofReal |y - x| ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) (ENNReal.rpow_ne_top_of_nonneg
        (by norm_num) ENNReal.ofReal_ne_top)
    have hreal := ENNReal.toReal_mono hfinite hosc
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
    simp only [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_ofReal (abs_nonneg _),
      ← Real.sqrt_eq_rpow, ← Lp.norm_def, norm_realHilbertTransformL2] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_right
      ((norm_realLineCoordinateCLM_le _ J).trans hJ) (Real.sqrt_nonneg _))

private theorem abs_average_sub_le_sqrt
    {V : ℝ → ℝ} (hV : Continuous V) {B : NNReal}
    (hosc : ∀ x y, |V y - V x| ≤ (B : ℝ) * Real.sqrt |y - x|)
    (x d : ℝ) (hd : 0 < d) :
    |d⁻¹ * (∫ s in x..x + d, V s) - V x| ≤ (B : ℝ) * Real.sqrt d := by
  have hbound : ‖∫ s in x..x + d, V s - V x‖ ≤ (B : ℝ) * Real.sqrt d * d := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := x + d) (C := (B : ℝ) * Real.sqrt d)
      (f := fun s ↦ V s - V x) (fun s hs ↦ ?_)
    · simpa only [add_sub_cancel_left, abs_of_pos hd] using h
    · rw [uIoc_of_le (le_add_of_nonneg_right hd.le)] at hs
      have hsd : |s - x| ≤ d := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
        linarith [hs.2]
      exact (hosc x s).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsd) B.coe_nonneg)
  have hid : d⁻¹ * (∫ s in x..x + d, V s) - V x =
      d⁻¹ * (∫ s in x..x + d, V s - V x) := by
    rw [intervalIntegral.integral_sub (hV.intervalIntegrable _ _) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
    generalize (∫ s in x..x + d, V s) = z
    cas using hd.ne'
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  calc
    d⁻¹ * |∫ s in x..x + d, V s - V x| ≤ d⁻¹ * ((B : ℝ) * Real.sqrt d * d) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hd.le)
    _ = (B : ℝ) * Real.sqrt d := by
      have hcancel : d⁻¹ * ((B : ℝ) * Real.sqrt d * d) = (B : ℝ) * Real.sqrt d := by
        rw [mul_comm ((B : ℝ) * Real.sqrt d) d, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      exact hcancel

/-- The complete bounded H² class determines a jointly continuous
spectral Hilbert coefficient. It is the spatial derivative of the normalized
velocity at every point, with uniform bound `2 B` and square-root modulus `B`. -/
theorem exists_hkCurve_hilbert_coefficient
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) :
    ∃ c : ℝ → ℝ → ℝ, Continuous (Function.uncurry c) ∧
      (∀ t, IsHilbertPair (oneDimensionalPushforwardL2 (f (projIcc 0 T hT t)).val)
        (fun x ↦ c x t)) ∧
      (∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x) ∧
      (∀ x t, ‖c x t‖ ≤ 2 * (B : ℝ)) ∧
      (∀ x y t, |c y t - c x t| ≤ (B : ℝ) * Real.sqrt |y - x|) := by
  have hex (t : ℝ) := exists_hilbert_slice_of_hkBaseBall
    (f (projIcc 0 T hT t)).property.1
  choose V hV hVae hVbound hVosc using hex
  let c : ℝ → ℝ → ℝ := fun x t ↦ V t x
  have hprimitive (x t : ℝ) : hkCurveHilbertVelocity hT f x t = ∫ s in 0..x, c s t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hVae t] with s hs _hs
    exact hs
  have hcderiv (x t : ℝ) :
      HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x := by
    have heq : (fun y ↦ hkCurveHilbertVelocity hT f y t) =
        fun y ↦ ∫ s in 0..y, c s t := funext fun y ↦ hprimitive y t
    rw [heq]
    exact intervalIntegral.integral_hasDerivAt_right ((hV t).intervalIntegrable _ _)
      (hV t).stronglyMeasurable.stronglyMeasurableAtFilter (hV t).continuousAt
  have hcint (x d t : ℝ) :
      hkCurveHilbertVelocity hT f (x + d) t - hkCurveHilbertVelocity hT f x t =
        ∫ s in x..x + d, c s t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hcderiv s t) ((hV t).intervalIntegrable _ _)).symm
  let d : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hd (n : ℕ) : 0 < d n := by dsimp only [d]; positivity
  let Q (n : ℕ) (p : ℝ × ℝ) : ℝ :=
    (d n)⁻¹ * (hkCurveHilbertVelocity hT f (p.1 + d n) p.2 -
      hkCurveHilbertVelocity hT f p.1 p.2)
  have hQ (n : ℕ) : Continuous (Q n) :=
    continuous_const.mul
      (((continuous_hkCurveHilbertVelocity hT f).comp
        ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub
          (continuous_hkCurveHilbertVelocity hT f))
  have hQbound (n : ℕ) (p : ℝ × ℝ) :
      dist (c p.1 p.2) (Q n p) ≤ (B : ℝ) * Real.sqrt (d n) := by
    rw [dist_comm, Real.dist_eq]
    dsimp only [Q]
    rw [hcint]
    exact abs_average_sub_le_sqrt (hV p.2) (hVosc p.2) p.1 (d n) (hd n)
  have hsmall : Tendsto (fun n ↦ (B : ℝ) * Real.sqrt (d n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt.const_mul (B : ℝ)
  have hlim : TendstoUniformly Q (Function.uncurry c) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with n hn
    intro p
    exact (hQbound n p).trans_lt hn
  refine ⟨c, hlim.continuous (.of_forall hQ), ?_, hcderiv, ?_, ?_⟩
  · intro t
    exact (isHilbertPair_realHilbertTransformL2 _).congr_ae EventuallyEq.rfl (hVae t)
  · intro x t
    exact hVbound t x
  · intro x y t
    exact hVosc t x y

end DeGregorio.Iteration
