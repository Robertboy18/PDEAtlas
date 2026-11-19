/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.CharacteristicTrace.Smooth
import PDE.Analysis.Calculus.Gradient
import PDE.Analysis.InnerProductSpace.Calculus.Normalization
import PDE.Analysis.Integration.UniformLimit
import PDE.Analysis.Topology.UniformConvergence
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import PDE.Hyperbolic.Models.Wave.Regularization.Approximation
import PDE.Hyperbolic.Models.Wave.Regularization.Regularity

/-!
# Weak characteristic traces of C¹ tested waves

A joint C¹ field with continuous forcing satisfies the characteristic trace
equation in the weak sense on each compact test support away from the cone
vertex and the time faces. Spatial convolution produces C² approximants from
the tested wave equation; their values, time derivatives, and forces converge
on the test support.
-/

@[expose] public noncomputable section

open PDE PDE.Common PDE.Analysis Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Gradient Convolution

namespace WaveEquation

variable {n : ℕ}

private theorem tendsto_integral_mul_compact {f : ℕ → ℝ^n → ℝ} {g ψ : ℝ^n → ℝ} {K : Set (ℝ^n)}
    (hK : IsCompact K) (hf : ∀ i, ContinuousOn (f i) K) (hg : ContinuousOn g K)
    (hψ : ContinuousOn ψ K) (hz : ∀ x, x ∉ K → ψ x = 0)
    (hlim : TendstoLocallyUniformlyOn f g atTop K) :
    Tendsto (fun i ↦ ∫ x, f i x * ψ x) atTop (𝓝 (∫ x, g x * ψ x)) := by
  have hc : TendstoLocallyUniformlyOn (fun _ : ℕ ↦ ψ) ψ atTop K :=
    fun V hV x _ ↦ ⟨K, self_mem_nhdsWithin, Eventually.of_forall
      (fun _ _ _ ↦ refl_mem_uniformity hV)⟩
  have hm : Continuous (fun p : ℝ × ℝ ↦ p.1 * p.2) := continuous_fst.mul continuous_snd
  have hl := hm.comp_tendstoLocallyUniformlyOn (hlim.prodMk hc) (hg.prodMk hψ)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hl
  have hi := hu.tendsto_setIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun i ↦ (hf i).mul hψ) hK hK.measurableSet
    (Subset.refl _) hK.measure_lt_top.ne
  have he (a : ℝ^n → ℝ) : (∫ x in K, a x * ψ x) = ∫ x, a x * ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx, mul_zero])
  simpa only [he] using hi

/-- A C¹ field satisfying the spatially tested wave equation obeys the weak
characteristic trace equation. Compact test support avoids the cone tip and
time faces. Spatial convolution supplies every approximation and limit. -/
theorem integral_characteristicTrace_of_tested_wave {u F : ℝ × ℝ^n → ℝ} {I : Set ℝ} {K : Set (ℝ^n)}
    (hI : IsOpen I) (hK : IsCompact K) (hu : ContDiffOn ℝ 1 u (I ×ˢ univ))
    (hF : ContinuousOn F (I ×ˢ univ)) (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0)
    (hsF : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0)
    (hw : ∀ t ∈ I, ∀ ψ : ℝ^n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      HasDerivAt (deriv (fun s ↦ ∫ y, u (s, y) * ψ y))
      ((∫ y, u (t, y) * PDE.laplacian ψ y) + ∫ y, F (t, y) * ψ y) t)
    (c : ℝ^n) (T : ℝ) {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (haway : ∀ x ∈ tsupport φ, x ≠ c) (ht : ∀ x ∈ tsupport φ, T - ‖x - c‖ ∈ I) :
    (∫ x, u (T - ‖x - c‖, x) * PDE.laplacian φ x) -
        2 * (∫ x, fderiv ℝ u (T - ‖x - c‖, x) (1, 0) *
          ⟪NormedSpace.normalize (x - c), ∇ φ x⟫) -
        ((n : ℝ) - 1) *
          (∫ x, (fderiv ℝ u (T - ‖x - c‖, x) (1, 0) / ‖x - c‖) * φ x) =
      -(∫ x, F (T - ‖x - c‖, x) * φ x) := by
  let κ : ℕ → ContDiffBump (0 : ℝ^n) := fun j ↦
    { rIn := (1 / ((j : ℝ) + 1)) / 2
      rOut := 1 / ((j : ℝ) + 1)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hκ : Tendsto (fun j ↦ (κ j).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let e := timeSpaceContinuousLinearEquiv n
  let A := fun i (p : ℝ × ℝ^n) ↦ ((κ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (fun y ↦ u (p.1, y))) p.2
  let B := fun i (p : ℝ × ℝ^n) ↦ ((κ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (fun y ↦ F (p.1, y))) p.2
  let U := fun i (p : ℝ^(n + 1)) ↦ A i (e p)
  let v := fun p : ℝ^(n + 1) ↦ u (e p)
  let S := spaceTimeCylinder (univ : Set (ℝ^n)) I
  let G := backwardConeGraph c T
  let g := fun x : ℝ^n ↦ (T - ‖x - c‖, x)
  have hg : Continuous g :=
    (continuous_const.sub ((continuous_id.sub continuous_const).norm)).prodMk continuous_id
  have hG : Continuous G := e.symm.continuous.comp hg
  have hgm : MapsTo g (tsupport φ) (I ×ˢ univ) := fun x hx ↦ ⟨ht x hx, mem_univ _⟩
  have hGm : MapsTo G (tsupport φ) S := fun x hx ↦ ⟨ht x hx, mem_univ _⟩
  have hS : IsOpen S := isOpen_spaceTimeCylinder isOpen_univ hI
  have hv : ContDiffOn ℝ 1 v S := hu.comp_continuousLinearMap e.toContinuousLinearMap
  have hreg (i : ℕ) : ContDiffOn ℝ 2 (U i) S :=
    contDiffOn_two_convolution_timeSpace_of_tested_wave hI hK hu hF hs hsF hw
      ((κ i).contDiff_normed (μ := volume)) ((κ i).hasCompactSupport_normed (μ := volume))
  have hswap (i : ℕ) (f : ℝ^n → ℝ) : f ⋆[ContinuousLinearMap.mul ℝ ℝ] (κ i).normed volume =
        (κ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f := funext fun x ↦ by
    rw [convolution_mul_swap, convolution_lsmul]
    simp only [smul_eq_mul, mul_comm]
  have hround (t : ℝ) (x : ℝ^n) : e (timeSpaceCons t x) = (t, x) := by
    simp only [e, timeSpaceContinuousLinearEquiv_apply, time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
  have hop (i : ℕ) (x : ℝ^n) (hx : x ∈ tsupport φ) :
      waveOperator (U i) (G x) = B i (g x) := by
    have ht0 := ht x hx
    have huloc : LocallyIntegrable (fun y ↦ u (T - ‖x - c‖, y)) volume :=
      (hu.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ ↦ ⟨ht0, mem_univ _⟩)).locallyIntegrable
    have he := hasDerivAt_deriv_convolution_of_tested_wave
      (u := fun t y ↦ u (t, y)) (F := fun t y ↦ F (t, y)) huloc (hw _ ht0)
      ((κ i).contDiff_normed (μ := volume)) ((κ i).hasCompactSupport_normed (μ := volume)) x
    simp_rw [hswap i] at he
    rw [show G x = timeSpaceCons (T - ‖x - c‖) x from rfl, waveOperator_timeSpaceCons_of_contDiffAt
        ((hreg i).contDiffAt (hS.mem_nhds (hGm hx)))]
    simp only [U, hround]
    change deriv (deriv (fun s ↦ A i (s, x))) (T - ‖x - c‖) -
      PDE.laplacian (fun y ↦ A i (T - ‖x - c‖, y)) x = B i (g x)
    rw [he.deriv]
    exact add_sub_cancel_left _ _
  have hUc (i : ℕ) : ContinuousOn (fun x ↦ U i (G x)) (tsupport φ) :=
    (hreg i).continuousOn.comp hG.continuousOn hGm
  have hDc (i : ℕ) : ContinuousOn (fun x ↦ ∂[0] (U i) (G x)) (tsupport φ) :=
    ((hreg i).of_le (by norm_num) |>.continuousOn_partialDeriv 0 hS).comp hG.continuousOn hGm
  have hBc (i : ℕ) : ContinuousOn (fun x ↦ B i (g x)) (tsupport φ) := by
    have hb := continuousOn_convolution_right_with_param (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ) hK (fun t y ht hy ↦ hsF t ht y hy)
      ((κ i).continuous_normed (μ := volume)).locallyIntegrable hF
    exact hb.comp hg.continuousOn hgm
  have hvc : ContinuousOn (fun x ↦ v (G x)) (tsupport φ) := hv.continuousOn.comp hG.continuousOn hGm
  have hvd : ContinuousOn (fun x ↦ ∂[0] v (G x)) (tsupport φ) :=
    (hv.continuousOn_partialDeriv 0 hS).comp hG.continuousOn hGm
  have hFc : ContinuousOn (fun x ↦ F (g x)) (tsupport φ) := hF.comp hg.continuousOn hgm
  have hlim := ((ContDiffBump.tendstoLocallyUniformlyOn_convolution_parameter
    (μ := volume) hu.continuousOn hκ).comp e (mapsTo_preimage e _)
      e.continuous.continuousOn).comp G hGm hG.continuousOn
  have hD := (ContDiffBump.tendstoLocallyUniformlyOn_partialDeriv_convolution_timeSpace
    hI hK hu hs hκ 0).comp G hGm hG.continuousOn
  have hB := (ContDiffBump.tendstoLocallyUniformlyOn_convolution_parameter
    (μ := volume) hF hκ).comp g hgm hg.continuousOn
  have hΔc : Continuous (PDE.laplacian φ) := by
    unfold PDE.laplacian
    exact continuous_finsetSum _ fun i _ ↦
      ((hφ.partialDeriv i (k := 1) (by norm_num)).continuous_partialDeriv i)
  have hΔz (x : ℝ^n) (hx : x ∉ tsupport φ) : PDE.laplacian φ x = 0 := Finset.sum_eq_zero fun i _ ↦
      partialDeriv_eq_zero_of_notMem_tsupport i fun h ↦ hx (tsupport_partialDeriv_subset i h)
  have hgrad : Continuous (∇ φ) := continuous_gradient_of_contDiff (hφ.of_le (by norm_num))
  have hgradz (x : ℝ^n) (hx : x ∉ tsupport φ) : ∇ φ x = 0 := by
    ext i
    simp [gradient_apply_eq_partialDeriv, partialDeriv_eq_zero_of_notMem_tsupport i hx]
  have hnormal : ContinuousOn (fun x : ℝ^n ↦ NormedSpace.normalize (x - c))
      (tsupport φ) := by
    intro x hx
    exact ((NormedSpace.contDiffAt_normalize (k := 1) (sub_ne_zero.mpr (haway x hx))).comp x
      (contDiffAt_id.sub contDiffAt_const)).continuousAt.continuousWithinAt
  have hradc : ContinuousOn (fun x ↦ φ x / ‖x - c‖) (tsupport φ) := hφ.continuous.continuousOn.div
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
      (fun x hx ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (haway x hx)))
  have hL₁ := tendsto_integral_mul_compact hc hUc hvc hΔc.continuousOn hΔz hlim
  have hL₂ := tendsto_integral_mul_compact hc hDc hvd (hnormal.inner hgrad.continuousOn)
    (fun x hx ↦ by rw [hgradz x hx, inner_zero_right]) hD
  have hL₃ := tendsto_integral_mul_compact hc hDc hvd hradc
    (fun x hx ↦ by rw [image_eq_zero_of_notMem_tsupport hx, zero_div]) hD
  have hR := tendsto_integral_mul_compact hc hBc hFc hφ.continuous.continuousOn
    (fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx) hB
  have hforce (i : ℕ) : (∫ x, waveOperator (U i) (G x) * φ x) = ∫ x, B i (g x) * φ x := by
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only [hop i x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hrad (a : ℝ^n → ℝ) : (fun x ↦ (a x / ‖x - c‖) * φ x) =
      (fun x ↦ a x * (φ x / ‖x - c‖)) := funext fun x ↦ by ring
  have heq (i : ℕ) : (∫ x, U i (G x) * PDE.laplacian φ x) -
        2 * (∫ x, ∂[0] (U i) (G x) * ⟪NormedSpace.normalize (x - c), ∇ φ x⟫) -
        ((n : ℝ) - 1) * (∫ x, ∂[0] (U i) (G x) * (φ x / ‖x - c‖)) =
      -(∫ x, B i (g x) * φ x) := by
    have hi := integral_characteristicTrace_of_contDiffAt (u := U i) c T hφ hc haway
      (fun x hx ↦ (hreg i).contDiffAt (hS.mem_nhds (hGm hx)))
    rw [← hforce i]
    convert hi using 3
    rw [hrad]
  have hvalue (x : ℝ^n) : v (G x) = u (g x) := rfl
  have hvelocity (x : ℝ^n) : ∂[0] v (G x) = fderiv ℝ u (g x) (1, 0) := by
    have he : e (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = (1, 0) := by
      apply Prod.ext
      · simp [e, timeSpaceContinuousLinearEquiv_apply, time]
      · change spatialPart (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = 0
        rw [← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_zero]
    change (fderiv ℝ (u ∘ e) (backwardConeGraph c T x)) (EuclideanSpace.single 0 1) = _
    rw [e.comp_right_fderiv, ContinuousLinearMap.comp_apply]
    change (fderiv ℝ u (e (backwardConeGraph c T x))) (e (EuclideanSpace.single 0 1)) = _
    rw [he]
    congr 2
  have htrace := tendsto_nhds_unique ((hL₁.sub (hL₂.const_mul 2)).sub
    (hL₃.const_mul ((n : ℝ) - 1))) (hR.neg.congr fun i ↦ (heq i).symm)
  rw [hrad]
  simpa only [hvalue, hvelocity, g] using htrace

end WaveEquation
