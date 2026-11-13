/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Calculus.GreenPairing
public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Propagation

/-!
# Compact backward Fourier tests for the wave residual

The Fourier wave with zero terminal displacement and prescribed smooth
compactly supported terminal velocity tests a zero-data classical field by its
wave residual. Finite propagation gives common compact support for the test,
while the compared field needs no support or spatial growth bound. Only the
field and its first time derivative require continuous traces at the initial
and terminal times; the second derivatives and equation are interior data.
-/

@[expose] public section

open MeasureTheory Filter Set PDE
open scoped Topology

open PDE.Common
open scoped SchwartzMap

namespace WaveEquation.Fourier

/-- A compact Fourier backward wave tests a zero-data classical field by its
wave residual. Spatial compact support is derived from the terminal test;
only continuous first derivative traces are required at time zero. -/
theorem integral_mul_eq_integral_backwardWave_residual {n : ℕ} [Fact (0 < n)] {b : ℝ} (hb : 0 < b)
    (φ : 𝓢(ℝ^n, ℝ)) (hφ : HasCompactSupport (φ : ℝ^n → ℝ)) {u U U₂ : ℝ → ℝ^n → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hzero : ∀ x, u 0 x = 0) (hzero' : ∀ x, U 0 x = 0)
    (hint : IntervalIntegrable (fun s ↦ ∫ x, (U₂ s x - laplacian (u s) x) *
      realSolution 0 φ (timeSpaceCons (b - s) x)) volume 0 b) :
    (∫ x, u b x * φ x) = ∫ s in 0..b, ∫ x,
      (U₂ s x - laplacian (u s) x) * realSolution 0 φ (timeSpaceCons (b - s) x) := by
  let Φ := realSolution 0 φ
  let v := fun s x ↦ Φ (timeSpaceCons (b - s) x)
  let V := fun s x ↦ -(∂[0] Φ) (timeSpaceCons (b - s) x)
  let V₂ := fun s x ↦ (∂[0] (∂[0] Φ)) (timeSpaceCons (b - s) x)
  have hΦ : ContDiff ℝ 2 Φ := contDiff_two_realSolution 0 φ
  have hΦ' : ContDiff ℝ 1 (∂[0] Φ) := contDiff_partialDeriv_of_succ hΦ
  have hΦ'' : Continuous (∂[0] (∂[0] Φ)) := (contDiff_partialDeriv_of_succ (m := 0) hΦ').continuous
  have ha : Continuous (fun p : ℝ × ℝ^n ↦ timeSpaceCons (b - p.1) p.2) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have hv : Continuous v.uncurry := hΦ.continuous.comp ha
  have hV : Continuous V.uncurry := (hΦ'.continuous.comp ha).neg
  have hV₂ : Continuous V₂.uncurry := hΦ''.comp ha
  have hdv (s : ℝ) (x : ℝ^n) : HasDerivAt (fun r ↦ v r x) (V s x) s := by
    simpa [v, V, Function.comp_def] using (hasDerivAt_timeSpaceCons Φ (b - s) x
        (hΦ.differentiable (by norm_num) _)).comp s ((hasDerivAt_id s).const_sub b)
  have hdV (s : ℝ) (x : ℝ^n) : HasDerivAt (fun r ↦ V r x) (V₂ s x) s := by
    have hd := ((hasDerivAt_timeSpaceCons (∂[0] Φ) (b - s) x
      (hΦ'.differentiable one_ne_zero _)).comp s ((hasDerivAt_id s).const_sub b)).neg
    simp only [Function.comp_def, mul_neg, mul_one, neg_neg] at hd
    exact hd
  obtain ⟨K, hK, hsupport⟩ := exists_uniform_compactSupport_realSolution 0 φ
    (by simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : ℝ^n ↦ (0 : ℝ)))) hφ b
  have hsupp (s : ℝ) (hs : s ∈ Icc 0 b) (x : ℝ^n) (hx : x ∉ K) : v s x = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hx' ↦ ?_
    exact hx (hsupport (b - s) ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩ hx')
  have hw (s : ℝ) (x : ℝ^n) : V₂ s x = laplacian (v s) x := by
    have he := waveOperator_realSolution (0 : 𝓢(ℝ^n, ℝ)) φ (timeSpaceCons (b - s) x)
    change (∂[0] (∂[0] Φ)) (timeSpaceCons (b - s) x) -
      (∑ i : Fin n, (∂[i.succ] (∂[i.succ] Φ)) (timeSpaceCons (b - s) x)) = 0 at he
    rw [← laplacian_timeSlice Φ (b - s) x hΦ] at he
    exact sub_eq_zero.mp he
  have he := integral_wavePairing_derivative_eq_sub hb hK hu hv.continuousOn hU
    hV.continuousOn hU₂ hV₂.continuousOn hdu (fun s _ ↦ hdv s) hdU (fun s _ ↦ hdV s) hsupp hu₂
    (fun s _ ↦ hΦ.comp (contDiff_timeSpaceCons_spatial n (b - s))) (fun s _ ↦ hw s) hint
  have hbv (x : ℝ^n) : v b x = 0 := by
    simp only [v, Φ, sub_self, realSolution_initial_position, zero_apply]
  have hbV (x : ℝ^n) : V b x = -φ x := by
    simp only [V, Φ, sub_self, partialDeriv_realSolution_initial_velocity]
  simpa only [hbv, hbV, hzero, hzero', mul_zero, zero_mul, sub_zero, zero_sub,
    mul_neg, neg_neg, integral_zero] using he.symm

end WaveEquation.Fourier
