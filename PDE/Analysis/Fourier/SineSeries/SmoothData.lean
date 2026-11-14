/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.Reconstruction
import Mathlib.Analysis.PSeries
import PDE.Analysis.Calculus.Periodic

/-!
# Sine reconstruction for smooth periodic data

Two integrations by parts give summable Fourier coefficients for a `C²` function of
period two. Together with Fourier completeness this constructs its odd real part as an
absolutely convergent sine series. No convergence hypothesis is imposed on the data.

The statements concern odd, two-periodic `C²` data on the real line. On the unit interval
these are the `C²` Dirichlet data whose odd reflection is again `C²`.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory Set
open scoped Topology

private theorem norm_fourierCoeffOn_le {F : ℝ → ℂ} {M : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 2, ‖F x‖ ≤ M) (n : ℤ) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 2) F n‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2)
    (f := fun x ↦ fourier (-n) (x : AddCircle ((2 : ℝ) - 0)) • F x) (C := M) ?_
  · rw [fourierCoeffOn_eq_integral, norm_smul]
    norm_num only [sub_zero, norm_div, norm_one, Real.norm_ofNat]
    rw [show |(2 : ℝ) - 0| = 2 by norm_num] at h
    nlinarith [h]
  · intro x hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2), mem_Ioc] at hx
    exact hF x ⟨hx.1.le, hx.2⟩

/-- Smoothness of the real lift of a period-two function implies absolute summability
of its Fourier coefficients. The proof uses two integrations by parts and the `p = 2`
series estimate. -/
theorem summable_fourierCoeff_of_contDiff_two (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ 2 (fun x : ℝ ↦ f (x : AddCircle (2 : ℝ)))) :
    Summable (fourierCoeff f) := by
  let F : ℝ → ℂ := fun x ↦ f (x : AddCircle (2 : ℝ))
  have hF : ContDiff ℝ 2 F := hf
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hper : Function.Periodic F 2 := by
    intro x
    simp only [F, AddCircle.coe_add_period]
  have hper' : Function.Periodic (deriv F) 2 := hper.deriv
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF'.continuous_deriv_one.continuousOn (s := Icc (0 : ℝ) 2))
  have hcoeff (n : ℤ) : fourierCoeff f n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 2) F n := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
    simp only [fourier_coe_apply, zero_add, sub_zero, F]
  have hparts (G : ℝ → ℂ) (hG : Differentiable ℝ G)
      (hG' : Continuous (deriv G)) (hp : Function.Periodic G 2) (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn (by norm_num : (0 : ℝ) < 2) G n =
        (1 / (-2 * Real.pi * Complex.I * n)) *
          (-2 * fourierCoeffOn (by norm_num : (0 : ℝ) < 2) (deriv G) n) := by
    have h := fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 2) hn
      (fun x _ ↦ (hG x).hasDerivAt) (hG'.intervalIntegrable 0 2)
    simpa [show G 2 = G 0 by simpa using hp 0] using h
  have hdecay (n : ℤ) (hn : n ≠ 0) :
      ‖fourierCoeff f n‖ ≤ (M / Real.pi ^ 2) * (1 / (n : ℝ) ^ 2) := by
    rw [hcoeff, hparts F (hF.differentiable (by norm_num))
      (hF.continuous_deriv (by norm_num)) hper n hn,
      hparts (deriv F) hF'.differentiable_one hF'.continuous_deriv_one hper' n hn]
    have hnorm : ‖(1 : ℂ) / (-2 * Real.pi * Complex.I * n)‖ =
        1 / (2 * Real.pi * |(n : ℝ)|) := by
      simp [Complex.norm_intCast]
    simp only [norm_mul, norm_neg, hnorm, Complex.norm_ofNat]
    calc
      1 / (2 * Real.pi * |(n : ℝ)|) *
          (2 * (1 / (2 * Real.pi * |(n : ℝ)|) *
            (2 * ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 2) (deriv (deriv F)) n‖))) ≤
        1 / (2 * Real.pi * |(n : ℝ)|) *
          (2 * (1 / (2 * Real.pi * |(n : ℝ)|) * (2 * M))) := by
            gcongr
            exact norm_fourierCoeffOn_le hM n
      _ = (M / Real.pi ^ 2) * (1 / (n : ℝ) ^ 2) := by
        rw [← sq_abs (n : ℝ)]
        ring
  have hs : Summable (fun n : ℤ ↦ (M / Real.pi ^ 2) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
  apply hs.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  exact hdecay n hn

/-- A continuous real periodic function, viewed on the period-two circle and embedded in `ℂ`. -/
noncomputable def periodicMap (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 2) : C(AddCircle (2 : ℝ), ℂ) where
  toFun := (show Function.Periodic (fun x ↦ (g x : ℂ)) 2 from
    fun x ↦ congrArg Complex.ofReal (hper x)).lift
  continuous_toFun := continuous_coinduced_dom.mpr (Complex.continuous_ofReal.comp hg)

/-- Evaluating the periodic map at a real representative recovers the original function. -/
@[simp] theorem periodicMap_coe (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 2) (x : ℝ) :
    periodicMap g hg hper (x : AddCircle (2 : ℝ)) = (g x : ℂ) :=
  rfl

/-- Fourier-defined real sine coefficients for two-periodic data. -/
noncomputable def periodicCoefficient (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 2) : ℕ → ℝ :=
  coefficient (periodicMap g hg hper)

/-- For odd periodic data, the Fourier-defined coefficient is the usual unit-interval
sine coefficient. The factor two comes from the squared norm of an unnormalized sine mode. -/
theorem periodicCoefficient_eq_integral (g : ℝ → ℝ) (hg : Continuous g)
    (hper : Function.Periodic g 2) (hodd : ∀ x, g (-x) = -g x) (n : ℕ) :
    periodicCoefficient g hg hper n =
      2 * ∫ x in (0 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x := by
  have hkernel (k : ℤ) (x : ℝ) :
      (fourier (-k) (x : AddCircle (2 : ℝ)) * (g x : ℂ)).im =
        -(g x * Real.sin ((k : ℝ) * Real.pi * x)) := by
    have he : fourier (-k) (x : AddCircle (2 : ℝ)) =
        Complex.exp (((-(k : ℝ) * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring
    rw [he]
    simp only [Complex.mul_im, Complex.exp_re, Complex.exp_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, zero_add, mul_one,
      Real.exp_zero, one_mul, neg_mul, Real.sin_neg]
    ring
  have hcoeff (k : ℤ) :
      (fourierCoeff (periodicMap g hg hper) k).im =
        -(1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, g x * Real.sin ((k : ℝ) * Real.pi * x) := by
    have hc : Continuous (fun x : ℝ ↦
        fourier (-k) (x : AddCircle (2 : ℝ)) * (g x : ℂ)) := by
      fun_prop
    rw [fourierCoeff_eq_intervalIntegral _ _ (-1)]
    simp only [periodicMap_coe, show (-1 : ℝ) + 2 = 1 by norm_num, smul_eq_mul]
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    have him := Complex.imCLM.intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := volume) (-1) 1)
    simp only [Complex.imCLM_apply] at him
    rw [← him]
    simp only [hkernel, intervalIntegral.integral_neg]
    ring
  have heven (x : ℝ) :
      g (-x) * PDE.Representations.intervalDirichletSineMode n (-x) =
        g x * PDE.Representations.intervalDirichletSineMode n x := by
    simp [PDE.Representations.intervalDirichletSineMode, hodd, Real.sin_neg]
  have hc : Continuous (fun x ↦ g x * PDE.Representations.intervalDirichletSineMode n x) :=
    hg.mul (PDE.Representations.contDiff_intervalDirichletSineMode (k := 0) n).continuous
  have hequal :
      (∫ x in (-1 : ℝ)..0, g x * PDE.Representations.intervalDirichletSineMode n x) =
        ∫ x in (0 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x := by
    simpa only [heven, neg_zero] using
      (intervalIntegral.integral_comp_neg
        (f := fun x ↦ g x * PDE.Representations.intervalDirichletSineMode n x)
        (a := (0 : ℝ)) (b := 1)).symm
  have hfull :
      (∫ x in (-1 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x) =
        2 * ∫ x in (0 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1), hequal, two_mul]
  unfold periodicCoefficient coefficient
  rw [hcoeff, hcoeff]
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg,
    mul_neg, intervalIntegral.integral_neg]
  change - -((1 / 2 : ℝ) *
      (∫ x in (-1 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x)) -
    -((1 / 2 : ℝ) *
      (∫ x in (-1 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x)) = _
  rw [hfull]
  ring

/-- Twice continuously differentiable periodic data have absolutely summable sine coefficients. -/
theorem summable_norm_periodicCoefficient (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hper : Function.Periodic g 2) :
    Summable (fun n ↦ ‖periodicCoefficient g hg.continuous hper n‖) := by
  apply summable_norm_coefficient
  apply summable_fourierCoeff_of_contDiff_two
  simp only [periodicMap_coe]
  exact Complex.ofRealCLM.contDiff.comp hg

/-- An odd, two-periodic `C²` function is the sum of its Fourier-defined sine series. -/
theorem hasSum_periodicCoefficient_sineMode (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hper : Function.Periodic g 2) (hodd : ∀ x, g (-x) = -g x) (x : ℝ) :
    HasSum (fun n ↦ periodicCoefficient g hg.continuous hper n *
      PDE.Representations.intervalDirichletSineMode n x) (g x) := by
  have hsum := summable_fourierCoeff_of_contDiff_two (periodicMap g hg.continuous hper)
    (show ContDiff ℝ 2 (fun y : ℝ ↦
      periodicMap g hg.continuous hper (y : AddCircle (2 : ℝ))) from by
        simpa only [periodicMap_coe, Function.comp_def, Complex.ofRealCLM_apply] using
          Complex.ofRealCLM.contDiff.comp hg)
  have h := hasSum_coefficient_sineMode hsum x
  have hinit : oddRealPart (periodicMap g hg.continuous hper) x = g x := by
    simp only [oddRealPart, periodicMap_coe, Complex.ofReal_re, hodd]
    ring
  simpa only [periodicCoefficient, hinit] using h

end PDE.Analysis.Fourier.SineSeries
