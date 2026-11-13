/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalFreeField
public import PDE.Analysis.Calculus.ParametricIntegral.CompactSupport
import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Compact spatial tests of the full free wave

Compact support of the test permits time differentiation of C¹ fields and
spatial integration by parts for C² fields. The Kirchhoff solution
therefore satisfies the tested homogeneous wave equation for arbitrary C³
initial displacement and C² initial velocity.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open scoped Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A compact continuous spatial test permits time differentiation of a joint
C¹ field without a global bound on the field or its derivative. -/
theorem hasDerivAt_integral_mul_spatial_test {H : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) {φ : ℝ^3 → ℝ}
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x : ℝ^3, H (s, x) * φ x)
      (∫ x : ℝ^3, fderiv ℝ H (t, x) (1, 0) * φ x) t := by
  apply hasDerivAt_integral_of_locally_uniform_compact_support (f := fun s x ↦ H (s, x) * φ x)
    (D := fun s x ↦ fderiv ℝ H (s, x) (1, 0) * φ x) (μ := volume)
    (I := univ) isOpen_univ hφs.isCompact (hH.continuous.mul (hφ.comp continuous_snd)).continuousOn
    (((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (hφ.comp continuous_snd)).continuousOn
  · intro s _ x
    simpa only [Function.comp_def, id_eq] using
      (((hH.differentiable one_ne_zero (s, x)).hasFDerivAt).comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))).mul_const (φ x)
  · intro s _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  · exact mem_univ t

private theorem integral_laplacian_mul_test {F φ : ℝ^3 → ℝ}
    (hF : ContDiff ℝ 2 F) (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) :
    (∫ x : ℝ^3, laplacian F x * φ x) = ∫ x : ℝ^3, F x * laplacian φ x := by
  have hF1 (i : Fin 3) : ContDiff ℝ 1 (∂[i] F) := contDiff_partialDeriv_of_succ (m := 1) hF
  have hφ1 (i : Fin 3) : ContDiff ℝ 1 (∂[i] φ) := contDiff_partialDeriv_of_succ (m := 1) hφ
  have hiF (i : Fin 3) : Integrable (fun x ↦ (∂[i] ∂[i] F) x * φ x) :=
    (((hF1 i).continuous_partialDeriv i).mul hφ.continuous).integrable_of_hasCompactSupport
      hφs.mul_left
  have hiφ (i : Fin 3) : Integrable (fun x ↦ F x * (∂[i] ∂[i] φ) x) :=
    (hF.continuous.mul ((hφ1 i).continuous_partialDeriv i)).integrable_of_hasCompactSupport
      ((hφs.partialDeriv i).partialDeriv i).mul_left
  simp only [laplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hiF i), integral_finsetSum _ (fun i _ ↦ hiφ i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc
    _ = ∫ x : ℝ^3, φ x * (∂[i] ∂[i] F) x := by simp only [mul_comm]
    _ = -(∫ x : ℝ^3, (∂[i] φ) x * (∂[i] F) x) :=
      integral_mul_partialDeriv_eq_neg i (hφ.of_le (by norm_num)) (hF1 i) hφs
    _ = ∫ x : ℝ^3, (∂[i] ∂[i] φ) x * F x := by
      rw [integral_mul_partialDeriv_eq_neg i (hφ1 i) (hF.of_le (by norm_num))
        (hφs.partialDeriv i), neg_neg]
    _ = _ := by simp only [mul_comm]

/-- The full free wave has the second time derivative prescribed by
the spatially tested homogeneous PDE. Only the test needs compact support. -/
theorem hasDerivAt_deriv_integral_cauchyFreeField {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, cauchyFreeField g h (s, x) * φ x))
      (∫ x : ℝ^3, cauchyFreeField g h (t, x) * laplacian φ x) t := by
  let H := cauchyFreeField g h
  let D : ℝ × ℝ^3 → ℝ := fun p ↦ fderiv ℝ H p (1, 0)
  have hH : ContDiff ℝ 2 H :=
    (contDiff_two_kirchhoffFormula hg hh).comp (contDiff_timeSpaceCons_uncurry 3)
  have hD : ContDiff ℝ 1 D :=
    (hH.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hd (s : ℝ) (x : ℝ^3) : HasDerivAt (fun b ↦ H (b, x)) (D (s, x)) s := by
    simpa only [Function.comp_def, id_eq] using
      ((hH.differentiable (by norm_num) (s, x)).hasFDerivAt).comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have he (x : ℝ^3) : fderiv ℝ D (t, x) (1, 0) = laplacian (fun y ↦ H (t, y)) x := by
    have htime : deriv (fun s ↦ H (s, x)) = fun s ↦ D (s, x) := funext (fun s ↦ (hd s x).deriv)
    have hsecond := (((hD.differentiable one_ne_zero (t, x)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv
    simp only [Function.comp_def, id_eq] at hsecond
    have hw := waveOperator_kirchhoffFormula hg hh
      (p := timeSpaceCons t x) (by simpa using ht)
    rw [waveOperator_timeSpaceCons (contDiff_two_kirchhoffFormula hg hh)] at hw
    change deriv (deriv (fun s ↦ H (s, x))) t - laplacian (fun y ↦ H (t, y)) x = 0 at hw
    rw [htime, hsecond] at hw
    exact sub_eq_zero.mp hw
  have hfirst : deriv (fun s ↦ ∫ x : ℝ^3, H (s, x) * φ x) = fun s ↦ ∫ x : ℝ^3, D (s, x) * φ x :=
    funext (fun s ↦ (hasDerivAt_integral_mul_spatial_test
      (hH.of_le (by norm_num)) hφ.continuous hφs s).deriv)
  change HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, H (s, x) * φ x)) _ t
  rw [hfirst]
  apply (hasDerivAt_integral_mul_spatial_test hD hφ.continuous hφs t).congr_deriv
  simp_rw [he]
  exact integral_laplacian_mul_test (hH.comp (contDiff_const.prodMk contDiff_id)) hφ hφs

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
