/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.NewtonFrequency
public import PDE.Hyperbolic.Models.Wave.Strichartz.FourierLaplacian
public import PDE.Elliptic.Classical.Poisson.BoundedRepresentation
public import PDE.FDeriv.Laplacian.Intrinsic
public import PDE.Analysis.Integration.Convolution.Decay
import CAS.ExactTactic
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Identification of the Fourier and physical Newton potentials

The inverse-Laplacian frequency datum solves the Poisson equation.
The bounded Poisson representation identifies its real part with
physical convolution up to a constant. Decay of both potentials removes that
constant. Only the source is Schwartz and compactly supported.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter
open scoped Topology SchwartzMap

namespace WaveEquation.Strichartz

/-- The inverse Fourier Newton potential has two continuous derivatives. -/
theorem contDiff_two_fourierInv_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) :
    ContDiff ℝ 2 (𝓕⁻ (newtonFrequency F)) := by
  have hu := (Fourier.cosine_wave_regular_of_integrable_moments
    (integrable_newtonFrequency F) (integrable_norm_mul_newtonFrequency F)
    (integrable_norm_sq_mul_newtonFrequency F)).1
  let L : ℝ^3 →L[ℝ] ℝ × ℝ^3 := ContinuousLinearMap.inr ℝ ℝ (ℝ^3)
  have heq : 𝓕⁻ (newtonFrequency F) = Fourier.waveSolution (newtonFrequency F) 0 ∘ L :=
    funext fun x ↦ (Fourier.waveSolution_initial_position _ _ x).symm
  rw [heq]
  exact hu.comp L.contDiff

/-- The Newton frequency datum solves the Poisson equation with the Fourier-inverted source. -/
theorem neg_laplacian_fourierInv_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) (x : ℝ^3) :
    -Laplacian.laplacian (𝓕⁻ (newtonFrequency F) : ℝ^3 → ℂ) x = (𝓕⁻ F) x := by
  rw [Fourier.laplacian_fourierInv_of_integrable_moments
    (integrable_newtonFrequency F) (integrable_norm_mul_newtonFrequency F)
    (integrable_norm_sq_mul_newtonFrequency F)]
  have hfreq : (fun ξ ↦ -((2 * Real.pi * ‖ξ‖) ^ 2) • newtonFrequency F ξ) =ᵐ[volume]
      -(F : ℝ^3 → ℂ) := by
    filter_upwards [volume.ae_ne (0 : ℝ^3)] with ξ hξ
    simp only [neg_smul, angularFrequency_sq_smul_newtonFrequency F hξ, Pi.neg_apply]
  rw [Real.fourierInv_congr_ae hfreq, SchwartzMap.fourierInv_coe]
  simp only [Real.fourierInv_eq, Pi.neg_apply, smul_neg, integral_neg, neg_neg]

/-- The real part of the inverse Fourier Newton potential solves the real Poisson equation. -/
theorem neg_coordinate_laplacian_fourierInv_newtonFrequency (f : 𝓢(ℝ^3, ℝ)) (x : ℝ^3) :
    -PDE.laplacian (Complex.reCLM ∘
      𝓕⁻ (newtonFrequency (𝓕 (f.postcompCLM Complex.ofRealCLM)))) x = f x := by
  let fc := f.postcompCLM Complex.ofRealCLM
  let v := 𝓕⁻ (newtonFrequency (𝓕 fc))
  have hv : ContDiff ℝ 2 v := contDiff_two_fourierInv_newtonFrequency (𝓕 fc)
  rw [(Complex.reCLM.contDiff.comp hv).contDiffAt.coordinate_laplacian_eq_laplacian,
    hv.contDiffAt.laplacian_CLM_comp_left]
  change -(Laplacian.laplacian v x).re = f x
  rw [← Complex.neg_re, neg_laplacian_fourierInv_newtonFrequency, fourierInv_fourier_eq]
  rfl

/-- The normalized three-dimensional Newton potential of compact L¹ data vanishes at infinity. -/
theorem tendsto_convolution_fundamentalSolution_three {f : ℝ^3 → ℝ}
    (hf : Integrable f) (hfc : HasCompactSupport f) :
    Tendsto (convolution (PotentialTheory.fundamentalSolution 3) f
      (ContinuousLinearMap.mul ℝ ℝ)) (cocompact (ℝ^3)) (𝓝 0) := by
  let c := (4 * Real.pi)⁻¹
  have hkernel (y : ℝ^3) : PotentialTheory.fundamentalSolution 3 y = c * ‖y‖⁻¹ := by
    rw [PotentialTheory.fundamentalSolution_of_three_le (by norm_num),
      PDE.Analysis.unitBallVolume_three]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    have hc : (3 : ℝ) * (4 * Real.pi / 3) = 4 * Real.pi := by cas
    rw [hc, one_div, mul_inv]
  have heq : convolution (PotentialTheory.fundamentalSolution 3) f
      (ContinuousLinearMap.mul ℝ ℝ) = fun z : ℝ^3 ↦ ∫ y, ‖z - y‖⁻¹ • (c * f y) := by
    funext z
    rw [convolution_mul]
    simp_rw [hkernel]
    have h := integral_sub_left_eq_self (fun y : ℝ^3 ↦ ‖y‖⁻¹ * (c * f (z - y))) volume z
    simpa only [sub_sub_cancel, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h.symm
  rw [heq]
  exact MeasureTheory.tendsto_integral_norm_sub_inv_smul (hf.const_mul c) hfc.mul_left

/-- The inverse Fourier Newton potential equals the normalized physical potential.
Compact support is used only for physical Poisson representation and decay. -/
theorem re_fourierInv_newtonFrequency_eq_convolution
    (f : 𝓢(ℝ^3, ℝ)) (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) (x : ℝ^3) :
    (𝓕⁻ (newtonFrequency (𝓕 (f.postcompCLM Complex.ofRealCLM))) x).re = convolution
      (PotentialTheory.fundamentalSolution 3) f (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  let fc := f.postcompCLM Complex.ofRealCLM
  let G := newtonFrequency (𝓕 fc)
  let v := 𝓕⁻ G
  let u : ℝ^3 → ℝ := Complex.reCLM ∘ v
  let f₂ : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^3)) ℝ 2 :=
    ⟨f, f.smooth 2, hfc, Set.subset_univ _⟩
  have hv : ContDiff ℝ 2 v := contDiff_two_fourierInv_newtonFrequency (𝓕 fc)
  have hu : ContDiff ℝ 2 u := Complex.reCLM.contDiff.comp hv
  have hpoisson : ∀ y, -PDE.laplacian u y = f₂ y :=
    neg_coordinate_laplacian_fourierInv_newtonFrequency f
  have hbound : ∀ y, |u y| ≤ ∫ ξ, ‖G ξ‖ := by
    intro y
    apply (Complex.abs_re_le_norm (v y)).trans
    change ‖𝓕⁻ G y‖ ≤ _
    rw [Real.fourierInv_eq]
    exact (norm_integral_le_integral_norm _).trans (le_of_eq (by simp only [Circle.norm_smul]))
  obtain ⟨C, hC⟩ := PoissonEquation.exists_eq_fundamentalSolutionConvolution_add_const
    (by norm_num : 3 ≤ 3) f₂ hu hpoisson ⟨_, hbound⟩
  have hvlim : Tendsto v (cocompact (ℝ^3)) (𝓝 0) := by
    change Tendsto (𝓕⁻ G) _ _
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact tendsto_integral_exp_inner_smul_cocompact (fun ξ ↦ G (-ξ))
  have hulim : Tendsto u (cocompact (ℝ^3)) (𝓝 0) := by
    simpa only [map_zero] using Complex.reCLM.continuous.continuousAt.tendsto.comp hvlim
  have hnlim : Tendsto (PoissonEquation.fundamentalSolutionConvolution 3 f₂)
      (cocompact (ℝ^3)) (𝓝 0) := tendsto_convolution_fundamentalSolution_three f.integrable hfc
  have hzero : (0 : ℝ) = C := by
    apply tendsto_nhds_unique hulim
    have heq : u = fun y ↦ PoissonEquation.fundamentalSolutionConvolution 3 f₂ y + C := funext hC
    rw [heq]
    simpa only [zero_add] using hnlim.add_const C
  change u x = PoissonEquation.fundamentalSolutionConvolution 3 f₂ x
  rw [hC x, ← hzero, add_zero]

end WaveEquation.Strichartz
