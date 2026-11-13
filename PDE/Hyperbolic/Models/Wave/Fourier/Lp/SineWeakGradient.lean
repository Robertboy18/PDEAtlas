/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.DistributionTheory.TemperedDistribution.Sobolev.Fourier
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Evolution

/-!
# Weak spatial gradients of the physical sine evolution

The Fourier multiplier of each coordinate derivative is bounded uniformly
in time. Plancherel constructs an L2 weak derivative for arbitrary
L2 velocity, including zero frequency and the closed initial time.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal

namespace WaveEquation.Fourier

/-- Each coordinate gradient multiplier of the sine evolution is bounded by one,
uniformly in time and including zero frequency. -/
theorem norm_coordinate_mul_sineKernel_le {n : ℕ} (i : Fin n) (ξ : ℝ^n) (t : ℝ) :
    ‖(2 * Real.pi * Complex.I) * (ξ i : ℂ)‖ * |sineKernel (2 * Real.pi * ‖ξ‖) t| ≤ 1 := by
  have hcoord : |ξ i| ≤ ‖ξ‖ := PiLp.norm_apply_le ξ i
  have hpos : 0 ≤ 2 * Real.pi := by positivity
  calc
    _ = (2 * Real.pi * |ξ i|) * |sineKernel (2 * Real.pi * ‖ξ‖) t| := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_of_nonneg Real.pi_pos.le, mul_one, Real.norm_eq_abs]
    _ ≤ (2 * Real.pi * ‖ξ‖) * |sineKernel (2 * Real.pi * ‖ξ‖) t| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoord hpos) (abs_nonneg _)
    _ = |(2 * Real.pi * ‖ξ‖) * sineKernel (2 * Real.pi * ‖ξ‖) t| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hpos (norm_nonneg ξ))]
    _ = |Real.sin (2 * Real.pi * ‖ξ‖ * t)| := by rw [frequency_mul_sineKernel]
    _ ≤ 1 := Real.abs_sin_le_one _

/-- Arbitrary L2 velocity gives L2 weak spatial derivatives of its
physical sine evolution, each bounded by the velocity norm at every time. -/
theorem exists_weakDerivative_sineEvolution_norm_le {n : ℕ} (i : Fin n)
    (t : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ∃ v : Lp ℂ 2 (volume : Measure (ℝ^n)),
      SobolevSpace.HasComplexWeakDerivativeOn univ [i] (sineEvolution t u) v ∧ ‖v‖ ≤ ‖u‖ := by
  let z := sineEvolution t u
  let m : ℝ^n → ℂ := fun ξ ↦ (2 * Real.pi * Complex.I) * (ξ i : ℂ) * (𝓕 z) ξ
  have hFourier : (𝓕 z : Lp ℂ 2 (volume : Measure (ℝ^n))) =ᵐ[volume]
      fun ξ ↦ sineKernel (2 * Real.pi * ‖ξ‖) t • (𝓕 u : Lp ℂ 2 volume) ξ := by
    change (𝓕 (𝓕⁻ (sinePropagator _ t (𝓕 u))) : Lp ℂ 2 volume) =ᵐ[volume] _
    rw [fourier_fourierInv_eq]
    exact sinePropagator_coeFn _ t (𝓕 u)
  have hb : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ ‖(𝓕 u : Lp ℂ 2 volume) ξ‖ := by
    filter_upwards [hFourier] with ξ hξ
    dsimp only [m]
    rw [hξ, norm_mul, norm_smul, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_coordinate_mul_sineKernel_le i ξ t)
  have hm : MemLp m 2 volume := (Lp.memLp (𝓕 u)).of_le (by
    dsimp only [m]
    exact (by fun_prop : Measurable (fun ξ : ℝ^n ↦
      (2 * Real.pi * Complex.I) * (ξ i : ℂ))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (𝓕 z))) hb
  refine ⟨𝓕⁻ (hm.toLp m), ?_, ?_⟩
  · apply (SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier [i] z _).mpr
    rw [fourier_fourierInv_eq]
    change (fun ξ ↦ (∏ j : Fin 1, (2 * Real.pi * Complex.I) *
      (ξ ([i].get j) : ℂ)) * (𝓕 z : Lp ℂ 2 volume) ξ) =ᵐ[volume] hm.toLp m
    simpa only [Fin.prod_univ_one, List.get_cons_zero] using hm.coeFn_toLp.symm
  · have hn : ‖hm.toLp m‖ ≤ ‖(𝓕 u : Lp ℂ 2 volume)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hm.coeFn_toLp, hb] with ξ hξ hbound
      rwa [hξ]
    have he : ‖𝓕⁻ (hm.toLp m)‖ = ‖hm.toLp m‖ := by
      simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ (hm.toLp m))).symm
    rw [he]
    exact hn.trans_eq (Lp.norm_fourier_eq u)

end WaveEquation.Fourier
