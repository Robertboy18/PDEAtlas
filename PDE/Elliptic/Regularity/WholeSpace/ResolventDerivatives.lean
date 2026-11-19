/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.WholeSpace.Resolvent

/-!
# L² estimates for second derivatives of the Bessel resolvent

The solution of `u - (2π)⁻² Δu = f` has an L² second derivative in each pair
of directions. Its norm is at most `(2π)² ‖v‖ ‖w‖ ‖f‖₂`. The proof constructs
the derivative from a bounded Fourier symbol and identifies its distribution.

The domain is a finite-dimensional real inner product space; the target is a
complex Hilbert space. No derivative representative or derivative bound is assumed.
-/

@[expose] public noncomputable section

open FourierTransform MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv

namespace PDE.Elliptic.WholeSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem resolvent_hessian_symbol_bound (v w x : E) :
    ‖Complex.ofReal (inner ℝ x v * inner ℝ x w / (1 + ‖x‖ ^ 2))‖ ≤ ‖v‖ * ‖w‖ := by
  have hd : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  calc
    |inner ℝ x v| * |inner ℝ x w| ≤ (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) :=
      mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm x w)
        (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖v‖ * ‖w‖) * ‖x‖ ^ 2 := by ring
    _ ≤ (‖v‖ * ‖w‖) * (1 + ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem resolvent_hessian_symbol_temperate (v w : E) :
    (fun x : E ↦
      Complex.ofReal (inner ℝ x v * inner ℝ x w / (1 + ‖x‖ ^ 2))).HasTemperateGrowth := by
  have h : (fun x : E ↦ Complex.ofReal
      (inner ℝ x v * inner ℝ x w * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ))).HasTemperateGrowth := by
    fun_prop
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using h

variable [MeasurableSpace E] [BorelSpace E]

private theorem resolvent_hessian_symbol_memLp (v w : E) (μ : Measure E) :
    MemLp (fun x : E ↦
      Complex.ofReal (inner ℝ x v * inner ℝ x w / (1 + ‖x‖ ^ 2))) ∞ μ :=
  memLp_top_of_bound (resolvent_hessian_symbol_temperate v w).1.continuous.aestronglyMeasurable
    (‖v‖ * ‖w‖) (Filter.Eventually.of_forall (resolvent_hessian_symbol_bound v w))

variable [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The second derivative of the whole-space Bessel resolvent has an L²
representative with bound `(2π)² ‖v‖ ‖w‖ ‖f‖₂`. Derivatives are distributional,
with the outer derivative in direction `v`. The factor comes from Mathlib's
Fourier convention; zero directions and dimension zero are allowed. -/
theorem exists_lp_second_derivative_besselResolventL2
    (v w : E) (f : Lp F 2 (volume : Measure E)) :
    ∃ g : Lp F 2 (volume : Measure E),
      (g : 𝓢'(E, F)) =
        ∂_{v} (∂_{w} (besselResolventL2 E F f : 𝓢'(E, F))) ∧
      ‖g‖ ≤ (2 * Real.pi) ^ 2 * ‖v‖ * ‖w‖ * ‖f‖ := by
  let q : E → ℂ := fun x ↦
    Complex.ofReal (inner ℝ x v * inner ℝ x w / (1 + ‖x‖ ^ 2))
  have hq : q.HasTemperateGrowth := resolvent_hessian_symbol_temperate v w
  have hmem : MemLp q ∞ (volume : Measure E) :=
    resolvent_hessian_symbol_memLp v w volume
  let m : Lp ℂ ∞ (volume : Measure E) := hmem.toLp q
  have hm : ‖m‖ ≤ ‖v‖ * ‖w‖ := by
    dsimp only [m]
    rw [Lp.norm_toLp, eLpNorm_exponent_top hmem.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (eLpNormEssSup_le_of_ae_bound
        (Filter.Eventually.of_forall (resolvent_hessian_symbol_bound v w)))
  let z : Lp F 2 (volume : Measure E) := PDE.Analysis.Fourier.fourierMultiplierL2 m f
  have hz : (z : 𝓢'(E, F)) = fourierMultiplierCLM F q (f : 𝓢'(E, F)) :=
    PDE.Analysis.Fourier.fourierMultiplierL2_toTemperedDistribution hq hmem f
  have hr : (fun x : E ↦
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ))).HasTemperateGrowth := by
    fun_prop
  have hv : (fun x : E ↦ Complex.ofReal (inner ℝ x v)).HasTemperateGrowth := by
    fun_prop
  have hw : (fun x : E ↦ Complex.ofReal (inner ℝ x w)).HasTemperateGrowth := by
    fun_prop
  have hderiv :
      ∂_{v} (∂_{w} (besselResolventL2 E F f : 𝓢'(E, F))) =
        (2 * Real.pi * Complex.I : ℂ) ^ 2 • (z : 𝓢'(E, F)) := by
    rw [hz, besselResolventL2_toTemperedDistribution]
    simp only [besselPotential, show (-2 : ℝ) / 2 = -1 by norm_num,
      lineDeriv_eq_fourierMultiplierCLM, map_smul, smul_smul]
    rw [fourierMultiplierCLM_fourierMultiplierCLM_apply hr hw,
      fourierMultiplierCLM_fourierMultiplierCLM_apply (hr.mul hw) hv, ← pow_two]
    apply congrArg (fun s : E → ℂ ↦
      (2 * Real.pi * Complex.I : ℂ) ^ 2 • fourierMultiplierCLM F s (f : 𝓢'(E, F)))
    funext x
    dsimp only [q, Pi.mul_apply]
    simp only [Real.rpow_neg_one, Complex.ofReal_mul,
      Complex.ofReal_inv, div_eq_mul_inv]
    ring
  refine ⟨(2 * Real.pi * Complex.I : ℂ) ^ 2 • z, ?_, ?_⟩
  · calc
      (((2 * Real.pi * Complex.I : ℂ) ^ 2 • z : Lp F 2 volume) : 𝓢'(E, F)) =
          (2 * Real.pi * Complex.I : ℂ) ^ 2 • (z : 𝓢'(E, F)) :=
        (Lp.toTemperedDistributionCLM F volume 2).map_smul _ _
      _ = _ := hderiv.symm
  · have hc : ‖(2 * Real.pi * Complex.I : ℂ) ^ 2‖ = (2 * Real.pi) ^ 2 := by
      norm_num [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    have hzbound : ‖z‖ ≤ (‖v‖ * ‖w‖) * ‖f‖ :=
      (PDE.Analysis.Fourier.norm_fourierMultiplierL2_apply_le m f).trans
        (mul_le_mul_of_nonneg_right hm (norm_nonneg f))
    rw [norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left hzbound (sq_nonneg _)).trans_eq (by ring)

end PDE.Elliptic.WholeSpace
