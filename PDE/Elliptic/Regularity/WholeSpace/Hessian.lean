/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Lp
public import PDE.DistributionTheory.TemperedDistribution.Sobolev

/-!
# The homogeneous L² Hessian estimate

If `u` and `f` are L² and `Δu = f` as tempered distributions, every second
directional derivative has an L² representative. Its norm is at most
`‖v‖ ‖w‖ ‖f‖₂`. No first derivative is assumed.

The estimate compares the polynomial Fourier symbols of the second derivative
and Laplacian, then applies Plancherel. It does not divide by the frequency norm.
The domain is the whole finite-dimensional real inner product space, including
dimension zero, and the target is a complex Hilbert space.
-/

@[expose] public section

open FourierTransform MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv Laplacian

namespace PDE.Elliptic.WholeSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy–Schwarz compares the second-derivative symbol with the Laplacian symbol. -/
private theorem hessian_symbol_norm_le (v w ξ : E) :
    ‖(2 * Real.pi * Complex.I : ℂ) ^ 2 *
      (Complex.ofReal (inner ℝ ξ w) * Complex.ofReal (inner ℝ ξ v))‖ ≤
      (‖v‖ * ‖w‖) *
        ‖Complex.ofReal (-(2 * Real.pi) ^ 2) * Complex.ofReal (‖ξ‖ ^ 2)‖ := by
  have hc : ‖(2 * Real.pi * Complex.I : ℂ) ^ 2‖ = (2 * Real.pi) ^ 2 := by
    norm_num [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  simp only [norm_mul, hc, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_sq]
  calc
    (2 * Real.pi) ^ 2 * (|inner ℝ ξ w| * |inner ℝ ξ v|) ≤
        (2 * Real.pi) ^ 2 * ((‖ξ‖ * ‖w‖) * (‖ξ‖ * ‖v‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_real_inner_le_norm ξ w) (abs_real_inner_le_norm ξ v)
          (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (sq_nonneg _)
    _ = (‖v‖ * ‖w‖) * ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) := by ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A whole-space L² solution of `Δu = f` has a second distributional derivative
in directions `w`, then `v`, with norm at most `‖v‖ ‖w‖ ‖f‖₂`. The derivative
representative is constructed from the equation. The Fourier normalization cancels
in this homogeneous estimate; zero directions and dimension zero are allowed. -/
theorem exists_lp_second_derivative_norm_le_of_laplacian
    (u f : Lp F 2 (volume : Measure E))
    (hΔ : Δ (u : 𝓢'(E, F)) = (f : 𝓢'(E, F))) (v w : E) :
    ∃ D : Lp F 2 (volume : Measure E),
      ∂_{v} (∂_{w} (u : 𝓢'(E, F))) = (D : 𝓢'(E, F)) ∧
        ‖D‖ ≤ ‖v‖ * ‖w‖ * ‖f‖ := by
  obtain ⟨D, hD⟩ := exists_lp_second_derivative_of_laplacian u f hΔ v w
  let gv : E → ℂ := fun ξ ↦ Complex.ofReal (inner ℝ ξ v)
  let gw : E → ℂ := fun ξ ↦ Complex.ofReal (inner ℝ ξ w)
  let a : E → ℂ := fun ξ ↦ Complex.ofReal (‖ξ‖ ^ 2)
  have hgv : gv.HasTemperateGrowth := by dsimp only [gv]; fun_prop
  have hgw : gw.HasTemperateGrowth := by dsimp only [gw]; fun_prop
  have ha : a.HasTemperateGrowth := by dsimp only [a]; fun_prop
  have hDF : smulLeftCLM F
      ((2 * Real.pi * Complex.I : ℂ) ^ 2 • (gw * gv))
        (𝓕 u : Lp F 2 volume) = (𝓕 D : Lp F 2 volume) := by
    rw [smulLeftCLM_smul (hgw.mul hgv)]
    change (2 * Real.pi * Complex.I : ℂ) ^ 2 •
      smulLeftCLM F (gw * gv) (𝓕 u : Lp F 2 volume) = (𝓕 D : Lp F 2 volume)
    have hFourier := congrArg (fun T : 𝓢'(E, F) ↦ 𝓕 T) hD
    simp only [fourier_lineDerivOp_eq, map_smul, smul_smul, ← pow_two,
      Lp.fourier_toTemperedDistribution_eq] at hFourier
    change (2 * Real.pi * Complex.I : ℂ) ^ 2 •
      smulLeftCLM F gv (smulLeftCLM F gw (𝓕 u : Lp F 2 volume)) =
        (𝓕 D : Lp F 2 volume) at hFourier
    rw [smulLeftCLM_smulLeftCLM_apply hgw hgv] at hFourier
    exact hFourier
  have hfF : smulLeftCLM F (Complex.ofReal (-(2 * Real.pi) ^ 2) • a)
      (𝓕 u : Lp F 2 volume) = (𝓕 f : Lp F 2 volume) := by
    rw [smulLeftCLM_smul ha]
    change Complex.ofReal (-(2 * Real.pi) ^ 2) •
      smulLeftCLM F a (𝓕 u : Lp F 2 volume) = (𝓕 f : Lp F 2 volume)
    calc
      _ = 𝓕 (Δ (u : 𝓢'(E, F))) := by
        rw [laplacian_eq_fourierMultiplierCLM,
          ← Complex.coe_smul (-(2 * Real.pi) ^ 2), fourier_smul,
          fourierMultiplierCLM_apply, fourier_fourierInv_eq,
          Lp.fourier_toTemperedDistribution_eq]
      _ = _ := by rw [hΔ, Lp.fourier_toTemperedDistribution_eq]
  have hgD : (((2 * Real.pi * Complex.I : ℂ) ^ 2 • (gw * gv)) :
      E → ℂ).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).smul (hgw.mul hgv)
  have hgf : ((Complex.ofReal (-(2 * Real.pi) ^ 2) • a) :
      E → ℂ).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).smul ha
  have hDae := (Lp.smulLeft_toTemperedDistribution_eq_iff hgD).1 hDF
  have hfae := (Lp.smulLeft_toTemperedDistribution_eq_iff hgf).1 hfF
  refine ⟨D, hD, ?_⟩
  rw [← Lp.norm_fourier_eq D, ← Lp.norm_fourier_eq f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hDae, hfae] with ξ hξD hξf
  rw [← hξD, ← hξf]
  have hbound := mul_le_mul_of_nonneg_right (hessian_symbol_norm_le v w ξ)
    (norm_nonneg ((𝓕 u : Lp F 2 volume) ξ))
  simpa only [Pi.smul_apply, Pi.mul_apply, norm_smul, norm_mul, gv, gw, a, mul_assoc] using hbound

end PDE.Elliptic.WholeSpace
