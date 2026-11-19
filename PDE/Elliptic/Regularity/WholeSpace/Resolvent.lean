/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Multiplier
public import PDE.DistributionTheory.TemperedDistribution.Sobolev

/-!
# The whole-space Bessel resolvent on L²

The symbol `(1 + ‖ξ‖²)⁻¹` constructs the unique L² solution of
`u - (2π)⁻² Δu = f`. Its operator norm is at most one. The factor `(2π)⁻²`
comes from Mathlib's Fourier convention.

The solution belongs to the order-two Bessel space. No solution, first
derivative, or operator bound is assumed. The domain is the
whole finite-dimensional real inner product space, and the target may be any
complex Hilbert space. The dimension may be zero.
-/

@[expose] public noncomputable section

open FourierTransform MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap Laplacian

namespace PDE.Elliptic.WholeSpace

variable {E : Type*} [NormedAddCommGroup E]

private theorem resolvent_symbol_norm_le (x : E) :
    ‖Complex.ofReal ((1 + ‖x‖ ^ 2)⁻¹)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg ‖x‖))

variable [InnerProductSpace ℝ E]

private theorem resolvent_symbol_temperate :
    (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2)⁻¹)).HasTemperateGrowth := by
  have h : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ))).HasTemperateGrowth := by
    fun_prop
  simpa only [Real.rpow_neg_one] using h

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem resolvent_symbol_memLp :
    MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2)⁻¹)) ∞ volume :=
  memLp_top_of_bound resolvent_symbol_temperate.1.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall resolvent_symbol_norm_le)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (E F) in
/-- The L² solution operator of `I - (2π)⁻² Δ`, constructed from its bounded
Fourier symbol. -/
@[no_expose]
def besselResolventL2 :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  PDE.Analysis.Fourier.fourierMultiplierL2 ((resolvent_symbol_memLp (E := E)).toLp _)

/-- The resolvent has norm at most one on each L² input. This estimate follows
from the pointwise bound on its symbol. -/
theorem norm_besselResolventL2_apply_le (f : Lp F 2 (volume : Measure E)) :
    ‖besselResolventL2 E F f‖ ≤ ‖f‖ := by
  let m : Lp ℂ ∞ (volume : Measure E) := (resolvent_symbol_memLp (E := E)).toLp _
  have hm : ‖m‖ ≤ 1 := by
    dsimp only [m]
    rw [Lp.norm_toLp,
      eLpNorm_exponent_top (resolvent_symbol_memLp (E := E)).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (eLpNormEssSup_le_of_ae_bound
        (Filter.Eventually.of_forall resolvent_symbol_norm_le))
  change ‖PDE.Analysis.Fourier.fourierMultiplierL2 m f‖ ≤ ‖f‖
  exact (PDE.Analysis.Fourier.norm_fourierMultiplierL2_apply_le m f).trans
    (mul_le_of_le_one_left (norm_nonneg f) hm)

/-- The norm of the constructed resolvent is at most one. -/
theorem norm_besselResolventL2_le : ‖besselResolventL2 E F‖ ≤ 1 := by
  apply (besselResolventL2 E F).opNorm_le_bound (by norm_num)
  intro f
  simpa only [one_mul] using norm_besselResolventL2_apply_le f

/-- The L² resolvent represents the order-minus-two Bessel operator on the
input tempered distribution. -/
theorem besselResolventL2_toTemperedDistribution (f : Lp F 2 (volume : Measure E)) :
    (besselResolventL2 E F f : 𝓢'(E, F)) =
      besselPotential E F (-2) (f : 𝓢'(E, F)) := by
  rw [besselResolventL2, PDE.Analysis.Fourier.fourierMultiplierL2_toTemperedDistribution
    resolvent_symbol_temperate resolvent_symbol_memLp]
  simp only [besselPotential, show (-2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]

/-- Applying the order-two Bessel operator to the constructed solution returns
the forcing distribution. -/
theorem besselPotential_two_besselResolventL2 (f : Lp F 2 (volume : Measure E)) :
    besselPotential E F 2 (besselResolventL2 E F f : 𝓢'(E, F)) = (f : 𝓢'(E, F)) := by
  rw [besselResolventL2_toTemperedDistribution, besselPotential_besselPotential_apply]
  simp

/-- The constructed L² function solves the elliptic equation as an equality
of tempered distributions. -/
theorem besselResolventL2_equation (f : Lp F 2 (volume : Measure E)) :
    (besselResolventL2 E F f : 𝓢'(E, F)) -
      Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) •
        Δ (besselResolventL2 E F f : 𝓢'(E, F)) = (f : 𝓢'(E, F)) := by
  rw [← besselPotential_two_eq]
  exact besselPotential_two_besselResolventL2 f

/-- The solution has two orders of Bessel regularity, with the forcing as its
order-two Bessel representative. -/
theorem besselResolventL2_memSobolev (f : Lp F 2 (volume : Measure E)) :
    MemSobolev 2 2 (besselResolventL2 E F f : 𝓢'(E, F)) :=
  ⟨f, besselPotential_two_besselResolventL2 f⟩

/-- Any L² distributional solution of the same equation equals the constructed
resolvent. Uniqueness follows by applying the inverse Bessel operator and the
injective Lp embedding into tempered distributions. -/
theorem eq_besselResolventL2_of_equation (u f : Lp F 2 (volume : Measure E))
    (h : (u : 𝓢'(E, F)) -
      Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) • Δ (u : 𝓢'(E, F)) = (f : 𝓢'(E, F))) :
    u = besselResolventL2 E F f := by
  have hJ : besselPotential E F 2 (u : 𝓢'(E, F)) = (f : 𝓢'(E, F)) := by
    rwa [besselPotential_two_eq]
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := F) (μ := (volume : Measure E)) (p := 2))
  change (u : 𝓢'(E, F)) = (besselResolventL2 E F f : 𝓢'(E, F))
  rw [besselResolventL2_toTemperedDistribution]
  have hinverse := congrArg (besselPotential E F (-2)) hJ
  simpa using hinverse

end PDE.Elliptic.WholeSpace
