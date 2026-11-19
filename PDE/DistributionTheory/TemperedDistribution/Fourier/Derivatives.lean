/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.LpSpace
public import PDE.DistributionTheory.TemperedDistribution.Lp
public import PDE.DistributionTheory.TemperateGrowth.Products

/-!
# Fourier multipliers for iterated derivatives

Every directional derivative contributes the factor `2πi ⟪ξ, v⟫` in Mathlib's
Fourier convention. This holds for tempered distributions, so the `L²` consequence
requires only the input and the specified derivative to have `L²` representatives.
-/

@[expose] public noncomputable section

open FourierTransform LineDeriv MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F]

section Distribution

variable [NormedSpace ℂ F]

/-- Fourier transformation turns a finite word of directional derivatives into the
product of its linear symbols. The directions need not form a basis. -/
theorem fourier_iteratedLineDerivOp_eq {k : ℕ} (m : Fin k → E) (T : 𝓢'(E, F)) :
    𝓕 (∂^{m} T) =
      smulLeftCLM F
        (fun ξ ↦ ∏ j, (2 * Real.pi * Complex.I) * (inner ℝ ξ (m j) : ℂ)) (𝓕 T) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, fourier_lineDerivOp_eq, ih]
    have hhead : (fun ξ ↦ (inner ℝ ξ (m 0) : ℂ)).HasTemperateGrowth := by fun_prop
    have htail : (fun ξ ↦ ∏ j : Fin k,
        (2 * Real.pi * Complex.I) * (inner ℝ ξ (Fin.tail m j) : ℂ)).HasTemperateGrowth :=
      by fun_prop
    change ((2 * Real.pi * Complex.I : ℂ) •
      smulLeftCLM F (fun ξ ↦ (inner ℝ ξ (m 0) : ℂ)))
        (smulLeftCLM F _ (𝓕 T)) = _
    rw [← smulLeftCLM_smul hhead,
      smulLeftCLM_smulLeftCLM_apply htail (by fun_prop)]
    congr 2
    funext ξ
    simp only [Fin.prod_univ_succ, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _

/-- Differentiating a Fourier transform corresponds to multiplication of the original
distribution by the negative linear symbols. This identity allows polynomial moments
to be handled without assuming lower-order moments are square-integrable. -/
theorem iteratedLineDerivOp_fourier_eq {k : ℕ} (m : Fin k → E) (T : 𝓢'(E, F)) :
    ∂^{m} (𝓕 T) =
      𝓕 (smulLeftCLM F
        (fun ξ ↦ ∏ j, -(2 * Real.pi * Complex.I) * (inner ℝ ξ (m j) : ℂ)) T) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, ih, lineDerivOp_fourier_eq]
    congr 1
    have hhead : (fun ξ ↦ (inner ℝ ξ (m 0) : ℂ)).HasTemperateGrowth := by fun_prop
    have htail : (fun ξ ↦ ∏ j : Fin k,
        -(2 * Real.pi * Complex.I) * (inner ℝ ξ (Fin.tail m j) : ℂ)).HasTemperateGrowth :=
      by fun_prop
    change ((-(2 * Real.pi * Complex.I) : ℂ) •
      smulLeftCLM F (fun ξ ↦ (inner ℝ ξ (m 0) : ℂ)))
        (smulLeftCLM F _ T) = _
    rw [← smulLeftCLM_smul hhead,
      smulLeftCLM_smulLeftCLM_apply htail (by fun_prop)]
    congr 2
    funext ξ
    simp only [Fin.prod_univ_succ, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _

end Distribution

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An iterated derivative between `L²` classes is equivalent to the almost-everywhere
Fourier multiplier identity. No intermediate derivative is assumed to lie in `L²`. -/
theorem iteratedLineDerivOp_eq_iff_fourier {k : ℕ} (m : Fin k → E)
    (u v : Lp F 2 (volume : Measure E)) :
    ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F)) ↔
      (fun ξ ↦ (∏ j, (2 * Real.pi * Complex.I) * (inner ℝ ξ (m j) : ℂ)) •
        (𝓕 u : Lp F 2 (volume : Measure E)) ξ) =ᵐ[volume]
          (𝓕 v : Lp F 2 (volume : Measure E)) := by
  rw [← (fourierCLE ℂ 𝓢'(E, F)).injective.eq_iff]
  simp only [fourierCLE_apply, fourier_iteratedLineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq]
  exact Lp.smulLeft_toTemperedDistribution_eq_iff (by fun_prop)

/-- A derivative of the `L²` Fourier transform is represented by `v` exactly when
the polynomially weighted input agrees with the inverse transform of `v`. -/
theorem iteratedLineDerivOp_fourier_eq_iff {k : ℕ} (m : Fin k → E)
    (u v : Lp F 2 (volume : Measure E)) :
    ∂^{m} (𝓕 (u : 𝓢'(E, F))) = (v : 𝓢'(E, F)) ↔
      (fun ξ ↦ (∏ j, -(2 * Real.pi * Complex.I) * (inner ℝ ξ (m j) : ℂ)) • u ξ)
        =ᵐ[volume] (𝓕⁻ v : Lp F 2 (volume : Measure E)) := by
  rw [iteratedLineDerivOp_fourier_eq,
    ← (fourierCLE ℂ 𝓢'(E, F)).symm.injective.eq_iff]
  simp only [fourierCLE_symm_apply, fourierInv_fourier_eq,
    Lp.fourierInv_toTemperedDistribution_eq]
  exact Lp.smulLeft_toTemperedDistribution_eq_iff (by fun_prop)

end TemperedDistribution
