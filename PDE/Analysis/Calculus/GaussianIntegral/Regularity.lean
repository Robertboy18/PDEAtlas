/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import PDE.Analysis.Calculus.GaussianIntegral.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth dependence of Gaussian integrals on their parameters

Integrating `exp (-a ‖y‖² + ⟪y,b⟫)` against a continuous amplitude of polynomial
growth gives a jointly smooth function of `(a,b)` for `a > 0`. Differentiation
multiplies the amplitude by the linear exponent functional. Its quadratic growth
preserves the class of amplitudes, so induction gives every order.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace PDE.Analysis.GaussianIntegral

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem continuous_exp_smul (A : ℝ^n → F) (hA : Continuous A)
    (p : ℝ × ℝ^n) :
    Continuous (fun y ↦ Real.exp (exponentCLM y p) • A y) :=
  (Real.continuous_exp.comp
    (continuous_exponentCLM.clm_apply continuous_const)).smul hA

private theorem exists_integrable_bound_exp_smul
    (A : ℝ^n → F) {C : ℝ} (k : ℕ)
    (hA : ∀ y, ‖A y‖ ≤ C * (1 + ‖y‖ ^ 2) ^ k)
    (p : ℝ × ℝ^n) (hp : 0 < p.1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ bound : ℝ^n → ℝ, Integrable bound ∧
      ∀ q ∈ Metric.ball p ε, ∀ y,
        ‖Real.exp (exponentCLM y q) • A y‖ ≤ bound y := by
  obtain ⟨ε, a, B, hε, ha, hB, hb⟩ := exists_local_gaussian_bound p hp
  refine ⟨ε, hε, fun y ↦ (B * C) *
    ((1 + ‖y‖ ^ 2) ^ k * Real.exp (-a * ‖y‖ ^ 2)),
    (integrable_polynomial_gaussian a ha k).const_mul (B * C), ?_⟩
  intro q hq y
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (exponentCLM y q) * ‖A y‖ ≤
        (B * Real.exp (-a * ‖y‖ ^ 2)) * (C * (1 + ‖y‖ ^ 2) ^ k) :=
      mul_le_mul (hb q hq y) (hA y) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem derivative_amplitude_bound (A : ℝ^n → F)
    {C : ℝ} (k : ℕ)
    (hA : ∀ y, ‖A y‖ ≤ C * (1 + ‖y‖ ^ 2) ^ k) (y : ℝ^n) :
    ‖(exponentCLM y).smulRight (A y)‖ ≤
      (2 * C) * (1 + ‖y‖ ^ 2) ^ (k + 1) := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  calc
    ‖exponentCLM y‖ * ‖A y‖ ≤
        (2 * (1 + ‖y‖ ^ 2)) * (C * (1 + ‖y‖ ^ 2) ^ k) :=
      mul_le_mul (norm_exponentCLM_le y) (hA y) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Positive quadratic decay makes a polynomially growing amplitude integrable. -/
theorem integrable_exp_smul (A : ℝ^n → F) (hA : Continuous A)
    {C : ℝ} (k : ℕ)
    (hbound : ∀ y, ‖A y‖ ≤ C * (1 + ‖y‖ ^ 2) ^ k)
    (p : ℝ × ℝ^n) (hp : 0 < p.1) :
    Integrable (fun y ↦ Real.exp (exponentCLM y p) • A y) := by
  obtain ⟨ε, hε, bound, hb, hdom⟩ :=
    exists_integrable_bound_exp_smul A k hbound p hp
  exact hb.mono' (continuous_exp_smul A hA p).aestronglyMeasurable
    (ae_of_all _ (hdom p (Metric.mem_ball_self hε)))

/-- The derivative falls entirely on the Gaussian, even for a merely continuous amplitude. -/
theorem hasFDerivAt_integral_exp_smul (A : ℝ^n → F) (hA : Continuous A)
    {C : ℝ} (k : ℕ)
    (hbound : ∀ y, ‖A y‖ ≤ C * (1 + ‖y‖ ^ 2) ^ k)
    (p : ℝ × ℝ^n) (hp : 0 < p.1) :
    HasFDerivAt (fun q : ℝ × ℝ^n ↦ ∫ y, Real.exp (exponentCLM y q) • A y)
      (∫ y, Real.exp (exponentCLM y p) • (exponentCLM y).smulRight (A y)) p := by
  let D : ℝ^n → (ℝ × ℝ^n) →L[ℝ] F :=
    fun y ↦ (exponentCLM y).smulRight (A y)
  have hD : Continuous D :=
    isBoundedBilinearMap_smulRight.continuous.comp (continuous_exponentCLM.prodMk hA)
  obtain ⟨ε, hε, bound, hb, hdom⟩ :=
    exists_integrable_bound_exp_smul D (k + 1)
      (derivative_amplitude_bound A k hbound) p hp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q y ↦ Real.exp (exponentCLM y q) • A y)
    (F' := fun q y ↦ Real.exp (exponentCLM y q) • D y)
    (s := Metric.ball p ε) (bound := bound) (Metric.ball_mem_nhds p hε)
  · exact Filter.Eventually.of_forall fun q ↦
      (continuous_exp_smul A hA q).aestronglyMeasurable
  · exact integrable_exp_smul A hA k hbound p hp
  · exact (continuous_exp_smul D hD p).aestronglyMeasurable
  · exact ae_of_all _ fun y q hq ↦ hdom q hq y
  · exact hb
  · apply ae_of_all
    intro y q _
    convert ((exponentCLM y).hasFDerivAt.exp).smul_const (A y) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [D, smul_smul, mul_comm]

/-- Gaussian integrals with continuous polynomially growing amplitudes have every
joint finite derivative on the positive-rate half-space. -/
theorem contDiffOn_integral_exp_smul_nat [CompleteSpace F]
    (A : ℝ^n → F) (hA : Continuous A) {C : ℝ} (k : ℕ)
    (hbound : ∀ y, ‖A y‖ ≤ C * (1 + ‖y‖ ^ 2) ^ k) (m : ℕ) :
    ContDiffOn ℝ m
      (fun p : ℝ × ℝ^n ↦ ∫ y, Real.exp (exponentCLM y p) • A y)
      {p | 0 < p.1} := by
  induction m generalizing F k C with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    intro p hp
    exact (hasFDerivAt_integral_exp_smul A hA k hbound p hp).continuousAt.continuousWithinAt
  | succ m ih =>
    let D : ℝ^n → (ℝ × ℝ^n) →L[ℝ] F :=
      fun y ↦ (exponentCLM y).smulRight (A y)
    have hD : Continuous D :=
      isBoundedBilinearMap_smulRight.continuous.comp (continuous_exponentCLM.prodMk hA)
    have hopen : IsOpen {p : ℝ × ℝ^n | 0 < p.1} :=
      isOpen_lt continuous_const continuous_fst
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hopen]
    refine ⟨fun p hp ↦
      (hasFDerivAt_integral_exp_smul A hA k hbound p hp).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (ih D hD (k + 1)
      (derivative_amplitude_bound A k hbound)).congr
    intro p hp
    exact (hasFDerivAt_integral_exp_smul A hA k hbound p hp).fderiv

/-- A polynomially growing continuous amplitude has a jointly smooth Gaussian transform
for every positive quadratic rate. No derivatives of the amplitude are required. -/
theorem contDiffOn_integral_exp_smul [CompleteSpace F]
    (A : ℝ^n → F) (hA : Continuous A) {C : ℝ} (k : ℕ)
    (hbound : ∀ y, ‖A y‖ ≤ C * (1 + ‖y‖ ^ 2) ^ k) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ^n ↦ ∫ y, Real.exp (exponentCLM y p) • A y)
      {p | 0 < p.1} :=
  contDiffOn_infty.mpr fun m ↦ contDiffOn_integral_exp_smul_nat A hA k hbound m

end PDE.Analysis.GaussianIntegral
