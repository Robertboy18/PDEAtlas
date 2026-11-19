/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.RealSpectrumExponential.Symbol
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Exponential Fourier multipliers of linear matrix symbols

The multiplier and its time derivative use Mathlib's `2π` Fourier
normalization. Continuity and differentiation require no spectral hypothesis.
Real spectrum gives uniform polynomial bounds on every bounded signed time
interval, without eigenvectors or diagonalizability.
-/

@[expose] public noncomputable section

open NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

namespace PDE.Analysis.Fourier

variable {n m : ℕ}

/-- The exponential multiplier associated with a linear matrix symbol. -/
def symbolMultiplier (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (t : ℝ) (ξ : ℝ^n) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)
    (exp ((2 * Real.pi * t) • (-Complex.I • (∑ j, ξ j • A j))))

/-- The infinitesimal generator, with the sign and normalization of the
inverse Fourier evolution. -/
def symbolGenerator (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (ξ : ℝ^n) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (2 * Real.pi) • (-Complex.I •
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (∑ j, ξ j • A j))

/-- The multiplier is jointly continuous in time and frequency. -/
theorem continuous_symbolMultiplier (A : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    Continuous (fun p : ℝ × ℝ^n ↦
      symbolMultiplier A p.1 p.2) := by
  apply (StarAlgEquiv.isometry
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m))).continuous.comp
  apply (continuous_iff_continuousAt.mpr
    (fun Q ↦ (exp_analytic (𝕂 := ℂ) Q).continuousAt)).comp
  fun_prop

/-- The infinitesimal generator is continuous in frequency. -/
theorem continuous_symbolGenerator (A : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    Continuous (symbolGenerator A) := by
  have hM : Continuous (fun ξ : ℝ^n ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (∑ j, ξ j • A j)) := by
    apply (StarAlgEquiv.isometry
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m))).continuous.comp
    fun_prop
  exact (hM.const_smul (-Complex.I)).const_smul (2 * Real.pi)

/-- Differentiating the exponential yields multiplication by its
infinitesimal generator, including for defective matrix symbols. -/
theorem hasDerivAt_symbolMultiplier
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (ξ : ℝ^n) (t : ℝ) :
    HasDerivAt (fun u ↦ symbolMultiplier A u ξ)
      (symbolGenerator A ξ * symbolMultiplier A t ξ) t := by
  let e : Matrix (Fin m) (Fin m) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :=
    (Matrix.toEuclideanCLM.toAlgEquiv.toLinearMap.restrictScalars ℝ).toContinuousLinearMap
  have htime : HasDerivAt (fun u : ℝ ↦ 2 * Real.pi * u) (2 * Real.pi) t := by
    convert (hasDerivAt_id t).const_mul (2 * Real.pi) using 1 <;> simp
  have h := e.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const' (𝕂 := ℝ)
      (-Complex.I • (∑ j, ξ j • A j)) (2 * Real.pi * t)).scomp t htime)
  convert h using 1
  · rfl
  · dsimp only [symbolGenerator, symbolMultiplier]
    change _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)
      ((2 * Real.pi) • ((-Complex.I • (∑ j, ξ j • A j)) *
        exp ((2 * Real.pi * t) • (-Complex.I • (∑ j, ξ j • A j)))))
    have hreal (Q : Matrix (Fin m) (Fin m) ℂ) :
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) ((2 * Real.pi) • Q) =
          (2 * Real.pi) • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) Q :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)).toAlgEquiv.toLinearMap.map_smul_of_tower
        (2 * Real.pi) Q
    rw [hreal]
    simp only [map_mul, map_smul]
    apply ContinuousLinearMap.ext
    intro v
    simp only [mul_apply_eq_comp, smul_apply]

/-- The generator costs exactly one frequency power. -/
theorem norm_symbolGenerator_le
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (ξ : ℝ^n) :
    ‖symbolGenerator A ξ‖ ≤ (2 * Real.pi * ∑ j, ‖A j‖) * ‖ξ‖ := by
  have hnorm : ‖∑ j, ξ j • A j‖ ≤ (∑ j, ‖A j‖) * ‖ξ‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul, mul_comm ‖A j‖]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le ξ j) (norm_nonneg _)
  rw [symbolGenerator, norm_smul, norm_smul, norm_neg, Complex.norm_I, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
    Matrix.l2_opNorm_toEuclideanCLM]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hnorm (mul_nonneg zero_le_two Real.pi_pos.le)

/-- The exponential acting on a fixed vector has the expected time
derivative. Real differentiation retains the complex-linear operator action. -/
theorem hasDerivAt_symbolMultiplier_apply
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (ξ : ℝ^n) (v : EuclideanSpace ℂ (Fin m)) (t : ℝ) :
    HasDerivAt (fun u ↦ symbolMultiplier A u ξ v)
      (symbolGenerator A ξ (symbolMultiplier A t ξ v)) t := by
  exact ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin m)) v).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_symbolMultiplier A ξ t)

/-- Real spectrum supplies a uniform polynomial bound on bounded signed
time intervals. The constant precedes both time and frequency. -/
theorem exists_norm_symbolMultiplier_le
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    {T : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ T →
      ∀ ξ : ℝ^n,
        ‖symbolMultiplier A t ξ‖ ≤ C * (1 + ‖ξ‖ ^ (m - 1)) := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨0, le_rfl, fun t ht _ ↦ absurd ((abs_nonneg t).trans ht) (not_le.mpr hT)⟩
  obtain ⟨C, hC, hbound⟩ := Matrix.exists_norm_exp_symbol_le A hA
    (T := 2 * Real.pi * T) (by positivity)
  refine ⟨C, hC, fun t ht ξ ↦ ?_⟩
  rw [symbolMultiplier, Matrix.l2_opNorm_toEuclideanCLM]
  apply hbound
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left ht (by positivity)

end PDE.Analysis.Fourier
