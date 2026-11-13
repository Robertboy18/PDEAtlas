/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.TriangularExponential
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
public import PDE.Common.Euclidean

/-!
# Polynomial exponential growth for real spectrum

Every complex endomorphism of a finite-dimensional inner product space with real
spectrum satisfies a polynomial bound for its imaginary-time exponential. The
proof constructs an orthonormal triangular form and uses the finite interaction
expansion. Orthonormal coordinates preserve the operator norm, so the constants do
not depend on a basis or on the separation of eigenvalues.

In dimension `m`, the degree is at most `m - 1`, including defective matrices.
The finite-sum estimate also covers dimension zero. On `0 ≤ t ≤ T`, its constants
depend only on `m` and `T`, which is the uniformity needed for matrix symbols
depending on a Fourier frequency.
-/

@[expose] public section

open NormedSpace Set
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A finite-dimensional operator with real spectrum has polynomial, rather than
exponential, growth along imaginary time. No eigenbasis is assumed. -/
theorem norm_exp_smul_le_sum_of_real_spectrum
    (T : E →L[ℂ] E) (hT : ∀ z ∈ spectrum ℂ T, z.im = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • (-Complex.I • T))‖ ≤
      ∑ k ∈ Finset.range (Module.finrank ℂ E),
        (2 * ‖T‖) ^ k * t ^ k / k.factorial := by
  classical
  have := FiniteDimensional.complete ℂ E
  let e : (E →ₗ[ℂ] E) ≃⋆ₐ[ℂ] (E →L[ℂ] E) :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }
  obtain ⟨b, hb⟩ :=
    T.toLinearMap.exists_orthonormalBasis_isUpperTriangular
  let F : (E →L[ℂ] E) ≃⋆ₐ[ℂ]
      Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    e.symm.trans (LinearMap.toMatrixOrthonormal b)
  have hmatrix : F T =
      LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap := rfl
  have hupper : (F T).IsUpperTriangular := by
    rw [hmatrix]
    exact hb
  have hreal (i : Fin (Module.finrank ℂ E)) : (F T i i).im = 0 := by
    apply hT
    rw [← AlgEquiv.spectrum_eq F T, hupper.spectrum_eq_range_diag]
    exact Set.mem_range_self i
  have hbound := Matrix.norm_exp_smul_le_sum_of_isUpperTriangular
    (F T) hupper hreal ht
  have hFnorm (S : E →L[ℂ] E) : ‖F S‖ = ‖S‖ :=
    StarAlgEquiv.norm_map F S
  have hFcont : Continuous F := (StarAlgEquiv.isometry F).continuous
  have hmap : F (exp (t • (-Complex.I • T))) =
      exp (t • (-Complex.I • F T)) := by
    rw [map_exp_of_mem_ball (𝕂 := ℂ) F hFcont _
      ((expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)]
    apply congrArg exp
    calc
      F (t • (-Complex.I • T)) = t • F (-Complex.I • T) :=
        F.toAlgEquiv.toLinearMap.map_smul_of_tower t _
      _ = t • (-Complex.I • F T) := congrArg (t • ·) (map_smul F (-Complex.I) T)
  calc
    ‖exp (t • (-Complex.I • T))‖ =
        ‖F (exp (t • (-Complex.I • T)))‖ := (hFnorm _).symm
    _ = ‖exp (t • (-Complex.I • F T))‖ := congrArg norm hmap
    _ ≤ ∑ k ∈ Finset.range (Module.finrank ℂ E),
        (2 * ‖T‖) ^ k * t ^ k / k.factorial := by
      simpa only [hFnorm] using hbound

end ContinuousLinearMap

namespace Matrix

variable {m : ℕ}

/-- The real-spectrum estimate in matrix form, using the Euclidean operator norm.
The matrix may have repeated eigenvalues and arbitrary Jordan blocks. -/
theorem norm_exp_smul_le_sum_of_real_spectrum
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ z ∈ spectrum ℂ A, z.im = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • (-Complex.I • A))‖ ≤
      ∑ k ∈ Finset.range m, (2 * ‖A‖) ^ k * t ^ k / k.factorial := by
  let F : Matrix (Fin m) (Fin m) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :=
    toEuclideanCLM (n := Fin m) (𝕜 := ℂ)
  have hT : ∀ z ∈ spectrum ℂ (F A), z.im = 0 := by
    intro z hz
    apply hA z
    rwa [AlgEquiv.spectrum_eq] at hz
  have h := ContinuousLinearMap.norm_exp_smul_le_sum_of_real_spectrum (F A) hT ht
  have hFnorm (B : Matrix (Fin m) (Fin m) ℂ) : ‖F B‖ = ‖B‖ :=
    l2_opNorm_toEuclideanCLM B
  have hFcont : Continuous F := (StarAlgEquiv.isometry F).continuous
  have hmap : F (exp (t • (-Complex.I • A))) =
      exp (t • (-Complex.I • F A)) := by
    rw [map_exp_of_mem_ball (𝕂 := ℂ) F hFcont _
      ((expSeries_radius_eq_top ℂ (Matrix (Fin m) (Fin m) ℂ)).symm ▸ edist_lt_top _ _)]
    apply congrArg exp
    calc
      F (t • (-Complex.I • A)) = t • F (-Complex.I • A) :=
        F.toAlgEquiv.toLinearMap.map_smul_of_tower t _
      _ = t • (-Complex.I • F A) := congrArg (t • ·) (map_smul F (-Complex.I) A)
  rw [← hmap, hFnorm, hFnorm] at h
  simpa only [finrank_euclideanSpace_fin] using h

/-- On a fixed nonnegative time interval the polynomial constant depends only on
time and dimension. In particular, there is no choice of eigenbasis in the bound. -/
theorem norm_exp_smul_le_polynomial_of_real_spectrum
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ z ∈ spectrum ℂ A, z.im = 0) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖exp (t • (-Complex.I • A))‖ ≤
      (∑ k ∈ Finset.range m, (2 * T) ^ k / k.factorial) *
        (1 + ‖A‖ ^ (m - 1)) := by
  have hT : 0 ≤ T := ht.trans htT
  refine (norm_exp_smul_le_sum_of_real_spectrum A hA ht).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hkm : k ≤ m - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hk)
  have hpow : ‖A‖ ^ k ≤ 1 + ‖A‖ ^ (m - 1) := by
    by_cases hAone : ‖A‖ ≤ 1
    · exact (pow_le_one₀ (norm_nonneg A) hAone).trans
        (le_add_of_nonneg_right (pow_nonneg (norm_nonneg A) _))
    · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hAone)) hkm).trans
        (le_add_of_nonneg_left zero_le_one)
  calc
    (2 * ‖A‖) ^ k * t ^ k / k.factorial
        ≤ (2 * ‖A‖) ^ k * T ^ k / k.factorial :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htT k) (by positivity))
            (by positivity)
    _ = ((2 * T) ^ k / k.factorial) * ‖A‖ ^ k := by
      simp only [mul_pow]
      ring
    _ ≤ ((2 * T) ^ k / k.factorial) * (1 + ‖A‖ ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A real-spectrum matrix symbol has a frequency-uniform polynomial bound on each
bounded nonnegative time interval. The coefficient norm estimate is derived from
its linear dependence on frequency; it is not an additional hypothesis. The
estimate includes zero spatial or matrix dimension and defective symbols. -/
theorem norm_exp_symbol_le_polynomial_of_real_spectrum
    {n : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (ξ : ℝ^n) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖exp (t • (-Complex.I • (∑ j, ξ j • A j)))‖ ≤
      (∑ k ∈ Finset.range m, (2 * T) ^ k / k.factorial) *
        (1 + ((∑ j, ‖A j‖) * ‖ξ‖) ^ (m - 1)) := by
  have hT : 0 ≤ T := ht.trans htT
  have hnorm : ‖∑ j, ξ j • A j‖ ≤ (∑ j, ‖A j‖) * ‖ξ‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    calc
      ‖ξ j • A j‖ = ‖ξ j‖ * ‖A j‖ := norm_smul _ _
      _ ≤ ‖ξ‖ * ‖A j‖ :=
        mul_le_mul_of_nonneg_right (PiLp.norm_apply_le ξ j) (norm_nonneg _)
      _ = ‖A j‖ * ‖ξ‖ := mul_comm _ _
  refine (norm_exp_smul_le_polynomial_of_real_spectrum
    (∑ j, ξ j • A j) (hA ξ) ht htT).trans ?_
  apply mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hnorm (m - 1)))
  exact Finset.sum_nonneg fun k _ ↦ by positivity

end Matrix
