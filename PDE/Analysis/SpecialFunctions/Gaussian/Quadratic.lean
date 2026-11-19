/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian integrals of quadratic forms

Orthogonal diagonalization reduces a symmetric quadratic form to a product of
scalar Gaussian integrals. Positive definiteness identifies the resulting product
with the determinant normalization and proves integrability. The dimension may be zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory Matrix
open scoped BigOperators

variable {n : ℕ}

/-- A diagonal Gaussian factors into the one-dimensional Gaussian integrals.
The identity also uses the Bochner zero convention when a coefficient is nonpositive. -/
theorem integral_gaussian_diagonal (eig : Fin n → ℝ) :
    (∫ x : ℝ^n, Real.exp (-∑ i, eig i / 2 * (x i) ^ 2)) =
      ∏ i, Real.sqrt (2 * Real.pi / eig i) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i (x : ℝ) ↦ Real.exp (-(eig i / 2 * x ^ 2)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (fun x : ℝ ↦ Real.exp (-(eig i / 2 * x ^ 2))) =
      (fun x ↦ Real.exp (-(eig i / 2) * x ^ 2)) by ext x; congr 1; ring,
    integral_gaussian]
  congr 1
  ring

/-- An orthonormal eigenbasis diagonalizes the quadratic form of a symmetric matrix. -/
theorem inner_toEuclideanLin_eigenbasis {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (y : ℝ^n) :
    inner ℝ (hA.eigenvectorBasis.repr.symm y)
      (Matrix.toEuclideanLin A (hA.eigenvectorBasis.repr.symm y)) =
        ∑ i, hA.eigenvalues i * (y i) ^ 2 := by
  let b := hA.eigenvectorBasis
  have heig (i : Fin n) : Matrix.toEuclideanLin A (b i) =
      hA.eigenvalues i • b i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hmap : Matrix.toEuclideanLin A (b.repr.symm y) =
      b.repr.symm (WithLp.toLp 2 (fun i ↦ hA.eigenvalues i * y i)) := by
    rw [← b.sum_repr_symm y]
    simp only [map_sum, map_smul, heig, smul_smul]
    rw [← b.sum_repr_symm]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  change inner ℝ (b.repr.symm y) (Matrix.toEuclideanLin A (b.repr.symm y)) = _
  rw [hmap, b.repr.symm.inner_map_map]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An orthogonal change of variables expresses the Gaussian integral through the eigenvalues. -/
theorem integral_gaussian_quadratic_prod {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    (∫ x : ℝ^n,
      Real.exp (-(inner ℝ x (Matrix.toEuclideanLin A x)) / 2)) =
        ∏ i, Real.sqrt (2 * Real.pi / hA.eigenvalues i) := by
  rw [← hA.eigenvectorBasis.repr.symm.measurePreserving.integral_comp
    hA.eigenvectorBasis.repr.symm.toHomeomorph.measurableEmbedding]
  simp only [inner_toEuclideanLin_eigenbasis hA]
  convert integral_gaussian_diagonal hA.eigenvalues using 1
  congr 1
  ext x
  congr 1
  rw [neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Gaussian integral of a positive-definite quadratic form is determined by its determinant.
The empty determinant and empty product include dimension zero. -/
theorem integral_gaussian_quadratic {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    (∫ x : ℝ^n,
      Real.exp (-(inner ℝ x (Matrix.toEuclideanLin A x)) / 2)) =
        Real.sqrt ((2 * Real.pi) ^ n / A.det) := by
  rw [integral_gaussian_quadratic_prod hA.isHermitian,
    ← Real.sqrt_prod Finset.univ (fun i _ ↦ div_nonneg (by positivity)
      (hA.eigenvalues_pos i).le)]
  congr 1
  have hdet : A.det = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    hdet]

/-- The positive determinant makes the computed Gaussian integral nonzero. -/
theorem integrable_gaussian_quadratic {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    Integrable (fun x : ℝ^n ↦
      Real.exp (-(inner ℝ x (Matrix.toEuclideanLin A x)) / 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussian_quadratic hA]
  apply ne_of_gt
  exact Real.sqrt_pos.mpr (div_pos (pow_pos (by positivity) _) hA.det_pos)

/-- The determinant normalization in the conventional Laplace notation. -/
theorem integral_gaussian_quadratic_rpow {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    (∫ x : ℝ^n,
      Real.exp (-(inner ℝ x (Matrix.toEuclideanLin A x)) / 2)) =
        (2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt A.det := by
  rw [integral_gaussian_quadratic hA, Real.sqrt_div' _ hA.det_pos.le]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (by positivity)]
  congr 1
  ring

end PDE.Analysis
