/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.QuadraticAsymptotic
public import PDE.Analysis.SpecialFunctions.Gaussian.Quadratic
import CAS.ExactTactic

/-!
# Determinant and sign normalization of the quadratic leading term

The product of the one-dimensional Fresnel coefficients records the absolute
determinant and the sum of the signs of the eigenvalues. Orthogonal change of
variables then gives the leading asymptotic for any invertible symmetric matrix.

`tendsto_integral_matrix_quadratic` is Lemma 2 of Evans, §4.5.3(b), for a nonsingular
symmetric matrix, with error `o(1)` in place of `O(ε)`. As in step 2 of his proof, the product
of the one-dimensional coefficients gives `|det A|^(-1/2)` and the signature phase, and a
rotation reduces the general case to the diagonal one.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 2, (41), p. 221, and step 2 of its
  proof, p. 222. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- Multiplying a real coefficient by a positive scalar preserves its sign. -/
theorem sign_div_two (r : ℝ) : Real.sign (r / 2) = Real.sign r := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [Real.sign_of_neg hr, Real.sign_of_neg (div_neg_of_neg_of_pos hr (by norm_num))]
  · simp
  · rw [Real.sign_of_pos hr, Real.sign_of_pos (div_pos hr (by norm_num))]

/-- The product Fresnel coefficient has the determinant magnitude and spectral sign. -/
theorem diagonalFresnel_half (eig : Fin n → ℝ) :
    diagonalFresnel (fun i ↦ eig i / 2) =
      ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt |∏ i, eig i| : ℝ) *
        Complex.exp ((Real.pi / 4 * ∑ i, Real.sign (eig i) : ℝ) * I) := by
  have hroot (r : ℝ) : Real.pi / |r / 2| = 2 * Real.pi / |r| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_div_eq_mul_div]
    congr 1
    cas
  simp only [diagonalFresnel, hroot, sign_div_two, Finset.prod_mul_distrib]
  rw [← Complex.ofReal_prod, ← Real.sqrt_prod Finset.univ
    (fun i _ ↦ div_nonneg (by positivity) (abs_nonneg (eig i)))]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.abs_prod, Real.sqrt_div' _ (abs_nonneg _)]
  have hpow : Real.sqrt ((2 * Real.pi) ^ n) = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (by positivity)]
    congr 1
    cas
  rw [hpow, ← Complex.exp_sum]
  congr 2
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

/-- Orthogonal diagonalization gives the leading term for an arbitrary
nondegenerate real symmetric quadratic form and a smooth compact amplitude. -/
theorem tendsto_integral_matrix_quadratic
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    {a : ℝ^n → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) :
    Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
      ∫ x : ℝ^n, Complex.exp
        ((inner ℝ x (Matrix.toEuclideanLin A x) / 2 / ε ^ 2 : ℝ) * I) * a x)
      (𝓝[>] 0) (𝓝 (
        ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt |A.det| : ℝ) *
          Complex.exp ((Real.pi / 4 * ∑ i, Real.sign (hA.eigenvalues i) : ℝ) * I) *
            a 0)) := by
  let U := hA.eigenvectorBasis.repr.symm
  have hdprod : A.det = ∏ i, hA.eigenvalues i := by
    simpa using hA.det_eq_prod_eigenvalues
  have heig : ∀ i, hA.eigenvalues i / 2 ≠ 0 := by
    intro i
    apply div_ne_zero _ (by norm_num)
    have hp : (∏ j, hA.eigenvalues j) ≠ 0 := by
      rwa [← hdprod]
    exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have h := tendsto_integral_diagonal_quadratic heig
    (ha.comp U.toContinuousLinearEquiv.contDiff)
    (hc.comp_homeomorph U.toHomeomorph)
  rw [diagonalFresnel_half, ← hdprod] at h
  simp only [Function.comp_apply, map_zero] at h
  apply h.congr
  intro ε
  congr 1
  symm
  rw [← U.measurePreserving.integral_comp U.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  rw [PDE.Analysis.inner_toEuclideanLin_eigenbasis hA]
  congr 2
  simp only [diagonalQuadratic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PDE.Analysis.StationaryPhase
