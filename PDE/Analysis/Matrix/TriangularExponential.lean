/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Schur
public import PDE.Analysis.Matrix.Volterra
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Polynomial bounds for triangular matrix exponentials

Split an upper triangular matrix with real diagonal as `A = D + N`. The diagonal
evolution is unitary. For the interaction curve
`X(t) = exp(itD) exp(-itA)`, direct differentiation gives

`X'(t) = exp(itD) (-iN) exp(-itD) X(t)`.

The coefficient is strictly upper triangular, so the finite Volterra expansion
applies. Its norm is at most `2 ‖A‖`, in the Euclidean operator norm. Combining the
factorial estimates gives a polynomial of degree at most `m - 1`, also for repeated
diagonal entries and nontrivial Jordan blocks.
-/

@[expose] public section

open Set NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {m : ℕ}

/-- The imaginary exponential of a real diagonal matrix has operator norm at most
one. The inequality also covers the empty matrix. -/
private theorem norm_exp_imaginary_diagonal_le_one
    (d : Fin m → ℂ) (hd : ∀ i, (d i).im = 0) (t : ℝ) :
    ‖exp (t • (Complex.I • diagonal d))‖ ≤ 1 := by
  rw [← diagonal_smul, ← diagonal_smul, exp_diagonal, l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  simp only [Pi.coe_exp, Pi.smul_apply, Complex.real_smul, smul_eq_mul,
    ← Complex.exp_eq_exp_ℂ, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hd i,
    mul_zero, zero_mul, sub_self, Real.exp_zero, le_refl]

/-- The norm estimate for the exponential of an upper triangular matrix
with real diagonal. The bound uses its original Euclidean operator norm. -/
theorem norm_exp_smul_le_sum_of_isUpperTriangular
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsUpperTriangular)
    (hreal : ∀ i, (A i i).im = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • (-Complex.I • A))‖ ≤
      ∑ k ∈ Finset.range m, (2 * ‖A‖) ^ k * t ^ k / k.factorial := by
  classical
  by_cases hm : m = 0
  · subst m
    have hz : exp (t • (-Complex.I • A)) = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, Finset.range_zero, Finset.sum_empty, le_refl]
  have : NeZero m := ⟨hm⟩
  let D : Matrix (Fin m) (Fin m) ℂ := diagonal (fun i ↦ A i i)
  let P : Matrix (Fin m) (Fin m) ℂ := Complex.I • D
  let Q : Matrix (Fin m) (Fin m) ℂ := -Complex.I • A
  let U : C(ℝ, Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun s ↦ exp (s • P), (differentiable_exp_smul_const ℝ P).continuous⟩
  let V : C(ℝ, Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun s ↦ exp (s • Q), (differentiable_exp_smul_const ℝ Q).continuous⟩
  let W : C(ℝ, Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun s ↦ exp ((-s) • P),
      (differentiable_exp_smul_const ℝ P).continuous.comp continuous_neg⟩
  let X : C(ℝ, Matrix (Fin m) (Fin m) ℂ) := U * V
  let K : C(ℝ, Matrix (Fin m) (Fin m) ℂ) :=
    U * ContinuousMap.const ℝ (P + Q) * W
  have hinv (s : ℝ) : W s * U s = 1 := by
    change exp ((-s) • P) * exp (s • P) = 1
    rw [neg_smul, ← Matrix.exp_add_of_commute _ _ (Commute.refl (s • P)).neg_left,
      neg_add_cancel, exp_zero]
  have hX (s : ℝ) : HasDerivAt X (K s * X s) s := by
    have hu : HasDerivAt (fun r : ℝ ↦ U r) (U s * P) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) P s
    have hv : HasDerivAt (fun r : ℝ ↦ V r) (Q * V s) s :=
      hasDerivAt_exp_smul_const' (𝕂 := ℝ) Q s
    have hmul : HasDerivAt (fun r : ℝ ↦ U r * V r)
        ((U s * P) * V s + U s * (Q * V s)) s := hu.mul hv
    have hderiv : K s * X s = (U s * P) * V s + U s * (Q * V s) := by
      change (U s * (P + Q) * W s) * (U s * V s) =
        (U s * P) * V s + U s * (Q * V s)
      rw [mul_assoc (U s * (P + Q)) (W s), ← mul_assoc (W s), hinv, one_mul]
      simp only [mul_add, add_mul, mul_assoc]
    exact hmul.congr_deriv hderiv.symm
  have hstrict : ∀ s i j, j ≤ i → K s i j = 0 := by
    intro s i j hji
    have hPQ : (P + Q) i j = 0 := by
      change (Complex.I • D + -Complex.I • A) i j = 0
      rcases hji.eq_or_lt with h | h
      · subst j
        simp [D, neg_smul]
      · have hij : i ≠ j := ne_of_gt h
        simp [D, hA h, diagonal_apply_ne _ hij]
    change (exp (s • (Complex.I • D)) * (P + Q) *
      exp ((-s) • (Complex.I • D))) i j = 0
    simp only [D, ← diagonal_smul, exp_diagonal, mul_diagonal, diagonal_mul, hPQ,
      mul_zero, zero_mul]
  have hD : ‖D‖ ≤ ‖A‖ := by
    rw [l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (norm_nonneg A)]
    exact fun i ↦ spectrum.norm_le_norm_of_mem (hA.spectrum_eq_range_diag ▸ mem_range_self i)
  have hPQnorm : ‖P + Q‖ ≤ 2 * ‖A‖ := (norm_add_le _ _).trans <| by
    simp only [P, Q, norm_smul, norm_neg, Complex.norm_I, one_mul]
    linarith
  have hUnorm (s : ℝ) : ‖U s‖ ≤ 1 :=
    norm_exp_imaginary_diagonal_le_one (fun i ↦ A i i) hreal s
  have hWnorm (s : ℝ) : ‖W s‖ ≤ 1 :=
    norm_exp_imaginary_diagonal_le_one (fun i ↦ A i i) hreal (-s)
  have hKnorm (s : ℝ) : ‖K s‖ ≤ 2 * ‖A‖ := by
    have hU := hUnorm s
    have hW := hWnorm s
    calc ‖K s‖ = ‖U s * (P + Q) * W s‖ := rfl
      _ ≤ ‖U s‖ * ‖P + Q‖ * ‖W s‖ := norm_mul₃_le
      _ ≤ 1 * (2 * ‖A‖) * 1 := by gcongr
      _ = 2 * ‖A‖ := by ring
  have hX0 : X 0 = 1 := show exp ((0 : ℝ) • P) * exp ((0 : ℝ) • Q) = 1 by simp
  have hbound := norm_le_sum_of_strictUpperTriangular_hasDerivAt K X hstrict hX
    (show 0 ≤ 2 * ‖A‖ by positivity) ht (fun s _ ↦ hKnorm s)
  have hrecover : V t = W t * X t :=
    show V t = W t * (U t * V t) by rw [← mul_assoc, hinv, one_mul]
  change ‖V t‖ ≤ _
  calc ‖V t‖ ≤ ‖W t‖ * ‖X t‖ := hrecover ▸ norm_mul_le _ _
    _ ≤ ‖X t‖ := mul_le_of_le_one_left (norm_nonneg _) (hWnorm t)
    _ ≤ _ := by simpa only [hX0, norm_one, one_mul] using hbound

end Matrix
