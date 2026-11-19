/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Fourth-power certificates for finite-rank operators

For a finite family `v` and an involution `σ`, the operator
`A x = ∑ i, ⟪v (σ i), x⟫ • v i` is symmetric. Its positive power traces are the
traces of the matrix `X i j = ⟪v (σ i), v j⟫`. Linear independence is unnecessary.

For six vectors and the pairing `σ` that swaps `2i - 1` and `2i`, `A / 2` (`pairedCorrection`)
is the matrix `M_s` of Chen, Hou and Huang, Section 4.3, step (f), whose largest eigenvalue they
bound by the Schatten norm in (4.36), and the matrix `A` of (8.27) in their supplementary
material. They take `p = 4` and enclose the entries of `X` by interval arithmetic; here these
entries and the numerical bounds enter as hypotheses.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.3, step (f), (4.36), and Supplementary material (in the same PDF), Section 8.1, (8.27).
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace PDE.Analysis

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram matrix with rows permuted by the pairing map. -/
def pairedGram (v : ι → E) (σ : ι → ι) : Matrix ι ι ℝ :=
  (Matrix.gram ℝ v).submatrix σ id

@[simp]
theorem pairedGram_apply (v : ι → E) (σ : ι → ι) (i j : ι) :
    pairedGram v σ i j = ⟪v (σ i), v j⟫ := rfl

variable [Fintype ι]

/-- The finite sum of rank-one operators associated with a paired family. -/
def pairedRankOne (v : ι → E) (σ : ι → ι) : E →L[ℝ] E :=
  ∑ i, InnerProductSpace.rankOne ℝ (v i) (v (σ i))

/-- Half of `pairedRankOne v σ`, the normalization of the matrix `M_s` of Chen, Hou and Huang. -/
def pairedCorrection (v : ι → E) (σ : ι → ι) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • pairedRankOne v σ

@[simp]
theorem pairedRankOne_apply (v : ι → E) (σ : ι → ι) (x : E) :
    pairedRankOne v σ x = ∑ i, ⟪v (σ i), x⟫ • v i := by
  simp [pairedRankOne]

/-- The quadratic form of the correction is a sum of paired scalar products. -/
theorem inner_pairedCorrection_self (v : ι → E) (σ : ι → ι) (x : E) :
    ⟪pairedCorrection v σ x, x⟫ =
      (1 / 2 : ℝ) * ∑ i, ⟪v (σ i), x⟫ * ⟪v i, x⟫ := by
  simp [pairedCorrection, pairedRankOne_apply, real_inner_smul_left, sum_inner]

/-- The operator takes values in the span of its defining family. -/
theorem pairedRankOne_mem_span (v : ι → E) (σ : ι → ι) (x : E) :
    pairedRankOne v σ x ∈ Submodule.span ℝ (Set.range v) := by
  rw [pairedRankOne_apply]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- An involutive pairing gives a symmetric operator, including for dependent vectors. -/
theorem isSymmetric_pairedRankOne (v : ι → E) {σ : ι → ι}
    (hσ : Function.Involutive σ) : (pairedRankOne v σ).toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, pairedRankOne_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  simpa only [mul_comm] using Fintype.sum_bijective σ hσ.bijective
    (fun i ↦ ⟪v (σ i), x⟫ * ⟪v i, y⟫)
    (fun i ↦ ⟪x, v i⟫ * ⟪v (σ i), y⟫) (fun i ↦ by
      rw [hσ i, real_inner_comm (v (σ i)) x])

private def gramSynthesis (v : ι → E) : (ι → ℝ) →ₗ[ℝ] E :=
  ∑ i, (LinearMap.proj i).smulRight (v i)

private def gramAnalysis (v : ι → E) (σ : ι → ι) : E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i ↦ innerₛₗ ℝ (v (σ i))

private theorem gramSynthesis_comp_analysis (v : ι → E) (σ : ι → ι) :
    (gramSynthesis v).comp (gramAnalysis v σ) = (pairedRankOne v σ).toLinearMap := by
  ext x
  simp [gramSynthesis, gramAnalysis]

private theorem gramAnalysis_comp_synthesis [DecidableEq ι] (v : ι → E) (σ : ι → ι) :
    (gramAnalysis v σ).comp (gramSynthesis v) = (pairedGram v σ).toLin' := by
  apply LinearMap.ext
  intro x
  funext i
  simp [gramSynthesis, gramAnalysis, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    mul_comm]

section FiniteDimensional

variable [DecidableEq ι] [FiniteDimensional ℝ E]

/-- Positive power traces of the operator are computed by its paired Gram matrix.
The zeroth power is excluded because the ambient and indexing dimensions can differ. -/
theorem trace_pairedRankOne_pow_succ (v : ι → E) (σ : ι → ι) (n : ℕ) :
    LinearMap.trace ℝ E ((pairedRankOne v σ).toLinearMap ^ (n + 1)) =
      Matrix.trace (pairedGram v σ ^ (n + 1)) := by
  classical
  let S := gramSynthesis v
  let B := gramAnalysis v σ
  have hcomm : (S.comp B).comp S = S.comp (B.comp S) := LinearMap.comp_assoc _ _ _
  have hp := Module.End.commute_pow_left_of_commute hcomm n
  rw [← gramSynthesis_comp_analysis, Module.End.iterate_succ,
    ← LinearMap.comp_assoc, hp, LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc, ← Module.End.iterate_succ, gramAnalysis_comp_synthesis,
    ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]

/-- Fourth powers have the same trace without any independence assumption. -/
theorem trace_pairedRankOne_pow_four (v : ι → E) (σ : ι → ι) :
    LinearMap.trace ℝ E ((pairedRankOne v σ).toLinearMap ^ 4) =
      Matrix.trace (pairedGram v σ ^ 4) :=
  trace_pairedRankOne_pow_succ v σ 3

/-- The factor `1/16` in the fourth-power certificate is exact. -/
theorem trace_pairedCorrection_pow_four (v : ι → E) (σ : ι → ι) :
    LinearMap.trace ℝ E ((pairedCorrection v σ).toLinearMap ^ 4) =
      Matrix.trace (pairedGram v σ ^ 4) / 16 := by
  simp only [pairedCorrection, ContinuousLinearMap.toLinearMap_smul, smul_pow,
    map_smul, trace_pairedRankOne_pow_four, smul_eq_mul]
  norm_num [div_eq_mul_inv, mul_comm]

/-- The fourth-power trace of a symmetric operator is the sum of fourth powers
of its real eigenvalues. -/
theorem trace_pow_four_eq_sum_eigenvalues (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) :
    LinearMap.trace ℝ E (A ^ 4) = ∑ i, hA.eigenvalues rfl i ^ 4 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (hA.eigenvectorBasis rfl).toBasis,
    ← LinearMap.toMatrix_pow, hA.toMatrix_eigenvectorBasis]
  simp [Matrix.diagonal_pow]

/-- A fourth-power trace bound controls the norm of a symmetric operator.
The certificate is polynomial: no numerical eigenvalue computation is needed. -/
theorem norm_apply_le_of_trace_pow_four_le (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    {c : ℝ} (hc : 0 ≤ c) (htrace : LinearMap.trace ℝ E (A ^ 4) ≤ c ^ 4) (x : E) :
    ‖A x‖ ≤ c * ‖x‖ := by
  classical
  let b := hA.eigenvectorBasis rfl
  have heig (i : Fin (Module.finrank ℝ E)) : hA.eigenvalues rfl i ^ 2 ≤ c ^ 2 := by
    have hfour : hA.eigenvalues rfl i ^ 4 ≤ c ^ 4 := by
      rw [trace_pow_four_eq_sum_eigenvalues A hA] at htrace
      exact (Finset.single_le_sum (fun j _ ↦ by positivity) (Finset.mem_univ i)).trans htrace
    apply (pow_le_pow_iff_left₀ (sq_nonneg _) (sq_nonneg _) (by decide : 2 ≠ 0)).mp
    simpa only [← pow_mul] using hfour
  have hdiag (i : Fin (Module.finrank ℝ E)) :
      ⟪b i, A x⟫ = hA.eigenvalues rfl i * ⟪b i, x⟫ := by
    simpa [b, OrthonormalBasis.repr_apply_apply] using
      hA.eigenvectorBasis_apply_self_apply rfl x i
  have hsq : ‖A x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖A x‖ ^ 2 = ∑ i, ⟪b i, A x⟫ ^ 2 := (b.sum_sq_inner_right _).symm
      _ = ∑ i, hA.eigenvalues rfl i ^ 2 * ⟪b i, x⟫ ^ 2 := by simp_rw [hdiag, mul_pow]
      _ ≤ ∑ i, c ^ 2 * ⟪b i, x⟫ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (heig i) (sq_nonneg _)
      _ = c ^ 2 * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, b.sum_sq_inner_right]
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
    (by decide : 2 ≠ 0)).mp
  simpa only [mul_pow] using hsq

/-- In finite dimension, the paired Gram trace is a sufficient norm certificate. -/
theorem norm_pairedRankOne_apply_le_of_trace_le_finiteDimensional
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    {c : ℝ} (hc : 0 ≤ c) (htrace : Matrix.trace (pairedGram v σ ^ 4) ≤ c ^ 4) (x : E) :
    ‖pairedRankOne v σ x‖ ≤ c * ‖x‖ := by
  apply norm_apply_le_of_trace_pow_four_le (pairedRankOne v σ).toLinearMap
    (isSymmetric_pairedRankOne v hσ) hc
  simpa only [trace_pairedRankOne_pow_four] using htrace

end FiniteDimensional

variable [DecidableEq ι]

/-- The same polynomial certificate applies in an arbitrary real inner-product space.
Only the span of the defining vectors and the test vector enters the spectral argument. -/
theorem norm_pairedRankOne_apply_le_of_trace_le
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    {c : ℝ} (hc : 0 ≤ c) (htrace : Matrix.trace (pairedGram v σ ^ 4) ≤ c ^ 4) (x : E) :
    ‖pairedRankOne v σ x‖ ≤ c * ‖x‖ := by
  let S := Submodule.span ℝ (insert x (Set.range v))
  have : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range v).insert x)
  let w : ι → S := fun i ↦
    ⟨v i, Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i))⟩
  let y : S := ⟨x, Submodule.subset_span (Set.mem_insert x _)⟩
  have hgram : pairedGram w σ = pairedGram v σ := rfl
  have hbound := norm_pairedRankOne_apply_le_of_trace_le_finiteDimensional w hσ hc
    (hgram ▸ htrace) y
  have hvalue : ((pairedRankOne w σ y : S) : E) = pairedRankOne v σ x := by
    simp [pairedRankOne_apply, w, y]
  simpa only [← hvalue, ← Submodule.norm_coe, y] using hbound

/-- An operator-norm form of the paired Gram certificate. -/
theorem norm_pairedRankOne_le_of_trace_le
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    {c : ℝ} (hc : 0 ≤ c) (htrace : Matrix.trace (pairedGram v σ ^ 4) ≤ c ^ 4) :
    ‖pairedRankOne v σ‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc
    (norm_pairedRankOne_apply_le_of_trace_le v hσ hc htrace)

/-- Although the paired Gram matrix need not be symmetric, its fourth-power trace
is nonnegative: it is the fourth-power trace of a symmetric finite-rank operator. -/
theorem trace_pairedGram_pow_four_nonneg (v : ι → E) {σ : ι → ι}
    (hσ : Function.Involutive σ) : 0 ≤ Matrix.trace (pairedGram v σ ^ 4) := by
  let S := Submodule.span ℝ (Set.range v)
  have : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  let w : ι → S := fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  change 0 ≤ Matrix.trace (pairedGram w σ ^ 4)
  rw [← trace_pairedRankOne_pow_four,
    trace_pow_four_eq_sum_eigenvalues _ (isSymmetric_pairedRankOne w hσ)]
  exact Finset.sum_nonneg fun i _ ↦ by positivity

/-- An exact polynomial certificate for the operator normalized by `1/2`. -/
theorem norm_pairedCorrection_le_of_trace_le
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    {c : ℝ} (hc : 0 ≤ c) (htrace : Matrix.trace (pairedGram v σ ^ 4) ≤ 16 * c ^ 4) :
    ‖pairedCorrection v σ‖ ≤ c := by
  have hbound := norm_pairedRankOne_le_of_trace_le v hσ
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
    (show Matrix.trace (pairedGram v σ ^ 4) ≤ (2 * c) ^ 4 by
      simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using htrace)
  simp only [pairedCorrection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith

/-- A quadratic-form consequence suitable for energy estimates. -/
theorem abs_inner_pairedCorrection_le_of_trace_le
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    {c : ℝ} (hc : 0 ≤ c) (htrace : Matrix.trace (pairedGram v σ ^ 4) ≤ 16 * c ^ 4)
    (x : E) : |⟪pairedCorrection v σ x, x⟫| ≤ c * ‖x‖ ^ 2 := by
  calc
    |⟪pairedCorrection v σ x, x⟫| ≤ ‖pairedCorrection v σ x‖ * ‖x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖pairedCorrection v σ‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ((pairedCorrection v σ).le_opNorm x) (norm_nonneg _)
    _ ≤ (c * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_pairedCorrection_le_of_trace_le v hσ hc htrace)
          (norm_nonneg _)) (norm_nonneg _)
    _ = c * ‖x‖ ^ 2 := by rw [pow_two, mul_assoc]

/-- The explicit fourth-root bound, written using two nonnegative square roots. -/
theorem norm_pairedCorrection_le_sqrt_sqrt (v : ι → E) {σ : ι → ι}
    (hσ : Function.Involutive σ) :
    ‖pairedCorrection v σ‖ ≤
      √(√(Matrix.trace (pairedGram v σ ^ 4))) / 2 := by
  have hnonneg := trace_pairedGram_pow_four_nonneg v hσ
  have hfour : √(√(Matrix.trace (pairedGram v σ ^ 4))) ^ 4 =
      Matrix.trace (pairedGram v σ ^ 4) := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hnonneg]
  have hbound := norm_pairedRankOne_le_of_trace_le v hσ
    (Real.sqrt_nonneg (√(Matrix.trace (pairedGram v σ ^ 4)))) hfour.ge
  simp only [pairedCorrection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith

/-- The strict trace threshold in (4.36) and (8.27) gives a strict contraction. -/
theorem norm_pairedCorrection_lt_one_of_trace_lt_sixteen
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    (htrace : Matrix.trace (pairedGram v σ ^ 4) < 16) :
    ‖pairedCorrection v σ‖ < 1 := by
  have hsquare := Real.sq_sqrt (trace_pairedGram_pow_four_nonneg v hσ)
  have hroot := Real.sq_sqrt (Real.sqrt_nonneg (Matrix.trace (pairedGram v σ ^ 4)))
  have hfirst : √(Matrix.trace (pairedGram v σ ^ 4)) < 4 := by
    nlinarith [Real.sqrt_nonneg (Matrix.trace (pairedGram v σ ^ 4))]
  have hsecond : √(√(Matrix.trace (pairedGram v σ ^ 4))) < 2 := by
    nlinarith [Real.sqrt_nonneg (√(Matrix.trace (pairedGram v σ ^ 4)))]
  exact (norm_pairedCorrection_le_sqrt_sqrt v hσ).trans_lt (by linarith)

/-- A positive coercivity margin follows from the strict Gram certificate.
This is an abstract quadratic-form estimate, independent of the PDE weights. -/
theorem pairedCorrection_coercivity_of_trace_lt_sixteen
    (v : ι → E) {σ : ι → ι} (hσ : Function.Involutive σ)
    (htrace : Matrix.trace (pairedGram v σ ^ 4) < 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E,
      δ * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ⟪pairedCorrection v σ x, x⟫ := by
  let c := ‖pairedCorrection v σ‖
  have hc : c < 1 := norm_pairedCorrection_lt_one_of_trace_lt_sixteen v hσ htrace
  refine ⟨1 - c, sub_pos.mpr hc, fun x ↦ ?_⟩
  have hinner : ⟪pairedCorrection v σ x, x⟫ ≤ c * ‖x‖ ^ 2 := by
    calc
      ⟪pairedCorrection v σ x, x⟫ ≤ ‖pairedCorrection v σ x‖ * ‖x‖ :=
        real_inner_le_norm _ _
      _ ≤ (c * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((pairedCorrection v σ).le_opNorm x) (norm_nonneg _)
      _ = c * ‖x‖ ^ 2 := by rw [pow_two, mul_assoc]
  nlinarith

end

end PDE.Analysis
