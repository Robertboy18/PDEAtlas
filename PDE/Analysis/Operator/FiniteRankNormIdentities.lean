/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Operator.FiniteRankNorms
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# The equalities of Remark 8 for finite-rank operators

For a finite-rank operator `T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ` on a real inner product space,
`PDE.Analysis.Operator.FiniteRankNorms` bounds `‖T f‖²` and `|⟪f, T f⟫|` by spectral norms of
matrices made from Gram matrices. Here we prove that both bounds are sharp, which are the
equalities of Remark 8 of Hou, Wang and Yang: `‖T‖² = ‖C^{1/2} D C^{1/2}‖` with `C` and `D` the
Gram matrices of `a` and `b`, and `‖(T + T*) / 2‖ = ‖W^{1/2} K W^{1/2}‖` with `W` the Gram matrix
of the two families side by side and `K = ½ [[0, 1], [1, 0]]`. We also read these spectral norms
on the real spectrum, as the greatest `|λ|` and as the largest eigenvalue.

Everything holds in every real inner product space and for all finite families. The statements
with the adjoint `T*` need completeness, and the ones with `IsGreatest` need a nonempty index
type, because the spectrum of a matrix on an empty index type is empty. Mathlib's
`spectralRadius` is not used: the spectral radius of the paper is read as the greatest `|λ|` on
the real spectrum, and no lemma here identifies the two. Remark 8 takes the supremum of
`|⟪f, T f⟫|` over the unit sphere; here it is the supremum of `|⟪T f, f⟫| / ‖f‖²` over all `f`
(`norm_symmetricPart_eq_iSup_rayleighQuotient`). The bound `λ_max(C^{1/2} D C^{1/2}) ≤ tr(C D)` of
Remark 8 is proved for the operator (`norm_finiteRank_apply_sq_le_trace`) and not restated for
the matrix.

## Main results

* `norm_le_of_abs_inner_le`: `‖T‖ ≤ t` for a symmetric operator with `|⟪f, T f⟫| ≤ t ‖f‖²` for
  every `f`. `norm_symmetricPart_le_of_abs_inner_le`, `abs_inner_le_norm_symmetricPart`: the
  norm of the symmetric part of a bounded operator is the least `t ≥ 0` with this property.
* `l2_opNorm_le_of_abs_quadForm_le`: `‖M‖ ≤ t` for a symmetric real matrix with
  `|βᵀ M β| ≤ t |β|²` for every `β`, the converse of `abs_dotProduct_mulVec_le_l2_opNorm`.
* `l2_opNorm_sqrt_mul_mul_sqrt_le`: if `|(W α)ᵀ B (W α)| ≤ t αᵀ W α` for every `α`, then
  `‖W^{1/2} B W^{1/2}‖ ≤ t`, the converse of `abs_gram_quadForm_le_l2_opNorm`.
* `norm_finiteRank_sq`, `norm_symmetricPart_finiteRank`: the two equalities.
* `isGreatest_norm_spectrum_of_transpose_eq`, `isGreatest_spectrum_of_posSemidef`: the spectral
  norm of a symmetric real matrix is the greatest `|λ|` on its real spectrum, and the spectral
  norm of a positive semidefinite real matrix is its largest eigenvalue.
* `isGreatest_norm_symmetricPart_finiteRank`, `isGreatest_norm_finiteRank_sq`: the two
  equalities in the form of the paper, with `ρ(W^{1/2} K W^{1/2})` and
  `λ_max(C^{1/2} D C^{1/2})`.

## How it works

Both bounds read `|cᵀ B c| ≤ ‖S B S‖ ‖f‖²`, where `c` collects the pairings of `f` with a family
`w`, `W` is the Gram matrix of `w` and `S = W^{1/2}`. Sharpness is the converse for matrices. The
matrix `S B S` is symmetric, so its norm is the supremum of `|βᵀ S B S β| / |β|²`, and
`βᵀ S B S β = (S β)ᵀ B (S β)`. The entries of `S β` are the pairings of `β` with the rows of `S`,
whose Gram matrix is `S Sᵀ = W` (`exists_gram_eq_mul_transpose`). So the two-sided bound for
pairings, `abs_pairing_quadForm_le_of_gram`, used in Euclidean space for the rows of `S`, turns
the inequality for `W` into `|(S β)ᵀ B (S β)| ≤ t |β|²`. The operator supplies the matrix
inequality with its own norm as `t`: for `f = ∑ₖ αₖ wₖ`, `W α` collects the pairings of `f` and
`αᵀ W α = ‖f‖²`. With `w = a` and `B = D` this reads `(C α)ᵀ D (C α) = ‖T f‖² ≤ ‖T‖² ‖f‖²`; with
the two families side by side and `B = K` it reads `(W α)ᵀ K (W α) = ⟪f, T f⟫`. The statements
with `IsGreatest` come from Mathlib's
`IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Remark 8.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped Matrix RealInnerProductSpace

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

section Operators

/-- The Rayleigh quotient of a bounded operator on a real inner product space is
`⟪f, T f⟫ / ‖f‖²`. -/
theorem rayleighQuotient_eq_inner_div (T : X →L[ℝ] X) (f : X) :
    T.rayleighQuotient f = ⟪f, T f⟫ / ‖f‖ ^ 2 := by
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real]
  rw [real_inner_comm f (T f)]

/-- If `|⟪f, T f⟫| ≤ t ‖f‖²` at one `f`, with `t ≥ 0`, then the Rayleigh quotient of `T` at `f`
is at most `t` in absolute value. -/
theorem abs_rayleighQuotient_le_of_abs_inner_le (T : X →L[ℝ] X) {t : ℝ} (ht : 0 ≤ t) {f : X}
    (h : |⟪f, T f⟫| ≤ t * ‖f‖ ^ 2) : |T.rayleighQuotient f| ≤ t := by
  rw [rayleighQuotient_eq_inner_div, abs_div, abs_of_nonneg (sq_nonneg ‖f‖)]
  exact div_le_of_le_mul₀ (sq_nonneg ‖f‖) ht h

/-- If the Rayleigh quotient of `T` at `f` is at most `t` in absolute value, then
`|⟪f, T f⟫| ≤ t ‖f‖²`. -/
theorem abs_inner_le_of_abs_rayleighQuotient_le (T : X →L[ℝ] X) {t : ℝ} {f : X}
    (h : |T.rayleighQuotient f| ≤ t) : |⟪f, T f⟫| ≤ t * ‖f‖ ^ 2 := by
  by_cases hf : f = 0
  · simp [hf]
  · have hpos : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) 2
    rw [rayleighQuotient_eq_inner_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at h
    exact h

/-- **The norm of a symmetric operator from its quadratic form.** If `T` is symmetric and
`|⟪f, T f⟫| ≤ t ‖f‖²` for every `f`, with `t ≥ 0`, then `‖T‖ ≤ t`. The norm of a symmetric
operator is the supremum of the absolute value of its Rayleigh quotient. -/
theorem norm_le_of_abs_inner_le (T : X →L[ℝ] X) (hT : (T : X →ₗ[ℝ] X).IsSymmetric) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ f, |⟪f, T f⟫| ≤ t * ‖f‖ ^ 2) : ‖T‖ ≤ t :=
  (ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT).trans_le
    (ciSup_le fun f ↦ abs_rayleighQuotient_le_of_abs_inner_le T ht (h f))

/-- **The symmetric part from above.** For a bounded operator `T` on a real Hilbert space, if
`|⟪f, T f⟫| ≤ t ‖f‖²` for every `f`, with `t ≥ 0`, then `‖(T + T*) / 2‖ ≤ t`. -/
theorem norm_symmetricPart_le_of_abs_inner_le [CompleteSpace X] (T : X →L[ℝ] X) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ f, |⟪f, T f⟫| ≤ t * ‖f‖ ^ 2) :
    ‖(2⁻¹ : ℝ) • (T + ContinuousLinearMap.adjoint T)‖ ≤ t :=
  (norm_symmetricPart_eq_iSup_rayleighQuotient T).trans_le
    (ciSup_le fun f ↦ abs_rayleighQuotient_le_of_abs_inner_le T ht (h f))

/-- **The symmetric part from below.** For a bounded operator `T` on a real Hilbert space,
`|⟪f, T f⟫| ≤ ‖(T + T*) / 2‖ ‖f‖²` for every `f`. -/
theorem abs_inner_le_norm_symmetricPart [CompleteSpace X] (T : X →L[ℝ] X) (f : X) :
    |⟪f, T f⟫| ≤ ‖(2⁻¹ : ℝ) • (T + ContinuousLinearMap.adjoint T)‖ * ‖f‖ ^ 2 :=
  abs_inner_le_of_abs_rayleighQuotient_le T
    ((le_ciSup T.bddAbove_rayleighQuotient f).trans_eq
      (norm_symmetricPart_eq_iSup_rayleighQuotient T).symm)

/-- For a bounded operator between real seminormed spaces, if `‖T f‖² ≤ t ‖f‖²` for every `f`, with
`t ≥ 0`, then `‖T‖² ≤ t`. -/
theorem norm_sq_le_of_norm_apply_sq_le {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ f, ‖T f‖ ^ 2 ≤ t * ‖f‖ ^ 2) : ‖T‖ ^ 2 ≤ t := by
  have hle : ‖T‖ ≤ √t := by
    refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg t) fun f ↦ ?_
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg f)) |>.2
    rw [mul_pow, Real.sq_sqrt ht]
    exact h f
  calc
    ‖T‖ ^ 2 ≤ √t ^ 2 := pow_le_pow_left₀ (norm_nonneg T) hle 2
    _ = t := Real.sq_sqrt ht

end Operators

section Matrices

/-- A real Gram matrix is symmetric. -/
theorem transpose_gram {κ : Type*} (w : κ → X) : (Matrix.gram ℝ w)ᵀ = Matrix.gram ℝ w := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.isHermitian_gram ℝ w

/-- The matrix `K = ½ [[0, 1], [1, 0]]` of Remark 8 of Hou, Wang and Yang is symmetric. -/
theorem transpose_swapHalf (ι : Type*) [DecidableEq ι] : (swapHalf ι)ᵀ = swapHalf ι := by
  rw [swapHalf, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_smul,
    Matrix.transpose_one]

open scoped MatrixOrder Matrix.Norms.L2Operator Classical in
/-- The square root `CFC.sqrt W` of a real matrix is symmetric. No hypothesis on `W` is needed,
because `CFC.sqrt W` is positive semidefinite by `CFC.sqrt_nonneg`. -/
theorem transpose_sqrt {κ : Type*} [Fintype κ] (W : Matrix κ κ ℝ) :
    (CFC.sqrt W)ᵀ = CFC.sqrt W := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)).isHermitian

open scoped MatrixOrder Matrix.Norms.L2Operator Classical in
/-- For a symmetric real matrix `B`, the matrix `W^{1/2} B W^{1/2}` is symmetric. -/
theorem transpose_sqrt_mul_mul_sqrt {κ : Type*} [Fintype κ] (W : Matrix κ κ ℝ)
    {B : Matrix κ κ ℝ} (hB : Bᵀ = B) :
    (CFC.sqrt W * B * CFC.sqrt W)ᵀ = CFC.sqrt W * B * CFC.sqrt W := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, transpose_sqrt W, hB, ← Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- **The spectral norm of a symmetric matrix from its quadratic form.** If the real matrix `M`
is symmetric and `|βᵀ M β| ≤ t |β|²` for every `β`, with `t ≥ 0`, then `‖M‖ ≤ t`. The operator
of `M` on Euclidean space is symmetric with quadratic form `βᵀ M β`, so this is
`norm_le_of_abs_inner_le`. It is the converse of `abs_dotProduct_mulVec_le_l2_opNorm`. -/
theorem l2_opNorm_le_of_abs_quadForm_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℝ} (hM : Mᵀ = M) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ β : κ → ℝ, |β ⬝ᵥ M *ᵥ β| ≤ t * (β ⬝ᵥ β)) : ‖M‖ ≤ t := by
  have hT : (Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ κ).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := M)).mpr
      ((Matrix.conjTranspose_eq_transpose_of_trivial M).trans hM)
  refine (Matrix.cstar_norm_def M).trans_le
    (norm_le_of_abs_inner_le (Matrix.toEuclideanCLM (𝕜 := ℝ) M) hT ht fun x ↦ ?_)
  rw [Matrix.inner_toEuclideanCLM, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact h (WithLp.ofLp x)

/-- **Every matrix `S Sᵀ` is a Gram matrix.** The rows of a real matrix `S`, as vectors of
Euclidean space, have Gram matrix `S Sᵀ`, and their pairings with a vector `β` are the entries
of `S β`. -/
theorem exists_gram_eq_mul_transpose {κ μ : Type*} [Fintype μ] (S : Matrix κ μ ℝ) :
    ∃ w : κ → EuclideanSpace ℝ μ, Matrix.gram ℝ w = S * Sᵀ ∧
      ∀ (β : μ → ℝ) (k : κ), ⟪w k, WithLp.toLp 2 β⟫ = (S *ᵥ β) k := by
  refine ⟨fun k ↦ WithLp.toLp 2 (S k), Matrix.ext fun k l ↦ ?_, fun β k ↦ ?_⟩
  · rw [Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, star_trivial]
    exact dotProduct_comm (S l) (S k)
  · rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
    exact dotProduct_comm β (S k)

end Matrices

section Pairings

variable {κ : Type*} [Fintype κ]

/-- **Quadratic forms through a factor.** Let `S` and `B` be real matrices. If
`|(S Sᵀ α)ᵀ B (S Sᵀ α)| ≤ t αᵀ S Sᵀ α` for every `α`, with `t ≥ 0`, then
`|(S β)ᵀ B (S β)| ≤ t |β|²` for every `β`. The entries of `S β` are the pairings of `β` with the
rows of `S`, whose Gram matrix is `S Sᵀ`, so this is `abs_pairing_quadForm_le_of_gram` in
Euclidean space. -/
theorem abs_quadForm_mulVec_le_of_mul_transpose {μ : Type*} [Fintype μ] (S : Matrix κ μ ℝ)
    (B : Matrix κ κ ℝ) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ α : κ → ℝ,
      |((S * Sᵀ) *ᵥ α) ⬝ᵥ B *ᵥ ((S * Sᵀ) *ᵥ α)| ≤ t * (α ⬝ᵥ (S * Sᵀ) *ᵥ α))
    (β : μ → ℝ) : |(S *ᵥ β) ⬝ᵥ B *ᵥ (S *ᵥ β)| ≤ t * (β ⬝ᵥ β) := by
  obtain ⟨w, hgram, hpair⟩ := exists_gram_eq_mul_transpose S
  have key := abs_pairing_quadForm_le_of_gram w B ht (fun α ↦ by
    rw [hgram]
    exact h α) (WithLp.toLp 2 β)
  have hc : (fun k ↦ ⟪w k, WithLp.toLp 2 β⟫) = S *ᵥ β := funext fun k ↦ hpair β k
  rw [hc, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial] at key
  exact key

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The spectral norm from a matrix inequality.** Let `W` be a positive semidefinite real
matrix with square root `S`, and let `B` be symmetric. If `|(W α)ᵀ B (W α)| ≤ t αᵀ W α` for
every `α`, with `t ≥ 0`, then `‖S B S‖ ≤ t`. This is the converse of
`abs_gram_quadForm_le_l2_opNorm`. The quadratic form of `S B S` at `β` is `(S β)ᵀ B (S β)`, and
`S Sᵀ = W`, so `abs_quadForm_mulVec_le_of_mul_transpose` bounds it by `t |β|²`. -/
theorem l2_opNorm_sqrt_mul_mul_sqrt_le [DecidableEq κ] {W : Matrix κ κ ℝ} (hW : W.PosSemidef)
    {B : Matrix κ κ ℝ} (hB : Bᵀ = B) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ α : κ → ℝ, |(W *ᵥ α) ⬝ᵥ B *ᵥ (W *ᵥ α)| ≤ t * (α ⬝ᵥ W *ᵥ α)) :
    ‖CFC.sqrt W * B * CFC.sqrt W‖ ≤ t := by
  have hSt := transpose_sqrt W
  have hSS : CFC.sqrt W * CFC.sqrt W = W :=
    CFC.sqrt_mul_sqrt_self W (Matrix.nonneg_iff_posSemidef.mpr hW)
  refine l2_opNorm_le_of_abs_quadForm_le (transpose_sqrt_mul_mul_sqrt W hB) ht fun β ↦ ?_
  have hform : β ⬝ᵥ (CFC.sqrt W * B * CFC.sqrt W) *ᵥ β =
      (CFC.sqrt W *ᵥ β) ⬝ᵥ B *ᵥ (CFC.sqrt W *ᵥ β) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec β,
      ← Matrix.mulVec_transpose, hSt]
  rw [hform]
  refine abs_quadForm_mulVec_le_of_mul_transpose (CFC.sqrt W) B ht (fun α ↦ ?_) β
  rw [hSt, hSS]
  exact h α

end Pairings

section FiniteRank

variable {ι : Type*} [Fintype ι]

/-- On a combination `f = ∑ⱼ αⱼ aⱼ` of the family `a`, `‖T f‖² = (C α)ᵀ D (C α)`, with `C` and
`D` the Gram matrices of `a` and `b`. -/
theorem norm_finiteRank_apply_sum_smul_sq (a : ι → X) (b : ι → Y) (α : ι → ℝ) :
    ‖finiteRank a b (∑ j, α j • a j)‖ ^ 2 =
      (Matrix.gram ℝ a *ᵥ α) ⬝ᵥ Matrix.gram ℝ b *ᵥ (Matrix.gram ℝ a *ᵥ α) := by
  have hc : (fun j ↦ ⟪a j, ∑ l, α l • a l⟫) = Matrix.gram ℝ a *ᵥ α :=
    funext fun k ↦ inner_sum_smul_eq_gram_mulVec a α k
  rw [norm_finiteRank_apply_sq, hc]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The norm of a finite-rank operator** (Hou–Wang–Yang, Remark 8). For
`T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ`, with `C` and `D` the Gram matrices of `a` and `b`,
`‖T‖² = ‖C^{1/2} D C^{1/2}‖`, the spectral norm. The bound from above is
`norm_finiteRank_apply_sq_le_l2_opNorm`. From below, `(C α)ᵀ D (C α) = ‖T f‖² ≤ ‖T‖² ‖f‖²` for
`f = ∑ⱼ αⱼ aⱼ`, and `l2_opNorm_sqrt_mul_mul_sqrt_le` applies with `t = ‖T‖²`. -/
theorem norm_finiteRank_sq [DecidableEq ι] (a : ι → X) (b : ι → Y) :
    ‖finiteRank a b‖ ^ 2 =
      ‖CFC.sqrt (Matrix.gram ℝ a) * Matrix.gram ℝ b * CFC.sqrt (Matrix.gram ℝ a)‖ := by
  refine le_antisymm (norm_sq_le_of_norm_apply_sq_le (finiteRank a b) (norm_nonneg _)
    (norm_finiteRank_apply_sq_le_l2_opNorm a b)) ?_
  refine l2_opNorm_sqrt_mul_mul_sqrt_le (Matrix.posSemidef_gram ℝ a) (transpose_gram b)
    (sq_nonneg _) fun α ↦ ?_
  rw [← norm_finiteRank_apply_sum_smul_sq a b α, ← norm_sq_sum_smul_eq_gram a α, abs_sq,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((finiteRank a b).le_opNorm _) 2

/-- On a combination `f = ∑ₖ αₖ wₖ` of the two families `a`, `b` side by side,
`⟪f, T f⟫ = (W α)ᵀ K (W α)`, with `W` their Gram matrix and `K` the matrix `swapHalf`. -/
theorem inner_finiteRank_apply_sum_smul [DecidableEq ι] (a b : ι → X) (α : ι ⊕ ι → ℝ) :
    ⟪∑ k, α k • Sum.elim a b k, finiteRank a b (∑ k, α k • Sum.elim a b k)⟫ =
      (Matrix.gram ℝ (Sum.elim a b) *ᵥ α) ⬝ᵥ swapHalf ι *ᵥ
        (Matrix.gram ℝ (Sum.elim a b) *ᵥ α) := by
  have hc : (fun k ↦ ⟪Sum.elim a b k, ∑ l, α l • Sum.elim a b l⟫) =
      Matrix.gram ℝ (Sum.elim a b) *ᵥ α :=
    funext fun k ↦ inner_sum_smul_eq_gram_mulVec (Sum.elim a b) α k
  rw [inner_finiteRank_apply_eq_swapHalf, hc]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The symmetric part of a finite-rank operator** (Hou–Wang–Yang, Remark 8). For
`T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ` on a real Hilbert space, with `W` the Gram matrix of the two families side
by side and `K` the matrix `swapHalf`, `‖(T + T*) / 2‖ = ‖W^{1/2} K W^{1/2}‖`, the spectral
norm. The bound from above is `abs_inner_finiteRank_le_l2_opNorm`. From below,
`(W α)ᵀ K (W α) = ⟪f, T f⟫` for `f = ∑ₖ αₖ wₖ`, which is at most `‖(T + T*) / 2‖ ‖f‖²` in
absolute value, and `l2_opNorm_sqrt_mul_mul_sqrt_le` applies. -/
theorem norm_symmetricPart_finiteRank [DecidableEq ι] [CompleteSpace X] (a b : ι → X) :
    ‖(2⁻¹ : ℝ) • (finiteRank a b + ContinuousLinearMap.adjoint (finiteRank a b))‖ =
      ‖CFC.sqrt (Matrix.gram ℝ (Sum.elim a b)) * swapHalf ι *
        CFC.sqrt (Matrix.gram ℝ (Sum.elim a b))‖ := by
  refine le_antisymm (norm_symmetricPart_le_of_abs_inner_le (finiteRank a b) (norm_nonneg _)
    (abs_inner_finiteRank_le_l2_opNorm a b)) ?_
  refine l2_opNorm_sqrt_mul_mul_sqrt_le (Matrix.posSemidef_gram ℝ (Sum.elim a b))
    (transpose_swapHalf ι) (norm_nonneg _) fun α ↦ ?_
  rw [← inner_finiteRank_apply_sum_smul a b α, ← norm_sq_sum_smul_eq_gram (Sum.elim a b) α]
  exact abs_inner_le_norm_symmetricPart (finiteRank a b) _

end FiniteRank

section Spectrum

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The spectral norm of a symmetric matrix on its real spectrum.** For a symmetric real
matrix `M` on a nonempty index type, `‖M‖` is the greatest element of
`{|λ| : λ ∈ spectrum ℝ M}`. This is
`IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum` of Mathlib, for the isometric
functional calculus of Hermitian matrices with the `l2` operator norm. -/
theorem isGreatest_norm_spectrum_of_transpose_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] {M : Matrix κ κ ℝ} (hM : Mᵀ = M) :
    IsGreatest ((‖·‖) '' spectrum ℝ M) ‖M‖ :=
  IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) M
    (Matrix.isHermitian_iff_isSelfAdjoint.mp
      ((Matrix.conjTranspose_eq_transpose_of_trivial M).trans hM))

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The spectral norm of a positive semidefinite matrix is its largest eigenvalue.** For a
positive semidefinite real matrix `P` on a nonempty index type, `‖P‖` is the greatest element
of `spectrum ℝ P`. The spectrum is nonnegative, so the greatest `|λ|` of
`isGreatest_norm_spectrum_of_transpose_eq` is attained at `λ = ‖P‖`. By
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` of Mathlib the real spectrum is the set
of eigenvalues. -/
theorem isGreatest_spectrum_of_posSemidef {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {P : Matrix κ κ ℝ} (hP : P.PosSemidef) : IsGreatest (spectrum ℝ P) ‖P‖ := by
  have hG := isGreatest_norm_spectrum_of_transpose_eq
    ((Matrix.conjTranspose_eq_transpose_of_trivial P).symm.trans hP.isHermitian.eq)
  obtain ⟨x, hx, hxP⟩ := hG.1
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
  have hxP' : x = ‖P‖ := (Real.norm_of_nonneg hx0).symm.trans hxP
  rw [hxP'] at hx
  exact ⟨hx, fun y hy ↦ (Real.le_norm_self y).trans (hG.2 ⟨y, hy, rfl⟩)⟩

open scoped MatrixOrder Matrix.Norms.L2Operator Classical in
/-- For a positive semidefinite real matrix `B`, the matrix `W^{1/2} B W^{1/2}` is positive
semidefinite. -/
theorem posSemidef_sqrt_mul_mul_sqrt {κ : Type*} [Fintype κ]
    (W : Matrix κ κ ℝ) {B : Matrix κ κ ℝ} (hB : B.PosSemidef) :
    (CFC.sqrt W * B * CFC.sqrt W).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (conjugate_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hB) (CFC.sqrt_nonneg W))

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The symmetric part and the spectral radius** (Hou–Wang–Yang, Remark 8). For
`T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ` on a real Hilbert space and a nonempty index type, `‖(T + T*) / 2‖` is the
greatest `|λ|` over the real spectrum of `W^{1/2} K W^{1/2}`. This is how the spectral radius
`ρ(W^{1/2} K W^{1/2})` of the paper is read; Mathlib's `spectralRadius` is not used. -/
theorem isGreatest_norm_symmetricPart_finiteRank {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [CompleteSpace X] (a b : ι → X) :
    IsGreatest
      ((‖·‖) '' spectrum ℝ (CFC.sqrt (Matrix.gram ℝ (Sum.elim a b)) * swapHalf ι *
        CFC.sqrt (Matrix.gram ℝ (Sum.elim a b))))
      ‖(2⁻¹ : ℝ) • (finiteRank a b + ContinuousLinearMap.adjoint (finiteRank a b))‖ := by
  rw [norm_symmetricPart_finiteRank a b]
  exact isGreatest_norm_spectrum_of_transpose_eq
    (transpose_sqrt_mul_mul_sqrt (Matrix.gram ℝ (Sum.elim a b)) (transpose_swapHalf ι))

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The norm and the largest eigenvalue** (Hou–Wang–Yang, Remark 8). For
`T f = ∑ⱼ ⟪aⱼ, f⟫ bⱼ` and a nonempty index type, `‖T‖²` is the greatest element of the real
spectrum of `C^{1/2} D C^{1/2}`, which is `λ_max(C^{1/2} D C^{1/2})` of the paper. -/
theorem isGreatest_norm_finiteRank_sq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → X) (b : ι → Y) :
    IsGreatest
      (spectrum ℝ (CFC.sqrt (Matrix.gram ℝ a) * Matrix.gram ℝ b * CFC.sqrt (Matrix.gram ℝ a)))
      (‖finiteRank a b‖ ^ 2) := by
  rw [norm_finiteRank_sq a b]
  exact isGreatest_spectrum_of_posSemidef
    (posSemidef_sqrt_mul_mul_sqrt (Matrix.gram ℝ a) (Matrix.posSemidef_gram ℝ b))

end Spectrum

end PDE.Analysis.Operator
