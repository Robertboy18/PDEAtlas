/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Operator.FiniteRankCaptureCertificates
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Two-sided finite-rank capture, with constants read off Gram matrices

`PDE.Analysis.Operator.finiteRank_capture_le` bounds `Q(f, f) - ∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ` from above.
This module bounds its absolute value, as Lemmas 1 and 3 of Hou, Wang and Yang do, for every
positive semidefinite symmetric form `Q` on a real vector space and every finite family of
modes `ψ̄ⱼ`. The constants are read off matrices that a computation produces. The Gram mismatch
`ε₃` is the spectral norm of `1 - G_Q^{1/2} diag(μ)⁻¹ G_Q^{1/2}`, with `G_Q` the `Q`-Gram matrix
of the modes. The angle `ε₄` of their Lemma 2 is bounded through the Frobenius norm of
`1 - G_E`, with `G_E` the energy Gram matrix of the modes. Nothing here computes the constants
for a given family.

## Main results

* `abs_dotProduct_mulVec_le_l2_opNorm`, `abs_dotProduct_mulVec_le_frobenius`: a real quadratic
  form is bounded by the spectral norm, and by the Frobenius norm, of its matrix.
* `abs_gram_sub_sum_sq_div_le`: the matrix identity behind the Gram mismatch.
* `abs_sub_sum_sq_div_le_of_matrix`, `abs_sub_sum_sq_div_le_l2_opNorm`: the two-sided Gram
  mismatch on the span of the modes, from a matrix inequality and from the spectral norm.
  The one-sided form is `PDE.Analysis.Operator.sub_sum_sq_div_le_of_matrix`.
* `abs_projection_sub_sum_sq_div_le`: the finite-rank functional of `f` against the `Q`-energy
  of its `Q`-projection onto the span of the modes.
* `form_sq_le_of_residual_frobenius`: the angle bound with the Frobenius constant. It is
  `PDE.Analysis.Operator.form_sq_le_of_residual` with its energy hypothesis proved from the
  Gram matrix.
* `form_le_of_orthogonal_add`: the two vectors of a quasi-orthogonal splitting are bounded by
  their sum, with the factor `1 / (1 - ε₄²)`; `one_sub_sq_le_one_sub_pow` compares it with the
  weaker factor `1 / (1 - ε₄)²`.
* `abs_finiteRank_capture_le`: the two-sided capture.

## How it works

For the lower bound, split `f` into its `Q`-projection `h` onto the span of the modes and the
rest. The rest contributes `Q(f - h, f - h) ≥ 0`, and on the span the functional differs from
`Q(h, h)` by at most `ε₃ Q(h, h) ≤ ε₃ Λ M(f, f)`.

The mismatch `ε₃` is a statement about one matrix. With `G` the `Q`-Gram matrix of the modes,
`S = G^{1/2}` and `y = S d`, the two quadratic expressions are `|y|²` and
`yᵀ S diag(μ)⁻¹ S y`. Their difference is the quadratic form of `1 - S diag(μ)⁻¹ S`, which the
spectral norm of that matrix bounds.

The angle `ε₄` comes from the residuals `rⱼ` of the approximate eigenvectors. A combination
`g = ∑ⱼ dⱼ ψ̄ⱼ` pairs with a `Q`-orthogonal `u` only through the residuals, which costs
`|d| (∑ⱼ μⱼ⁻² ‖rⱼ‖²)^{1/2}`, and `‖g‖² = dᵀ G_E d` is at least `(1 - ‖1 - G_E‖_F) |d|²`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.2, Lemmas 1 to 3, and
  their proofs in Appendix B. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped Matrix

section Matrices

variable {ι : Type*} [Fintype ι]

open scoped Matrix.Norms.L2Operator in
/-- A real quadratic form is bounded by the spectral norm of its matrix:
`|xᵀ A x| ≤ ‖A‖ |x|²`. -/
theorem abs_dotProduct_mulVec_le_l2_opNorm [DecidableEq ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 x)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x))
  rw [Matrix.inner_toEuclideanCLM] at h
  calc
    |x ⬝ᵥ A *ᵥ x| ≤ ‖WithLp.toLp 2 x‖ * (‖A‖ * ‖WithLp.toLp 2 x‖) :=
      h.trans (mul_le_mul_of_nonneg_left
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm _) (norm_nonneg _))
    _ = ‖A‖ * (x ⬝ᵥ x) := by
      rw [mul_left_comm, ← sq, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp,
        star_trivial]

open scoped Matrix.Norms.Frobenius in
/-- A real quadratic form is bounded by the Frobenius norm of its matrix:
`|xᵀ A x| ≤ ‖A‖_F |x|²`. This is `CAS.Analysis.Matrix.abs_quadForm_le_of_frobenius` stated with
Mathlib's Frobenius norm. -/
theorem abs_dotProduct_mulVec_le_frobenius (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ ‖A‖ * (x ⬝ᵥ x) := by
  rw [← CAS.Analysis.Matrix.sum_sum_mul_mul_eq_dotProduct_mulVec,
    ← CAS.Analysis.Matrix.sum_sq_eq_dotProduct]
  refine CAS.Analysis.Matrix.abs_quadForm_le_of_frobenius (norm_nonneg A) (le_of_eq ?_) x
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **The matrix identity behind the Gram mismatch.** For a positive semidefinite real matrix
`G` with square root `S`, and `y = S d`,

`dᵀ G d - ∑ⱼ ((dᵀ G)ⱼ)² / μⱼ = yᵀ (1 - S diag(μ)⁻¹ S) y`  and  `dᵀ G d = |y|²`,

so the left side is at most `‖1 - S diag(μ)⁻¹ S‖ dᵀ G d` in absolute value. -/
theorem abs_gram_sub_sum_sq_div_le [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    (μ : ι → ℝ) (d : ι → ℝ) :
    |d ⬝ᵥ G *ᵥ d - ∑ j, (d ᵥ* G) j ^ 2 / μ j| ≤
      ‖1 - CFC.sqrt G * Matrix.diagonal (fun j ↦ (μ j)⁻¹) * CFC.sqrt G‖ * (d ⬝ᵥ G *ᵥ d) := by
  set S := CFC.sqrt G with hS
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G (Matrix.nonneg_iff_posSemidef.mpr hG)
  have hSt : Sᵀ = S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)).isHermitian
  have hGt : Gᵀ = G := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hG.isHermitian
  set y := S *ᵥ d with hy
  have hvec : d ᵥ* S = y := by rw [← Matrix.mulVec_transpose, hSt]
  have hquad : d ⬝ᵥ G *ᵥ d = y ⬝ᵥ y := by
    rw [← hSS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvec]
  have hrow : d ᵥ* G = S *ᵥ y := by
    rw [← Matrix.mulVec_transpose, hGt, ← hSS, ← Matrix.mulVec_mulVec]
  have hsum : ∑ j, (d ᵥ* G) j ^ 2 / μ j =
      y ⬝ᵥ (S * Matrix.diagonal (fun j ↦ (μ j)⁻¹) * S) *ᵥ y := by
    rw [hrow, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hSt]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hdiff : d ⬝ᵥ G *ᵥ d - ∑ j, (d ᵥ* G) j ^ 2 / μ j =
      y ⬝ᵥ (1 - S * Matrix.diagonal (fun j ↦ (μ j)⁻¹) * S) *ᵥ y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← hsum, ← hquad]
  rw [hdiff, hquad]
  exact abs_dotProduct_mulVec_le_l2_opNorm _ y

end Matrices

section Mismatch

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  {ι : Type*} [Fintype ι]

/-- **Two-sided Gram mismatch from the mode matrix.** If the Gram matrix `G` of `Q` on the
modes satisfies `|dᵀ G d - ∑ⱼ ((dᵀ G)ⱼ)² / μⱼ| ≤ ε₃ dᵀ G d` for every `d`, then on the span of
the modes the functional `∑ⱼ Q(g, ψ̄ⱼ)² / μⱼ` differs from `Q(g, g)` by at most `ε₃ Q(g, g)`. -/
theorem abs_sub_sum_sq_div_le_of_matrix (Qform : H →L[ℝ] H →L[ℝ] ℝ) (ψbar : ι → H)
    (μ : ι → ℝ) {ε₃ : ℝ}
    (hmat : ∀ d : ι → ℝ,
      |d ⬝ᵥ formMatrix Qform ψbar ψbar *ᵥ d -
          ∑ j, (d ᵥ* formMatrix Qform ψbar ψbar) j ^ 2 / μ j| ≤
        ε₃ * (d ⬝ᵥ formMatrix Qform ψbar ψbar *ᵥ d)) :
    ∀ g ∈ Submodule.span ℝ (Set.range ψbar),
      |Qform g g - ∑ j, Qform g (ψbar j) ^ 2 / μ j| ≤ ε₃ * Qform g g := by
  intro g hg
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  have hrow (j : ι) :
      Qform (∑ i, d i • ψbar i) (ψbar j) = (d ᵥ* formMatrix Qform ψbar ψbar) j := by
    simp [Matrix.vecMul, dotProduct]
  simp only [hrow, form_sum_smul_sum_smul]
  exact hmat d

omit [Fintype ι] in
/-- The Gram matrix of a positive semidefinite symmetric form on a finite family is positive
semidefinite. -/
theorem posSemidef_formMatrix [Finite ι] (Qform : H →L[ℝ] H →L[ℝ] ℝ)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f) (ψbar : ι → H) :
    (formMatrix Qform ψbar ψbar).PosSemidef := by
  have := Fintype.ofFinite ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.IsHermitian.ext fun i j ↦ by simp [hQsymm]) fun d ↦ ?_
  rw [star_trivial, ← form_sum_smul_sum_smul]
  exact hQnonneg _

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- **Two-sided Gram mismatch with the spectral norm.** For a positive semidefinite symmetric
form `Q` with Gram matrix `G_Q` on the modes, the constant

`ε₃ = ‖1 - G_Q^{1/2} diag(μ)⁻¹ G_Q^{1/2}‖`

bounds the difference between `Q(g, g)` and `∑ⱼ Q(g, ψ̄ⱼ)² / μⱼ` on the span of the modes,
relative to `Q(g, g)`. -/
theorem abs_sub_sum_sq_div_le_l2_opNorm [DecidableEq ι] (Qform : H →L[ℝ] H →L[ℝ] ℝ)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f) (ψbar : ι → H)
    (μ : ι → ℝ) :
    ∀ g ∈ Submodule.span ℝ (Set.range ψbar),
      |Qform g g - ∑ j, Qform g (ψbar j) ^ 2 / μ j| ≤
        ‖1 - CFC.sqrt (formMatrix Qform ψbar ψbar) * Matrix.diagonal (fun j ↦ (μ j)⁻¹) *
          CFC.sqrt (formMatrix Qform ψbar ψbar)‖ * Qform g g :=
  abs_sub_sum_sq_div_le_of_matrix Qform ψbar μ
    (abs_gram_sub_sum_sq_div_le (posSemidef_formMatrix Qform hQsymm hQnonneg ψbar) μ)

/-- **The functional against the projection** (Lemma 1 of Hou, Wang and Yang). Let `Q` be
positive semidefinite and symmetric with `Q ≤ Λ M`, let `h` be a `Q`-orthogonal projection of
`f` onto the span of the modes, and let `ε₃` be a two-sided Gram mismatch on that span. Then

`|Q(h, h) - ∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ| ≤ ε₃ Λ M(f, f)`.

The pairings of `f` and of `h` with the modes agree, and `Q(h, h) ≤ Q(f, f) ≤ Λ M(f, f)`. -/
theorem abs_projection_sub_sum_sq_div_le (Mform Qform : H →L[ℝ] H →L[ℝ] ℝ) (ψbar : ι → H)
    (μ : ι → ℝ) {Λ ε₃ : ℝ}
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f)
    (hQ : ∀ f, Qform f f ≤ Λ * Mform f f)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range ψbar),
      |Qform g g - ∑ j, Qform g (ψbar j) ^ 2 / μ j| ≤ ε₃ * Qform g g)
    (hε₃0 : 0 ≤ ε₃) {f h : H} (hh : h ∈ Submodule.span ℝ (Set.range ψbar))
    (hfh : ∀ j, Qform (f - h) (ψbar j) = 0) :
    |Qform h h - ∑ j, Qform f (ψbar j) ^ 2 / μ j| ≤ ε₃ * Λ * Mform f f := by
  have hpair (j : ι) : Qform f (ψbar j) = Qform h (ψbar j) := by
    have := hfh j
    rwa [map_sub, sub_apply, sub_eq_zero] at this
  have hsplit : Qform f f = Qform (f - h) (f - h) + Qform h h := by
    have h0 : Qform (f - h) h = 0 := form_eq_zero_of_mem_span Qform ψbar hfh hh
    conv_lhs => rw [← sub_add_cancel f h]
    rw [form_add_add, h0, hQsymm h (f - h), h0]
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ by rw [hpair j]]
  calc
    _ ≤ ε₃ * Qform h h := hε₃ h hh
    _ ≤ ε₃ * (Λ * Mform f f) :=
      mul_le_mul_of_nonneg_left (by linarith [hQnonneg (f - h), hQ f]) hε₃0
    _ = ε₃ * Λ * Mform f f := (mul_assoc _ _ _).symm

end Mismatch

section Angle

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]

open scoped Matrix.Norms.Frobenius in
/-- **Quasi-orthogonality with the Frobenius constant** (Lemma 2 of Hou, Wang and Yang). Let
the modes satisfy `Q(ψ̄ⱼ, v) = μⱼ E(ψ̄ⱼ, v) + E(rⱼ, v)` on a subspace `V`, with `μⱼ ≠ 0`, and
let the energy Gram matrix `G_E` of the modes satisfy `‖1 - G_E‖_F < 1`. Then every `g` in the
span of the modes and every `u ∈ V` that is `Q`-orthogonal to the modes satisfy
`|E(g, u)| ≤ ε₄ ‖g‖_E ‖u‖_E` with

`ε₄² = (∑ⱼ μⱼ⁻² E(rⱼ, rⱼ)) / (1 - ‖1 - G_E‖_F)`,

stated here with squares. No sign of `Q` is used. The Frobenius norm gives the lower bound
`(1 - ‖1 - G_E‖_F) |b|² ≤ bᵀ G_E b`, which is the hypothesis of
`PDE.Analysis.Operator.form_residual_le_of_gram_lower`. -/
theorem form_sq_le_of_residual_frobenius {m : ℕ} (Eform Qform : H →L[ℝ] H →L[ℝ] ℝ)
    (V : Submodule ℝ H) (ψbar r : Fin m → H) (μ : Fin m → ℝ)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hμ : ∀ j, μ j ≠ 0)
    (hres : ∀ j, ∀ v ∈ V, Qform (ψbar j) v = μ j * Eform (ψbar j) v + Eform (r j) v)
    (hG : ‖(1 : Matrix (Fin m) (Fin m) ℝ) - formMatrix Eform ψbar ψbar‖ < 1) :
    ∀ g ∈ Submodule.span ℝ (Set.range ψbar), ∀ u ∈ V, (∀ j, Qform u (ψbar j) = 0) →
      Eform g u ^ 2 ≤ (∑ j, Eform (r j) (r j) / μ j ^ 2) /
        (1 - ‖(1 : Matrix (Fin m) (Fin m) ℝ) - formMatrix Eform ψbar ψbar‖) *
          Eform g g * Eform u u := by
  set δ := ‖(1 : Matrix (Fin m) (Fin m) ℝ) - formMatrix Eform ψbar ψbar‖
  set s := ∑ j, Eform (r j) (r j) / μ j ^ 2
  have hpos : 0 < 1 - δ := sub_pos.mpr hG
  have hε : 0 ≤ s / (1 - δ) :=
    div_nonneg (Finset.sum_nonneg fun j _ ↦ div_nonneg (hEnonneg _) (sq_nonneg _)) hpos.le
  have hs : ∑ j, (√(Eform (r j) (r j)) / |μ j|) ^ 2 = s :=
    Finset.sum_congr rfl fun j _ ↦ by rw [div_pow, Real.sq_sqrt (hEnonneg _), sq_abs]
  -- The mode combination has energy at least `(1 - ‖1 - G_E‖_F) |b|²`.
  have hlower (b : Fin m → ℝ) : (1 - δ) * ∑ i, b i ^ 2 ≤
      ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j := by
    have h := abs_dotProduct_mulVec_le_frobenius (1 - formMatrix Eform ψbar ψbar) b
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at h
    rw [CAS.Analysis.Matrix.sum_sum_mul_mul_eq_dotProduct_mulVec,
      CAS.Analysis.Matrix.sum_sq_eq_dotProduct]
    linarith [(abs_le.mp h).2]
  have hkey := form_sq_le_of_residual Eform Qform V ψbar r μ (ε₄ := √(s / (1 - δ))) hEsymm
    hEnonneg hQsymm hμ hres fun b ↦ by
      rw [Real.sq_sqrt hε, ← hs]
      exact form_residual_le_of_gram_lower Eform hEsymm hEnonneg ψbar r μ
        (fun j ↦ √(Eform (r j) (r j))) (fun j ↦ Real.sqrt_nonneg _)
        (fun j ↦ (Real.sq_sqrt (hEnonneg _)).ge) hpos hlower b
  simpa only [Real.sq_sqrt hε] using hkey

/-- `1 - ε²` is at least `(1 - ε)²` for `0 ≤ ε ≤ 1`. So the factor `1 / (1 - ε₄²)` of a
quasi-orthogonal splitting is at most the factor `1 / (1 - ε₄)²` that Hou, Wang and Yang use. -/
theorem one_sub_sq_le_one_sub_pow {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) ^ 2 ≤ 1 - ε ^ 2 := by
  nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hε1)]

/-- **A quasi-orthogonal splitting.** Let `E` be a positive semidefinite symmetric form and let
`x`, `u` make an angle at most `ε₄ < 1`, that is `E(x, u)² ≤ ε₄² E(x, x) E(u, u)`. If `x + u`
is `E`-orthogonal to `x`, then

`E(x, x) ≤ ε₄² / (1 - ε₄²) E(x + u, x + u)`  and  `E(u, u) ≤ 1 / (1 - ε₄²) E(x + u, x + u)`.

In the proof of Lemma 3 of Hou, Wang and Yang, `x` is the difference between the component of
`f` in the captured span and the `E`-projection of `f` onto that span, and `u` is the rest of
`f`. The orthogonality gives `E(x, x) = -E(x, u)` and Pythagoras
`E(u, u) = E(x + u, x + u) + E(x, x)`. -/
theorem form_le_of_orthogonal_add (Eform : H →L[ℝ] H →L[ℝ] ℝ)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f) {ε₄ : ℝ}
    (hε₄1 : ε₄ ^ 2 < 1) {x u : H} (horth : Eform (x + u) x = 0)
    (hangle : Eform x u ^ 2 ≤ ε₄ ^ 2 * Eform x x * Eform u u) :
    Eform x x ≤ ε₄ ^ 2 / (1 - ε₄ ^ 2) * Eform (x + u) (x + u) ∧
      Eform u u ≤ 1 / (1 - ε₄ ^ 2) * Eform (x + u) (x + u) := by
  have hpos : 0 < 1 - ε₄ ^ 2 := sub_pos.mpr hε₄1
  have hX : Eform x u = -Eform x x := by
    rw [map_add, add_apply, hEsymm u x] at horth
    linarith
  have hT : Eform (x + u) (x + u) = Eform u u - Eform x x := by
    rw [form_add_add, hEsymm u x, hX]
    ring
  -- `E(x, x)² ≤ ε₄² E(x, x) E(u, u)`, so `E(x, x) ≤ ε₄² E(u, u)`.
  have hA : Eform x x ≤ ε₄ ^ 2 * Eform u u := by
    rcases (hEnonneg x).eq_or_lt with h0 | hpos'
    · rw [← h0]
      exact mul_nonneg (sq_nonneg _) (hEnonneg u)
    · rw [hX, neg_sq, sq, mul_assoc] at hangle
      have := le_of_mul_le_mul_left (by linarith : Eform x x * Eform x x ≤
        Eform x x * (ε₄ ^ 2 * Eform u u)) hpos'
      exact this
  have hxx : Eform x x ≤ ε₄ ^ 2 / (1 - ε₄ ^ 2) * Eform (x + u) (x + u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos, hT]
    nlinarith
  refine ⟨hxx, ?_⟩
  have : Eform u u = Eform (x + u) (x + u) + Eform x x := by linarith
  rw [this]
  have h1 : 1 / (1 - ε₄ ^ 2) = 1 + ε₄ ^ 2 / (1 - ε₄ ^ 2) := by field_simp; ring
  rw [h1, add_mul, one_mul]
  linarith

end Angle

section Capture

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] {N m : ℕ}

/-- **Two-sided finite-rank capture** (Lemma 3 of Hou, Wang and Yang, without the residual term
`K₇`). For a positive semidefinite symmetric form `Q` with `Q ≤ Λ M` and a two-sided Gram
mismatch `ε₃` on the captured span,

`|Q(f, f) - ∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ| ≤ M₁ ‖∇f‖² + (η₂ M₁ + ε₃ Λ) ‖f‖²`,  `M₁ = K₅ + K₆ / (1 - ε₄)²`,

where `E = ‖∇·‖² + η₂ ‖·‖²` on the diagonal. The upper bound is
`PDE.Analysis.Operator.finiteRank_capture_le`. For the lower bound, the `Q`-projection `h` of
`f` onto the captured span has the pairings of `f`, the rest contributes `Q(f - h, f - h) ≥ 0`,
and the mismatch on the span costs at most `ε₃ Q(h, h) ≤ ε₃ Λ M(f, f)`. -/
theorem abs_finiteRank_capture_le (Eform Mform Qform gradientForm : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ) {η₂ Λ K₅ K₆ ε₃ ε₄ : ℝ}
    (hE : ∀ f, Eform f f = gradientForm f f + η₂ * Mform f f)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f)
    (hQ : ∀ f, Qform f f ≤ Λ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λ * Mform f f ≤ K₅ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
      Qform u u ≤ K₆ * Eform u u)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      |Qform g g - ∑ j, Qform g (capturedMode ψ C j) ^ 2 / μ j| ≤ ε₃ * Qform g g)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅) (hK₆0 : 0 ≤ K₆) (hε₃0 : 0 ≤ ε₃) (hε₄0 : 0 ≤ ε₄) (hε₄1 : ε₄ < 1) (f : H) :
    |Qform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j| ≤
      (K₅ + K₆ / (1 - ε₄) ^ 2) * gradientForm f f +
        (η₂ * (K₅ + K₆ / (1 - ε₄) ^ 2) + ε₃ * Λ) * Mform f f := by
  have hupper := finiteRank_capture_le Eform Mform Qform gradientForm ψ C μ hE hEsymm hEnonneg
    hQsymm hQnonneg hQ htail hK₆ (fun g hg ↦ (le_abs_self _).trans (hε₃ g hg)) hε₄ hK₅ hK₆0
    hε₃0 hε₄0 hε₄1 f
  -- The `Q`-orthogonal projection `h` of `f` onto the captured span.
  obtain ⟨e, he⟩ := exists_sub_sum_smul_orthogonal Qform hQsymm hQnonneg (capturedMode ψ C) f
  set h := ∑ j, e j • capturedMode ψ C j
  have hh : h ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨e, rfl⟩
  have hproj := abs_projection_sub_sum_sq_div_le Mform Qform (capturedMode ψ C) μ hQsymm
    hQnonneg hQ hε₃ hε₃0 hh he
  have hsplit : Qform f f = Qform (f - h) (f - h) + Qform h h := by
    have h0 : Qform (f - h) h = 0 := form_eq_zero_of_mem_span Qform _ he hh
    conv_lhs => rw [← sub_add_cancel f h]
    rw [form_add_add, h0, hQsymm h (f - h), h0]
    ring
  have hM₁ : 0 ≤ K₅ + K₆ / (1 - ε₄) ^ 2 :=
    add_nonneg hK₅ (div_nonneg hK₆0 (sq_nonneg _))
  have hEf := mul_nonneg hM₁ (hEnonneg f)
  rw [hE f] at hEf
  rw [abs_le]
  refine ⟨?_, hupper⟩
  linarith [(abs_le.mp hproj).1, hQnonneg (f - h)]

end Capture

end PDE.Analysis.Operator
