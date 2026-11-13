/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.Spectral
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The first variational eigenvalue

For a symmetric coercive form `B` and a compact map `j : V →L[ℝ] H` with dense range,
the first eigenvalue is the minimum of `B v v / ‖j v‖²` over vectors with `j v ≠ 0`.
It equals the reciprocal of the norm of the pivot solution operator. The minimum is
attained by a weak eigenfunction normalized in `H`. This is Rayleigh's formula, Evans,
§6.5.1, Theorem 2 (i) in the form of Remark (ii) after it, together with the existence of an
eigenfunction attaining the minimum from Theorem 2 (ii). The positivity of that
eigenfunction and the simplicity of the principal eigenvalue, the rest of his Theorem 2, are
not part of the statement.

The pivot space must be nontrivial for a normalized eigenfunction to exist. The map `j`
need not be injective. Vectors in the kernel of `j` are excluded from the quotient, but the
inequality `‖j v‖² ≤ ‖S‖ B v v`, with `S` the pivot solution operator, holds for every vector.

## Main results

* `norm_sq_le_norm_pivotSolutionOperator_mul`: `‖j v‖² ≤ ‖S‖ B v v` for every `v`, where `S`
  is the pivot solution operator.
* `exists_first_weakEigenfunction`: a weak eigenfunction `u` with `‖j u‖ = 1` and eigenvalue
  `λ = ‖S‖⁻¹ > 0`, where `λ` is the least value of `B v v / ‖j v‖²` over `j v ≠ 0`.

## How it works

Evans's proof of (5) begins by expanding a function in the orthonormal eigenbasis of
Theorem 1, (6)-(9). We do not use the eigenbasis. Cauchy–Schwarz for positive bilinear forms
transfers the operator-norm bound back to the energy, which gives the lower bound. For the
eigenvector, `ContinuousLinearMap.spectralRadius_eq_nnnorm` and
`Real.spectralRadius_mem_spectrum_or` put `‖S‖` or `-‖S‖` in the spectrum of the
self-adjoint operator `S`, positivity of `S` excludes `-‖S‖`, and the compact Fredholm
alternative, `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`, makes `‖S‖` an eigenvalue.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.1, Theorem 2 (Variational principle for the
  principal eigenvalue), (5), p. 356, and Remark (ii) and steps 1 and 2 of the proof, (6)-(9),
  p. 357. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The pivot solution operator controls the mass by the energy. This estimate does not
require compactness, dense range, or injectivity of the map into the pivot space. -/
theorem norm_sq_le_norm_pivotSolutionOperator_mul
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (j : V →L[ℝ] H) (v : V) :
    ‖j v‖ ^ 2 ≤ ‖pivotSolutionOperator B hB j‖ * B v v := by
  have hnonneg (w : V) : 0 ≤ B w w := by
    obtain ⟨c, hc, hcoercive⟩ := hB
    exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg w)) (norm_nonneg w)).trans
      (hcoercive w)
  by_cases hv : j v = 0
  · simpa only [hv, norm_zero, zero_pow two_ne_zero] using
      mul_nonneg (norm_nonneg (pivotSolutionOperator B hB j)) (hnonneg v)
  let R := pivotSolutionOperator B hB j
  let w := solveCLM B hB (pivotLoadCLM j (j v))
  have hwv : B w v = ‖j v‖ ^ 2 := by
    rw [solveCLM.isWeakSolution B hB (pivotLoadCLM j (j v)) v,
      pivotLoadCLM_apply, real_inner_self_eq_norm_sq]
  have hww : B w w = ⟪j v, R (j v)⟫_ℝ :=
    (inner_pivotSolutionOperator B hB j (j v) (j v)).symm
  have hcs : (B w v) ^ 2 ≤ B w w * B v v :=
    B.toBilinForm.apply_sq_le_of_symm hnonneg ⟨hsymm⟩ w v
  have hbound : B w w ≤ ‖R‖ * ‖j v‖ ^ 2 := by
    calc
      B w w = ⟪j v, R (j v)⟫_ℝ := hww
      _ ≤ ‖j v‖ * ‖R (j v)‖ := real_inner_le_norm _ _
      _ ≤ ‖j v‖ * (‖R‖ * ‖j v‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm (j v)) (norm_nonneg _)
      _ = ‖R‖ * ‖j v‖ ^ 2 := by ring
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mp
  calc
    ‖j v‖ ^ 2 * ‖j v‖ ^ 2 = (B w v) ^ 2 := by simp only [hwv, pow_two]
    _ ≤ B w w * B v v := hcs
    _ ≤ (‖R‖ * ‖j v‖ ^ 2) * B v v :=
      mul_le_mul_of_nonneg_right hbound (hnonneg v)
    _ = (‖R‖ * B v v) * ‖j v‖ ^ 2 := by ring

/-- A symmetric coercive form with a compact dense map into a nontrivial pivot space has
a first weak eigenfunction. Its positive eigenvalue is the attained minimum of the
Rayleigh quotient over vectors with nonzero pivot image; the eigenfunction has unit
pivot norm. This includes finite-dimensional spaces and allows a kernel for `j`. -/
theorem exists_first_weakEigenfunction [Nontrivial H]
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (j : V →L[ℝ] H)
    (hcompact : IsCompactOperator j) (hdense : DenseRange j) :
    ∃ (lambda : ℝ) (u : V), 0 < lambda ∧
      lambda = ‖pivotSolutionOperator B hB j‖⁻¹ ∧ ‖j u‖ = 1 ∧
      (∀ v, B u v = lambda * ⟪j u, j v⟫_ℝ) ∧
      IsLeast ((fun v : V ↦ B v v / ‖j v‖ ^ 2) '' {v | j v ≠ 0}) lambda := by
  let R := pivotSolutionOperator B hB j
  have hRcompact : IsCompactOperator R :=
    isCompactOperator_pivotSolutionOperator B hB j hcompact
  have hRsymm : R.IsSymmetric := isSymmetric_pivotSolutionOperator B hB hsymm j
  have hRne : R ≠ 0 := by
    obtain ⟨f, hf⟩ := exists_ne (0 : H)
    have hpos := inner_pivotSolutionOperator_pos B hB j hdense hf
    intro hzero
    change 0 < ⟪f, R f⟫_ℝ at hpos
    simp [hzero] at hpos
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hRne
  have hsome :
      ¬ ∀ μ, Module.End.HasEigenvalue (R : Module.End ℝ H) μ → μ = 0 := by
    intro h
    exact hRne
      ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hRcompact hRsymm).mp h)
  push Not at hsome
  obtain ⟨μ, hμ, hμne⟩ := hsome
  have hspectrum : (spectrum ℝ R).Nonempty :=
    ⟨μ, (hRcompact.hasEigenvalue_iff_mem_spectrum hμne).mp hμ⟩
  have hradius : (spectralRadius ℝ R).toReal = ‖R‖ := by
    rw [R.spectralRadius_eq_nnnorm hRsymm.isSelfAdjoint]
    simp
  have hnormEigen : Module.End.HasEigenvalue (R : Module.End ℝ H) ‖R‖ := by
    obtain hpos | hneg := Real.spectralRadius_mem_spectrum_or hspectrum
    · exact (hRcompact.hasEigenvalue_iff_mem_spectrum hRpos.ne').mpr
        (hradius ▸ hpos)
    · have hneg' : -‖R‖ ∈ spectrum ℝ R := hradius ▸ hneg
      obtain ⟨f, hf⟩ :=
        ((hRcompact.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hRpos.ne')).mpr
          hneg').exists_hasEigenvector
      have hRf : R f = -‖R‖ • f := hf.apply_eq_smul
      have hfpos := inner_pivotSolutionOperator_pos B hB j hdense hf.2
      change 0 < ⟪f, R f⟫_ℝ at hfpos
      rw [hRf, real_inner_smul_right, real_inner_self_eq_norm_sq] at hfpos
      exact False.elim ((not_lt_of_ge
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRpos.le) (sq_nonneg ‖f‖))) hfpos)
  obtain ⟨x, hx⟩ := hnormEigen.exists_hasEigenvector
  let f : H := (‖x‖⁻¹ : ℝ) • x
  have hf : ‖f‖ = 1 := norm_smul_inv_norm hx.2
  have hRx : R x = ‖R‖ • x := hx.apply_eq_smul
  have hRf : R f = ‖R‖ • f := by
    dsimp only [f]
    rw [map_smul, hRx, smul_comm]
  let u : V := ‖R‖⁻¹ • solveCLM B hB (pivotLoadCLM j f)
  have hju : j u = f := by
    change j (‖R‖⁻¹ • solveCLM B hB (pivotLoadCLM j f)) = f
    rw [map_smul]
    change ‖R‖⁻¹ • R f = f
    rw [hRf, smul_smul, inv_mul_cancel₀ hRpos.ne', one_smul]
  have hweak (v : V) : B u v = ‖R‖⁻¹ * ⟪j u, j v⟫_ℝ := by
    change B (‖R‖⁻¹ • solveCLM B hB (pivotLoadCLM j f)) v = _
    rw [map_smul, smul_apply, smul_eq_mul,
      solveCLM.isWeakSolution B hB (pivotLoadCLM j f) v, pivotLoadCLM_apply, hju]
  have hunorm : ‖j u‖ = 1 := hju.symm ▸ hf
  refine ⟨‖R‖⁻¹, u, inv_pos.mpr hRpos, rfl, hunorm, hweak, ?_, ?_⟩
  · refine ⟨u, ?_, ?_⟩
    · intro hzero
      simp [hzero] at hunorm
    · dsimp only
      rw [hweak u, real_inner_self_eq_norm_sq, hunorm, one_pow, mul_one, div_one]
  · rintro _ ⟨v, hv, rfl⟩
    apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mpr
    have hbound := norm_sq_le_norm_pivotSolutionOperator_mul B hB hsymm j v
    calc
      ‖R‖⁻¹ * ‖j v‖ ^ 2 ≤ ‖R‖⁻¹ * (‖R‖ * B v v) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hRpos.le)
      _ = B v v := by rw [← mul_assoc, inv_mul_cancel₀ hRpos.ne', one_mul]

end PDE.Analysis.Variational
