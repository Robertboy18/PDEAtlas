/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact adjoints on Hilbert spaces

The Hilbert adjoint of a compact operator between real or complex Hilbert spaces is compact.
This is the Hilbert-space case of Schauder's theorem, which Evans uses in the proof of the
Fredholm alternative.

## Main results

* `IsCompactOperator.exists_finite_rank_approximation`: a compact operator is an operator-norm
  limit of finite-rank operators with compact adjoints.
* `isCompactOperator_adjoint`: the adjoint of a compact operator is compact.

## How it works

The theorem is classical. Evans, Appendix D.5, Theorem 4, proves it for an operator on one real
Hilbert space by passing to a weakly convergent subsequence; we approximate instead. A finite
`ε`-net of the compact closure of the image of the unit ball spans a finite-dimensional
subspace, and composing `K` with the orthogonal projection onto it moves `K` by at most `ε` in
operator norm. The adjoint of this approximant is `K.adjoint` composed with the same projection,
hence compact. Taking adjoints preserves the operator norm, and compact operators form a closed
set (Mathlib's `isClosed_setOfPred_isCompactOperator`), so `K.adjoint` is compact.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.5, Theorem 4, p. 724, used in steps 6 and 8 of
  the proof of Theorem 5, p. 726. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace PDE.Analysis

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every compact operator between real or complex Hilbert spaces admits arbitrarily accurate
finite-rank approximants. The chosen approximant and its Hilbert adjoint are both compact. -/
theorem IsCompactOperator.exists_finite_rank_approximation
    {K : E →L[𝕜] F} (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : E →L[𝕜] F,
      FiniteDimensional 𝕜 A.range ∧ IsCompactOperator A ∧
        IsCompactOperator A.adjoint ∧ ‖K - A‖ ≤ ε := by
  let Q := closure (K '' Metric.closedBall 0 1)
  have hQ : IsCompact Q := hK.isCompact_closure_image_closedBall 1
  obtain ⟨N, _hNQ, hNfinite, hcover⟩ := hQ.finite_cover_balls hε
  let S : Submodule 𝕜 F := Submodule.span 𝕜 N
  let : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 hNfinite
  let : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  let P : F →L[𝕜] F := S.starProjection
  let A : E →L[𝕜] F := P.comp K
  have hArange : A.range ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact S.starProjection_apply_mem (K x)
  let rangeToSpan : A.range →ₗ[𝕜] S :=
    LinearMap.codRestrict S A.range.subtype fun y ↦ hArange y.property
  have hRangeToSpanInjective : Function.Injective rangeToSpan := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : S ↦ (z : F)) hxy)
  let : FiniteDimensional 𝕜 A.range :=
    FiniteDimensional.of_injective rangeToSpan hRangeToSpanInjective
  have hP : IsCompactOperator P := by
    have hpSub : IsCompactOperator S.orthogonalProjectionOnto :=
      isCompactOperator_of_locallyCompactSpace_dom S.orthogonalProjectionOnto
    exact hpSub.clm_comp S.subtypeL
  have hA : IsCompactOperator A := hP.comp_clm K
  have hPadjoint : P.adjoint = P :=
    S.starProjection_isSymmetric.clm_adjoint_eq
  have hAadjoint : IsCompactOperator A.adjoint := by
    rw [show A.adjoint = K.adjoint.comp P by simp [A, hPadjoint]]
    exact hP.clm_comp K.adjoint
  refine ⟨A, inferInstance, hA, hAadjoint, ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  have hKxQ : K x ∈ Q :=
    subset_closure ⟨x, by simpa [Metric.mem_closedBall] using hx.le, rfl⟩
  have hcovered := hcover hKxQ
  simp only [Set.mem_iUnion, exists_prop, Metric.mem_ball] at hcovered
  obtain ⟨y, hyN, hy⟩ := hcovered
  change ‖K x - S.starProjection (K x)‖ ≤ ε
  rw [S.starProjection_minimal]
  refine (ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
    (⟨y, Submodule.subset_span hyN⟩ : S)).trans ?_
  simpa [dist_eq_norm] using hy.le

/-- **Schauder's theorem for real or complex Hilbert spaces.** The Hilbert adjoint of a
compact continuous linear operator is compact (Evans, Appendix D.5, Theorem 4). -/
theorem isCompactOperator_adjoint
    {K : E →L[𝕜] F} (hK : IsCompactOperator K) :
    IsCompactOperator K.adjoint := by
  have hmem : K.adjoint ∈ closure {A : F →L[𝕜] E | IsCompactOperator A} := by
    refine Metric.mem_closure_iff.2 fun eps heps ↦ ?_
    obtain ⟨A, _hAfin, _hA, hAadj, hdist⟩ :=
      IsCompactOperator.exists_finite_rank_approximation hK (half_pos heps)
    refine ⟨A.adjoint, hAadj, ?_⟩
    have hnorm : ‖A.adjoint - K.adjoint‖ = ‖A - K‖ := by
      rw [← map_sub]
      exact ContinuousLinearMap.adjoint.norm_map (A - K)
    rw [dist_eq_norm, norm_sub_rev, hnorm, norm_sub_rev]
    exact hdist.trans_lt (half_lt_self heps)
  exact isClosed_setOfPred_isCompactOperator.closure_subset hmem

end PDE.Analysis
