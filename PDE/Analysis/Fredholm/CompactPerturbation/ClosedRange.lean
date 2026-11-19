/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Algebra.Order.Ring.Star

/-!
# Closed range for compact perturbations of the identity

If `K` is compact on a real Hilbert space, then `K - I` has closed range. The main
estimate bounds `K - I` below on the orthogonal complement of its kernel. We also
prove the orthogonality criterion for membership in a closed operator range.

## Main results

* `exists_antilipschitzWith_sub_identity_domRestrict_orthogonal_ker`: `K - I` is bounded below
  on the orthogonal complement of its kernel.
* `isClosed_range_sub_identity`: `K - I` has closed range.
* `mem_range_iff_forall_adjoint_ker_orthogonal`: a closed range is the orthogonal complement of
  the kernel of the adjoint.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.5, Theorem 5(ii) and (iii), p. 725, and steps
  2-4 of its proof, p. 725. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- A compact perturbation of the identity is bounded below on the
orthogonal complement of its kernel, estimate (4) in step 2 of Evans's proof of the Fredholm
alternative, Appendix D.5, Theorem 5. Otherwise normalized approximate null vectors have a
convergent subsequence, whose nonzero limit lies both in the kernel and its orthogonal
complement. -/
theorem exists_antilipschitzWith_sub_identity_domRestrict_orthogonal_ker
    (K : V →L[ℝ] V) (hK : IsCompactOperator K) :
    ∃ c, AntilipschitzWith c
      ((K - (1 : V →L[ℝ] V)).domRestrict (K - (1 : V →L[ℝ] V)).kerᗮ) := by
  let T := K - (1 : V →L[ℝ] V)
  let N : Submodule ℝ V := T.ker
  let X := Nᗮ
  let A : X →L[ℝ] V := T.domRestrict X
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra hanti
  push Not at hanti
  have hsmall : ∀ ε > 0, ∃ x : X, ‖A x‖ < ε * ‖x‖ := hanti
  obtain ⟨C : ℝ, hC⟩ := NormedField.exists_one_lt_norm ℝ
  obtain ⟨φ, _hφanti, hφpos, hφzero⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hxExists (m : ℕ) :
      ∃ x : X, ‖x‖ ≤ 1 ∧ ‖C‖⁻¹ ≤ ‖x‖ ∧ ‖A x‖ < φ m := by
    obtain ⟨x, hx⟩ := hsmall (φ m) (hφpos m)
    have hxne : x ≠ 0 := by
      intro hzero
      subst x
      simp at hx
    obtain ⟨d, hdne, hdUpper, hdLower, _hdInv⟩ :=
      rescale_to_shell hC (ε := 1) (by norm_num) hxne
    refine ⟨d • x, hdUpper.le, by simpa using hdLower, ?_⟩
    calc
      ‖A (d • x)‖ = ‖d‖ * ‖A x‖ := by simp [norm_smul]
      _ < ‖d‖ * (φ m * ‖x‖) := by
        exact mul_lt_mul_of_pos_left hx (norm_pos_iff.mpr hdne)
      _ = φ m * ‖d • x‖ := by simp [norm_smul]; ring
      _ ≤ φ m := by
        simpa using mul_le_of_le_one_right (hφpos m).le hdUpper.le
  choose x hxUpper hxLower hxA using hxExists
  let KX : X →L[ℝ] V := K.comp X.subtypeL
  have hKX : IsCompactOperator KX := hK.comp_clm X.subtypeL
  obtain ⟨Q, hQcompact, hQimage⟩ := hKX.image_closedBall_subset_compact 1
  obtain ⟨y, _hyQ, ψ, hψ, hKxy⟩ := hQcompact.tendsto_subseq
    (x := fun m ↦ KX (x m))
    (fun m ↦ hQimage ⟨x m, by simpa [Metric.mem_closedBall, dist_eq_norm] using hxUpper m, rfl⟩)
  have hAxZero : Tendsto (fun m ↦ A (x m)) atTop (𝓝 0) :=
    squeeze_zero_norm (by grind) hφzero
  have hxToY : Tendsto (fun m ↦ ((x (ψ m) : X) : V)) atTop (𝓝 y) := by
    have hsub := hKxy.sub (hAxZero.comp hψ.tendsto_atTop)
    convert hsub using 1
    · funext m
      change (x (ψ m) : V) = K (x (ψ m) : V) - T (x (ψ m) : V)
      simp [T]
    · simp
  have hyX : y ∈ X := by
    exact N.isClosed_orthogonal.mem_of_tendsto hxToY
      (Filter.Eventually.of_forall fun m ↦ (x (ψ m)).property)
  have hTyZero : T y = 0 := by
    apply tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hxToY)
    convert hAxZero.comp hψ.tendsto_atTop using 1
    funext m
    rfl
  have hyN : y ∈ N := LinearMap.mem_ker.mpr hTyZero
  have hyZero : y = 0 := by
    exact inner_self_eq_zero.mp ((N.mem_orthogonal' y).mp hyX y hyN)
  have hyNormLower : ‖C‖⁻¹ ≤ ‖y‖ := by
    exact ge_of_tendsto' (continuous_norm.tendsto y |>.comp hxToY) fun m ↦ hxLower (ψ m)
  have hCinvPos : 0 < ‖C‖⁻¹ := by positivity
  rw [hyZero, norm_zero] at hyNormLower
  exact (not_le_of_gt hCinvPos) hyNormLower

/-- The range of a compact perturbation of the identity is closed (Evans, Appendix D.5,
Theorem 5(ii)). -/
theorem isClosed_range_sub_identity
    (K : V →L[ℝ] V) (hK : IsCompactOperator K) :
    IsClosed ((K - (1 : V →L[ℝ] V)).range : Set V) := by
  let T := K - (1 : V →L[ℝ] V)
  let N : Submodule ℝ V := T.ker
  let X := Nᗮ
  let A : X →L[ℝ] V := T.domRestrict X
  obtain ⟨c, hc⟩ :=
    exists_antilipschitzWith_sub_identity_domRestrict_orthogonal_ker K hK
  have hAclosed : IsClosed (A.range : Set V) := by
    change IsClosed (Set.range A)
    exact hc.isClosed_range A.uniformContinuous
  have : CompleteSpace N := T.isClosed_ker.completeSpace_coe
  have hsup : X ⊔ N = ⊤ := by
    rw [sup_comm]
    exact N.sup_orthogonal_of_hasOrthogonalProjection
  have hcodisjoint : Codisjoint X T.ker := by
    simpa [N, codisjoint_iff] using hsup
  have hdomRange :
      (T.domRestrict X).range = X.map (T : V →ₗ[ℝ] V) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrange : A.range = T.range := by
    calc
      A.range = X.map (T : V →ₗ[ℝ] V) := by simp [A]
      _ = T.range := Submodule.map_eq_range_iff.mpr hcodisjoint
  rw [← hrange]
  exact hAclosed

/-- Hilbert-space closure-of-range criterion: a vector lies in the closure
of the range of `T` exactly when it is orthogonal to every vector in the
kernel of `T†`. -/
theorem mem_topologicalClosure_range_iff_forall_adjoint_ker_orthogonal
    (T : V →L[ℝ] V) (y : V) :
    y ∈ T.range.topologicalClosure ↔
      ∀ v : V, T.adjoint v = 0 → ⟪y, v⟫_ℝ = 0 := by
  rw [← T.range.orthogonal_orthogonal_eq_closure, T.orthogonal_range]
  exact T.adjoint.ker.mem_orthogonal' y

/-- If `T` has closed range, `y` lies in the range exactly when it is orthogonal to the kernel
of `T.adjoint`. For `T = K - 1` with `K` compact this is Evans, Appendix D.5, Theorem 5(iii). -/
theorem mem_range_iff_forall_adjoint_ker_orthogonal
    (T : V →L[ℝ] V) (hclosed : IsClosed (T.range : Set V)) (y : V) :
    y ∈ T.range ↔ ∀ v : V, T.adjoint v = 0 → ⟪y, v⟫_ℝ = 0 := by
  have hclosure : T.range.topologicalClosure = T.range := by
    apply le_antisymm
    · exact T.range.topologicalClosure_minimal le_rfl hclosed
    · exact T.range.le_topologicalClosure
  rw [← hclosure]
  exact mem_topologicalClosure_range_iff_forall_adjoint_ker_orthogonal T y

end PDE.Analysis
