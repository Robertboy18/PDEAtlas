/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import PDE.Analysis.Operator.Resolvent.Spectrum

/-!
# The part of an unbounded operator in a finite-dimensional invariant subspace

On a finite-dimensional subspace `V` of its domain that it maps into itself, an unbounded
operator `A` is an endomorphism of a finite-dimensional space (`LinearPMap.restrictEnd`), and
linear algebra applies. We draw the consequences that the Riesz projections of finite rank
(`LinearPMap.range_rieszProjection_resolvent_eq_genEigenspace`) and the spectral decomposition of
a semigroup generator use: generalized eigenvectors of `A|V` are generalized eigenvectors of `A`,
over an algebraically closed field they span `V`, only finitely many eigenvalues have an
eigenvector in `V`, and a bounded projection of finite rank that commutes with `A` gives a
resolvent relative to it. Invariant subspaces of infinite dimension, where the part of `A` is
again unbounded, are not treated.

## Main results

* `LinearPMap.restrictEnd`: the part of `A` in an invariant subspace of its domain.
* `coe_mem_genEigenspace_of_pow_apply_eq_zero`: a vector killed by `(A|V - μ)^k` is in the
  generalized eigenspace `ker (A - μ)^k` of `A`.
* `exists_mem_graph_smul_of_mem_genEigenspace`: a nonzero generalized eigenvector in an
  invariant subspace gives an eigenvector in that subspace.
* `le_iSup_genEigenspace_inf`: over an algebraically closed field, a finite-dimensional
  invariant subspace is spanned by generalized eigenvectors of `A`; this is Mathlib's
  `Module.End.iSup_maxGenEigenspace_eq_top` for `A.restrictEnd`.
* `finite_setOf_exists_mem_graph_smul`: finitely many eigenvalues of `A` have an eigenvector in
  a finite-dimensional invariant subspace.
* `exists_isResolventAtOn_of_finiteDimensional`: over a complete field, for a bounded projection
  `Q` of finite rank that commutes with `A` and a `z` that is not an eigenvalue of `A` in the
  range of `Q`, a bounded `S` with `(z - A) S = Q` and `S (z - A) = Q` on the domain.

## How it works

For the last statement, `z - A|V` is injective on the range `V` of `Q`, hence bijective because
`V` has finite dimension, and `S` is its inverse composed with `Q`. A linear map on a
finite-dimensional space over a complete field is continuous, so `S` is bounded.
-/

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {V : Submodule 𝕜 E} (hV : V ≤ A.domain)
  (hAV : ∀ ⦃x y⦄, (x, y) ∈ A.graph → x ∈ V → y ∈ V)

/-- The part of `A` in an invariant subspace `V` of its domain, as an endomorphism of `V`. -/
def restrictEnd (A : E →ₗ.[𝕜] E) (V : Submodule 𝕜 E) (hV : V ≤ A.domain)
    (hAV : ∀ ⦃x y⦄, (x, y) ∈ A.graph → x ∈ V → y ∈ V) : Module.End 𝕜 V :=
  (A.toFun.comp (Submodule.inclusion hV)).codRestrict V
    fun v ↦ hAV (A.mem_graph ⟨v, hV v.2⟩) v.2

/-- The part of `A` in `V` acts as `A`. -/
theorem mem_graph_restrictEnd (v : V) :
    ((v : E), (A.restrictEnd V hV hAV v : E)) ∈ A.graph :=
  A.mem_graph ⟨v, hV v.2⟩

/-- A vector of `V` killed by `(A|V - μ)^k` is in the generalized eigenspace `ker (A - μ)^k`
of `A`. -/
theorem coe_mem_genEigenspace_of_pow_apply_eq_zero {μ : 𝕜} {k : ℕ} {v : V}
    (h : ((A.restrictEnd V hV hAV - μ • 1) ^ k) v = 0) : (v : E) ∈ A.genEigenspace μ k := by
  induction k generalizing v with
  | zero =>
    rw [pow_zero, one_apply_eq_self] at h
    simp [h]
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp] at h
    exact mem_genEigenspace_succ.mpr ⟨_, mem_graph_restrictEnd hV hAV v, ih h⟩

include hAV in
/-- A nonzero generalized eigenvector in an invariant subspace gives an eigenvector in that
subspace: the last nonzero vector of the chain `x, (A - μ) x, (A - μ)² x, …`. -/
theorem exists_mem_graph_smul_of_mem_genEigenspace {μ : 𝕜} {k : ℕ} {x : E}
    (hx : x ∈ A.genEigenspace μ k) (hxV : x ∈ V) (hx0 : x ≠ 0) :
    ∃ v ∈ V, v ≠ 0 ∧ (v, μ • v) ∈ A.graph := by
  induction k generalizing x with
  | zero => exact absurd ((Submodule.mem_bot 𝕜).mp hx) hx0
  | succ k ih =>
    obtain ⟨y, hxy, hu⟩ := mem_genEigenspace_succ.mp hx
    by_cases hu0 : y - μ • x = 0
    · exact ⟨x, hxV, hx0, by rwa [sub_eq_zero.mp hu0] at hxy⟩
    · exact ih hu (V.sub_mem (hAV hxy hxV) (V.smul_mem μ hxV)) hu0

include hV hAV in
/-- **A finite-dimensional invariant subspace is spanned by generalized eigenvectors**, over an
algebraically closed field: `V` is the span of the spaces `ker (A - μ)^n ∩ V`, `n = dim V`. -/
theorem le_iSup_genEigenspace_inf [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 V] :
    V ≤ ⨆ μ, A.genEigenspace μ (Module.finrank 𝕜 V) ⊓ V := by
  have h : (⊤ : Submodule 𝕜 V) =
      ⨆ μ, (A.restrictEnd V hV hAV).genEigenspace μ (Module.finrank 𝕜 V) := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top (A.restrictEnd V hV hAV)]
    exact iSup_congr fun μ ↦ Module.End.maxGenEigenspace_eq_genEigenspace_finrank _ μ
  calc V = (⊤ : Submodule 𝕜 V).map V.subtype := (Submodule.map_subtype_top V).symm
    _ = ⨆ μ, ((A.restrictEnd V hV hAV).genEigenspace μ
          (Module.finrank 𝕜 V)).map V.subtype := by rw [h, Submodule.map_iSup]
    _ ≤ ⨆ μ, A.genEigenspace μ (Module.finrank 𝕜 V) ⊓ V := iSup_mono fun μ ↦ by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨coe_mem_genEigenspace_of_pow_apply_eq_zero hV hAV
          (LinearMap.mem_ker.mp (Module.End.mem_genEigenspace_nat.mp hv)), v.2⟩

include hV hAV in
/-- An operator has finitely many eigenvalues with an eigenvector in a finite-dimensional
invariant subspace of its domain. -/
theorem finite_setOf_exists_mem_graph_smul [FiniteDimensional 𝕜 V] :
    {μ : 𝕜 | ∃ x ∈ V, x ≠ 0 ∧ (x, μ • x) ∈ A.graph}.Finite := by
  refine (Module.End.finite_hasEigenvalue (A.restrictEnd V hV hAV)).subset ?_
  rintro μ ⟨x, hxV, hx0, hx⟩
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxV⟩)
    ⟨?_, fun h ↦ hx0 (congrArg Subtype.val h)⟩
  rw [Module.End.mem_eigenspace_iff]
  exact Subtype.ext (A.mem_graph_snd_inj (mem_graph_restrictEnd hV hAV ⟨x, hxV⟩) hx rfl)

/-- **The resolvent relative to a projection of finite rank.** Let `Q` be a bounded projection
of finite rank that commutes with `A`, with range in the domain of `A`. If `z` is not an
eigenvalue of `A` in the range of `Q`, there is a bounded `S` with `(z - A) S = Q`,
`S (z - A) = Q` on the domain, and `S Q = Q S = S`. -/
theorem exists_isResolventAtOn_of_finiteDimensional [CompleteSpace 𝕜] {Q : E →L[𝕜] E}
    (hQ : IsIdempotentElem Q) [FiniteDimensional 𝕜 (LinearMap.range Q.toLinearMap)]
    (hQA : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (Q x, Q y) ∈ A.graph)
    (hQV : LinearMap.range Q.toLinearMap ≤ A.domain) {z : 𝕜}
    (hz : ∀ x, Q x = x → (x, z • x) ∈ A.graph → x = 0) :
    ∃ S : E →L[𝕜] E, A.IsResolventAtOn z Q S ∧ S * Q = S ∧ Q * S = S := by
  have hfix : ∀ x ∈ LinearMap.range Q.toLinearMap, Q x = x := by
    rintro _ ⟨y, rfl⟩
    exact DFunLike.congr_fun hQ.eq y
  have hAV : ∀ ⦃x y⦄, (x, y) ∈ A.graph → x ∈ LinearMap.range Q.toLinearMap →
      y ∈ LinearMap.range Q.toLinearMap := fun x y hxy hx ↦ by
    have h := hQA hxy
    rw [hfix x hx] at h
    exact ⟨y, A.mem_graph_snd_inj h hxy rfl⟩
  set V := LinearMap.range Q.toLinearMap
  set f := A.restrictEnd V hQV hAV
  have hf (v : V) : (((z • (1 : Module.End 𝕜 V) - f) v : V) : E) = z • (v : E) - (f v : V) := by
    simp
  have hinj : Function.Injective (z • (1 : Module.End 𝕜 V) - f) := by
    refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ Subtype.ext (hz v (hfix v v.2) ?_)
    have h := mem_graph_restrictEnd hQV hAV v
    have h2 : ((f v : V) : E) = z • (v : E) :=
      (sub_eq_zero.mp ((hf v).symm.trans (by rw [hv]; rfl))).symm
    rwa [h2] at h
  obtain ⟨e, he⟩ : ∃ e : V ≃ₗ[𝕜] V, ∀ v, e v = (z • (1 : Module.End 𝕜 V) - f) v :=
    ⟨LinearEquiv.ofBijective _ ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩, fun _ ↦ rfl⟩
  set Qc : E →L[𝕜] V := Q.codRestrict V fun x ↦ ⟨x, rfl⟩
  set S : E →L[𝕜] E :=
    V.subtypeL ∘L (LinearMap.toContinuousLinearMap (e.symm : V →ₗ[𝕜] V)) ∘L Qc
  have hSy (y : E) : S y = (e.symm (Qc y) : V) := rfl
  have hQc (y : E) : ((Qc y : V) : E) = Q y := rfl
  refine ⟨S, ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩, ?_, ?_⟩
  · have h := mem_graph_restrictEnd hQV hAV (e.symm (Qc y))
    have h2 : ((f (e.symm (Qc y)) : V) : E) = z • (e.symm (Qc y) : V) - Q y := by
      have h3 := hf (e.symm (Qc y))
      rw [← he, e.apply_symm_apply, hQc] at h3
      rw [h3, sub_sub_cancel]
    rwa [h2] at h
  · have hx : (⟨Q x, x, rfl⟩ : V) = e.symm (Qc (z • x - y)) := by
      rw [LinearEquiv.eq_symm_apply, he]
      refine Subtype.ext ?_
      have h : ((f ⟨Q x, x, rfl⟩ : V) : E) = Q y :=
        A.mem_graph_snd_inj (mem_graph_restrictEnd hQV hAV ⟨Q x, x, rfl⟩) (hQA hxy) rfl
      rw [hf, h, hQc, _root_.map_sub, _root_.map_smul]
    rw [hSy, ← hx]
  · refine ContinuousLinearMap.ext fun y ↦ ?_
    have h : Qc (Q y) = Qc y := Subtype.ext (DFunLike.congr_fun hQ.eq y)
    rw [mul_apply_eq_comp, hSy, hSy, h]
  · exact ContinuousLinearMap.ext fun y ↦ hfix _ (e.symm (Qc y)).2

end LinearPMap
