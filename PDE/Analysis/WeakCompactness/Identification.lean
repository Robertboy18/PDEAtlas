/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness

/-!
# Identifying bounded weak limits in reflexive spaces

A bounded family in a reflexive space converges weakly when its evaluations
against a separating family of continuous linear functionals converge.
Weak compactness supplies cluster points, and separation identifies every
cluster point with the prescribed limit. The convergence holds along the original
filter, with no passage to a subsequence.

As a consequence, if `A` is an injective continuous linear map and `A uᵢ ⇀ A v`
weakly, then `uᵢ ⇀ v` weakly. In a real Hilbert space reflexivity holds
automatically, which gives the versions without a reflexivity hypothesis.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.WeakCompactness

section Reflexive

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a reflexive space, let `test` be a family of functionals separating points. If `u` is
bounded and `test t (u i) → test t v` for every `t`, then `u i ⇀ v` weakly. For example,
convergence against smooth test functions determines weak convergence in `Lᵖ`. -/
theorem tendsto_of_separating_functionals_of_reflexive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H))
    {T : Type*} (test : T → StrongDual ℝ H)
    (hseparate : Function.Injective (fun x : H ↦ fun t ↦ test t x))
    {ι : Type*} {l : Filter ι} (u : ι → H) (v : H)
    (hbounded : Bornology.IsBounded (range u))
    (htest : ∀ t, Tendsto (fun i ↦ test t (u i)) l (𝓝 (test t v))) :
    Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l (𝓝 (toWeakSpace ℝ H v)) := by
  let f : ι → WeakSpace ℝ H := fun i ↦ toWeakSpace ℝ H (u i)
  have hpre : (toWeakSpace ℝ H) ⁻¹' range f = range u := by
    ext x
    simp [f]
  have hcompact := isCompact_closure_of_isBounded_of_reflexive
    hreflexive (range f) (hpre ▸ hbounded)
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun i ↦ subset_closure ⟨i, rfl⟩)
  intro x _ hx
  obtain ⟨U, hU, hux⟩ := mapClusterPt_iff_ultrafilter.mp hx
  apply (toWeakSpace ℝ H).symm.injective
  apply hseparate
  funext t
  exact tendsto_nhds_unique (tendsto_evaluation hux (test t)) ((htest t).mono_left hU)

/-- Weak convergence through an injective continuous linear map identifies the weak
limit of a bounded family in a reflexive space. -/
theorem tendsto_of_injective_map_of_reflexive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H))
    (A : H →L[ℝ] E) (hA : Function.Injective A)
    {ι : Type*} {l : Filter ι} (u : ι → H) (v : H)
    (hbounded : Bornology.IsBounded (range u))
    (himage : Tendsto (fun i ↦ toWeakSpace ℝ E (A (u i))) l
      (𝓝 (toWeakSpace ℝ E (A v)))) :
    Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l (𝓝 (toWeakSpace ℝ H v)) := by
  refine tendsto_of_separating_functionals_of_reflexive hreflexive
    (fun φ : StrongDual ℝ E ↦ φ.comp A) ?_ u v hbounded ?_
  · intro x y hxy
    apply hA
    apply (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E)).injective
    ext φ
    exact congrFun hxy φ
  · intro φ
    exact tendsto_evaluation himage φ

end Reflexive

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak convergence of an injective linear image identifies the weak limit
of a norm-bounded Hilbert family, without passing to a new subsequence. -/
theorem tendsto_of_injective_map
    (A : H →L[ℝ] E) (hA : Function.Injective A)
    {ι : Type*} {l : Filter ι} (u : ι → H) (v : H)
    (hbounded : Bornology.IsBounded (range u))
    (himage : Tendsto (fun i ↦ toWeakSpace ℝ E (A (u i))) l
      (𝓝 (toWeakSpace ℝ E (A v)))) :
    Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l (𝓝 (toWeakSpace ℝ H v)) :=
  tendsto_of_injective_map_of_reflexive inclusionInDoubleDual_surjective
    A hA u v hbounded himage

/-- A bounded Hilbert-valued map is weakly continuous when its image under
an injective continuous linear map is weakly continuous. -/
theorem continuous_of_injective_map
    (A : H →L[ℝ] E) (hA : Function.Injective A)
    {T : Type*} [TopologicalSpace T] (u : T → H)
    (hbounded : Bornology.IsBounded (range u))
    (himage : Continuous (fun t ↦ toWeakSpace ℝ E (A (u t)))) :
    Continuous (fun t ↦ toWeakSpace ℝ H (u t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact tendsto_of_injective_map A hA u (u t) hbounded himage.continuousAt

end PDE.Analysis.WeakCompactness
