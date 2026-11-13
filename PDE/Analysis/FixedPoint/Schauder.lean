/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FixedPoint.Brouwer.CompactConvex
public import PDE.Analysis.FixedPoint.FiniteApproximation
public import PDE.Analysis.FixedPoint.Compactness
public import PDE.Analysis.Operator.CompactConvergence

/-!
# Schauder fixed points

A continuous self-map of a nonempty closed convex set with relatively compact image has a fixed
point, in any real normed space. For a compact convex set this is Schauder's fixed point
theorem, Evans, §9.2.2, Theorem 3, stated there in a Banach space; the set must be nonempty.
We also apply it through an injective compact operator out of a Hilbert space.

## Main results

* `exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_range`: a continuous self-map of a
  nonempty closed convex set whose range has compact closure has a fixed point.
* `exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_image`: the same for a map given on
  the whole space.
* `exists_isFixedPt_of_isCompact_convex`: Schauder's theorem for a nonempty compact convex set.
* `exists_isFixedPt_of_compact_embedding_on`: a self-map of a nonempty closed bounded convex
  subset of a Hilbert space has a fixed point if it is Lipschitz for `‖e ·‖`, where `e` is an
  injective compact operator; `exists_isFixedPt_of_compact_embedding` is the case of a ball.

## How it works

We follow Evans's proof. Step 1 approximates the identity of a compact set within `ε` by a
continuous map into the convex hull of finitely many of its points; Evans writes this map down
with distance weights, and we take it from `exists_continuous_finite_convexHull_approximation`.
We apply it to the closure of the range of the map rather than to the set, which is why the set
need only be closed. Step 2 finds a fixed point of the approximate map on that convex hull with
`exists_isFixedPt_of_isCompact_convex_finiteDimensional`, and step 3 passes to the limit
`ε → 0` with `exists_isFixedPt_of_forall_dist_lt`. For the embedding versions the image of the
set under `e` is compact by
`PDE.Analysis.isCompact_image_of_isCompactOperator_of_isClosed_convex_of_isBounded`, and the
map transported to it is Lipschitz, so the compact convex version applies.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.2, Theorem 3 (Schauder's fixed point theorem) and
  its proof, (15)-(16), pp. 538-539. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Metric Function Topology

namespace PDE.FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- Schauder's theorem for a bundled self-map of a nonempty closed convex set whose
image has compact closure in the ambient space. -/
theorem exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_range
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconv : Convex ℝ K) (f : C(K, K))
    (hcompact : IsCompact (closure (range fun x : K ↦ (f x : E)))) :
    ∃ x, IsFixedPt f x := by
  classical
  let C := closure (range fun x : K ↦ (f x : E))
  have hCK : C ⊆ K := closure_minimal (by rintro _ ⟨x, rfl⟩; exact (f x).property) hclosed
  have hcompactK : IsCompact (closure (f '' (univ : Set K))) := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [← hclosed.isClosedEmbedding_subtypeVal.closure_image_eq]
    simpa only [image_univ, ← range_comp, comp_def] using hcompact
  have happrox (ε : ℝ) (hε : 0 < ε) :
      ∃ x ∈ (univ : Set K), dist (f x) x < ε := by
    obtain ⟨s, hsC, p, hp⟩ := exists_continuous_finite_convexHull_approximation hcompact hε
    let V := Submodule.span ℝ (↑s : Set E)
    have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ s.finite_toSet
    have hspan : convexHull ℝ (↑s : Set E) ⊆ (V : Set E) :=
      convexHull_min Submodule.subset_span V.convex
    have hhullK : convexHull ℝ (↑s : Set E) ⊆ K :=
      convexHull_min (hsC.trans hCK) hconv
    let D : Set V := Subtype.val ⁻¹' convexHull ℝ (↑s : Set E)
    have hDcompact : IsCompact D :=
      IsInducing.subtypeVal.isCompact_preimage' (s.finite_toSet.isCompact_convexHull ℝ)
        (by simpa only [Subtype.range_coe] using hspan)
    have hDconv : Convex ℝ D := (convex_convexHull ℝ (↑s : Set E)).linear_preimage V.subtype
    let pV : C(C, V) :=
      ⟨fun x ↦ ⟨p x, hspan (hp x).1⟩, p.continuous.subtype_mk _⟩
    obtain ⟨x₀, hx₀⟩ := hne
    let c₀ : C := ⟨f ⟨x₀, hx₀⟩, subset_closure (mem_range_self _)⟩
    have hDne : D.Nonempty := ⟨pV c₀, (hp c₀).1⟩
    let q : C(D, K) :=
      ⟨fun x ↦ ⟨(x : V), hhullK x.property⟩,
        continuous_subtype_val.subtype_val.subtype_mk _⟩
    let qC : C(D, C) :=
      ⟨fun x ↦ ⟨f (q x), subset_closure (mem_range_self _)⟩,
        (f.continuous.subtype_val.comp q.continuous).subtype_mk _⟩
    let T : C(D, D) :=
      ⟨fun x ↦ ⟨pV (qC x), (hp (qC x)).1⟩,
        (pV.continuous.comp qC.continuous).subtype_mk _⟩
    obtain ⟨x, hx⟩ :=
      exists_isFixedPt_of_isCompact_convex_finiteDimensional hDne hDcompact hDconv T
    have hpoint := congrArg (fun y : D ↦ ((y : V) : E)) hx
    change p (qC x) = ((x : V) : E) at hpoint
    refine ⟨q x, mem_univ _, ?_⟩
    have herror := (hp (qC x)).2
    rw [hpoint] at herror
    change ‖((x : V) : E) - (f (q x) : E)‖ < ε at herror
    change dist (f (q x) : E) ((x : V) : E) < ε
    rw [dist_comm, dist_eq_norm]
    exact herror
  obtain ⟨x, _, hx⟩ := exists_isFixedPt_of_forall_dist_lt isClosed_univ
    f.continuous.continuousOn hcompactK happrox
  exact ⟨x, hx⟩

/-- A continuous map on a nonempty closed convex set with relatively compact image has
a fixed point, stated without bundling the map or its domain. -/
theorem exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_image
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconv : Convex ℝ K) {f : E → E}
    (hf : ContinuousOn f K) (hmap : MapsTo f K K)
    (hcompact : IsCompact (closure (f '' K))) : ∃ x ∈ K, IsFixedPt f x := by
  let g : C(K, K) := ⟨fun x ↦ ⟨f x, hmap x.property⟩, hf.mapsToRestrict hmap⟩
  have hgcompact : IsCompact (closure (range fun x : K ↦ (g x : E))) := by
    change IsCompact (closure (range (K.domRestrict f)))
    simpa only [range_domRestrict] using hcompact
  obtain ⟨x, hx⟩ := exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_range
    hne hclosed hconv g hgcompact
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- Every continuous self-map of a nonempty compact convex set in a real normed space
has a fixed point. Nonemptiness cannot be dropped. -/
theorem exists_isFixedPt_of_isCompact_convex
    (hne : K.Nonempty) (hcompact : IsCompact K) (hconv : Convex ℝ K) (f : C(K, K)) :
    ∃ x, IsFixedPt f x := by
  apply exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_range
    hne hcompact.isClosed hconv f
  apply hcompact.of_isClosed_subset isClosed_closure
  exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact (f x).property) hcompact.isClosed

/-- A self-map of a closed, convex, bounded Hilbert-space set has a fixed point if
a compact injective embedding makes it Lipschitz there. The set may carry several
independent norm constraints, and the Lipschitz constant need not be less than one. -/
theorem exists_isFixedPt_of_compact_embedding_on
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (e : H →L[ℝ] E) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    {s : Set H} (hne : s.Nonempty) (hclosed : IsClosed s) (hconvex : Convex ℝ s)
    (hbounded : Bornology.IsBounded s) (T : H → H) {C : NNReal}
    (hmap : MapsTo T s s)
    (hcontinuous : ∀ u ∈ s, ∀ v ∈ s,
      ‖e (T u - T v)‖ ≤ C * ‖e (u - v)‖) :
    ∃ u ∈ s, IsFixedPt T u := by
  classical
  let K := e '' s
  let f : E → E := fun y ↦ e (T (invFun (e : H → E) y))
  have hleft := leftInverse_invFun he
  have hKcompact : IsCompact K :=
    PDE.Analysis.isCompact_image_of_isCompactOperator_of_isClosed_convex_of_isBounded
      PDE.Analysis.inclusionInDoubleDual_surjective e hcompact hclosed hconvex hbounded
  have hKconvex : Convex ℝ K := hconvex.linear_image e.toLinearMap
  have hKnonempty : K.Nonempty := hne.image e
  have hf : LipschitzOnWith C f K := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simpa only [f, hleft u, hleft v, dist_eq_norm, map_sub] using hcontinuous u hu v hv
  have hfmap : MapsTo f K K := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨T u, ?_, ?_⟩
    · exact hmap hu
    · simp only [f, hleft u]
  let g : C(K, K) := ⟨fun y ↦ ⟨f y, hfmap y.property⟩, hf.continuousOn.mapsToRestrict hfmap⟩
  obtain ⟨y, hy⟩ := exists_isFixedPt_of_isCompact_convex hKnonempty hKcompact hKconvex g
  obtain ⟨u, hu, huy⟩ := y.property
  have hfix : f (y : E) = (y : E) := congrArg Subtype.val hy
  rw [← huy] at hfix
  refine ⟨u, hu, he ?_⟩
  simpa only [f, hleft u] using hfix

/-- An energy-ball self-map has a fixed point if a compact injective embedding makes it
Lipschitz on that ball. The Lipschitz constant need not be less than one. -/
theorem exists_isFixedPt_of_compact_embedding
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (e : H →L[ℝ] E) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (T : H → H) {r : ℝ} (hr : 0 ≤ r) {C : NNReal}
    (hmap : ∀ u, ‖u‖ ≤ r → ‖T u‖ ≤ r)
    (hcontinuous : ∀ u, ‖u‖ ≤ r → ∀ v, ‖v‖ ≤ r →
      ‖e (T u - T v)‖ ≤ C * ‖e (u - v)‖) :
    ∃ u, ‖u‖ ≤ r ∧ IsFixedPt T u := by
  simpa only [mem_closedBall, dist_zero_right] using
    exists_isFixedPt_of_compact_embedding_on e he hcompact
      (s := closedBall (0 : H) r) ⟨0, by simpa using hr⟩
      isClosed_closedBall (convex_closedBall (0 : H) r) isBounded_closedBall T
      (fun u hu ↦ by
        simpa only [mem_closedBall, dist_zero_right] using
          hmap u (by simpa only [mem_closedBall, dist_zero_right] using hu))
      (fun u hu v hv ↦ hcontinuous u
        (by simpa only [mem_closedBall, dist_zero_right] using hu) v
        (by simpa only [mem_closedBall, dist_zero_right] using hv))

end PDE.FixedPoint
