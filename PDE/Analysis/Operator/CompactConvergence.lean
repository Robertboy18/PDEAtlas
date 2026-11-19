/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import PDE.Analysis.WeakCompactness
public import PDE.Analysis.WeakSequentialBoundedness

/-!
# Compactness and convergence of linear operators

A set uniformly approximated by totally bounded sets is totally bounded. A
compact operator also sends a bounded weakly convergent
family to a strongly convergent family, without any completeness assumption
on either space.

For sequences the norm bound follows from weak convergence, so the sequential
theorem needs no separate boundedness premise.

`tendsto_compactOperator_of_tendsto_weak` is the remark in Evans, App. D.5, that a compact
`K : H → H` on a real Hilbert space sends `u_k ⇀ u` to `K u_k → K u`, here for compact maps
between real normed spaces. The norm bound comes from `isBounded_range_of_tendsto_weak`, and
the compactness from Mathlib's `IsCompactOperator.isCompact_closure_image_of_bounded`.

## Main results

* `totallyBounded_of_uniformly_approximated`: a set that lies within every `ε > 0` of some
  totally bounded set is totally bounded.
* `tendsto_compactOperator_of_tendsto_weak_of_bounded`, `tendsto_compactOperator_of_tendsto_weak`:
  a compact operator sends bounded weakly convergent families, and weakly convergent
  sequences, to norm convergent ones.
* `continuousOn_compactOperator_weak_of_bounded`: a compact operator is weak-to-norm
  continuous on bounded sets.
* `isCompact_image_of_isCompactOperator_of_isClosed_convex_of_isBounded`,
  `isCompact_image_closedBall_of_isCompactOperator`: in a reflexive space, a compact operator
  maps a closed, convex, bounded set to a compact set, in particular a closed ball of a real
  Hilbert space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. D.5, the remark after the definition of compact
  operators, p. 724. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

/-- A set is totally bounded if, at every scale, it lies uniformly close to
some totally bounded comparison set. -/
theorem totallyBounded_of_uniformly_approximated
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (happrox : ∀ ε > 0, ∃ B : Set X, TotallyBounded B ∧
      ∀ x ∈ A, ∃ y ∈ B, dist x y < ε) :
    TotallyBounded A := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨B, hB, hAB⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨t, htFinite, htCover⟩ :=
    Metric.totallyBounded_iff.mp hB (ε / 2) (half_pos hε)
  refine ⟨t, htFinite, ?_⟩
  intro x hx
  obtain ⟨y, hyB, hxy⟩ := hAB x hx
  obtain ⟨z, hzT, hyz⟩ := Set.mem_iUnion₂.mp (htCover hyB)
  apply Set.mem_iUnion₂.mpr
  exact ⟨z, hzT, by
    rw [Metric.mem_ball] at hyz ⊢
    exact (dist_triangle x y z).trans_lt <| by linarith⟩

/-- A compact linear map sends a bounded weakly convergent family to a
strongly convergent family. Boundedness is stated separately because an
arbitrary convergent net need not have bounded range. Neither space needs
to be complete. -/
theorem tendsto_compactOperator_of_tendsto_weak_of_bounded
    {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : IsCompactOperator T)
    {l : Filter ι} {u : ι → X} {uLimit : X}
    (hbounded : Bornology.IsBounded (range u))
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ X (u i)) l
      (𝓝 (toWeakSpace ℝ X uLimit))) :
    Tendsto (fun i ↦ T (u i)) l (𝓝 (T uLimit)) := by
  have hcompact := hT.isCompact_closure_image_of_bounded
    (f := T.toLinearMap) hbounded
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun i ↦ subset_closure ⟨u i, mem_range_self i, rfl⟩)
  intro y _ hy
  obtain ⟨U, hU, hyU⟩ := mapClusterPt_iff_ultrafilter.mp hy
  have hweak := (WeakSpace.map T).continuous.continuousAt.tendsto.comp
    (hu.mono_left hU)
  have hyweak := (toWeakSpaceCLM ℝ Y).continuous.continuousAt.tendsto.comp hyU
  exact (toWeakSpace ℝ Y).injective (tendsto_nhds_unique hyweak hweak)

/-- A compact linear map is weak-to-norm continuous on every norm-bounded set. -/
theorem continuousOn_compactOperator_weak_of_bounded
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : IsCompactOperator T)
    {s : Set X} (hs : Bornology.IsBounded s) :
    ContinuousOn (fun w : WeakSpace ℝ X ↦ T ((toWeakSpace ℝ X).symm w))
      (toWeakSpace ℝ X '' s) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_compactOperator_of_tendsto_weak_of_bounded T hT
  · apply hs.subset
    rintro y ⟨w, rfl⟩
    obtain ⟨z, hz, hzw⟩ := w.property
    simpa only [← hzw, LinearEquiv.symm_apply_apply] using hz
  · simpa only [LinearEquiv.apply_symm_apply] using continuous_subtype_val.tendsto x

/-- A compact linear map sends a weakly convergent sequence to a strongly
convergent sequence. Uniform boundedness supplies the norm bound automatically. -/
theorem tendsto_compactOperator_of_tendsto_weak
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : IsCompactOperator T)
    {u : ℕ → X} {uLimit : X}
    (hu : Tendsto (fun j ↦ toWeakSpace ℝ X (u j)) atTop
      (𝓝 (toWeakSpace ℝ X uLimit))) :
    Tendsto (fun j ↦ T (u j)) atTop (𝓝 (T uLimit)) :=
  tendsto_compactOperator_of_tendsto_weak_of_bounded T hT
    (isBounded_range_of_tendsto_weak hu) hu

/-- A compact linear map takes a closed, convex, bounded set in a reflexive space to
a compact set. Closedness of the image is obtained from weak compactness of the source,
rather than assumed. -/
theorem isCompact_image_of_isCompactOperator_of_isClosed_convex_of_isBounded
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (T : X →L[ℝ] Y) (hT : IsCompactOperator T) {s : Set X}
    (hclosed : IsClosed s) (hconvex : Convex ℝ s) (hbounded : Bornology.IsBounded s) :
    IsCompact (T '' s) := by
  have hweakclosed : IsClosed (toWeakSpace ℝ X '' s) := by
    have hclosure := hconvex.toWeakSpace_closure ℝ
    rw [hclosed.closure_eq] at hclosure
    rw [hclosure]
    exact isClosed_closure
  have hweakbounded : Bornology.IsBounded ((toWeakSpace ℝ X) ⁻¹' (toWeakSpace ℝ X '' s)) := by
    simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ X).injective] using hbounded
  have hweakcompact : IsCompact (toWeakSpace ℝ X '' s) := by
    rw [← hweakclosed.closure_eq]
    exact WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
      hreflexive _ hweakbounded
  have himage := hweakcompact.image_of_continuousOn
    (continuousOn_compactOperator_weak_of_bounded T hT hbounded)
  simpa only [Set.image_image, LinearEquiv.symm_apply_apply] using himage

/-- The closed energy ball in a real Hilbert space has compact image under a compact
embedding. This is the compactness input for Schauder in a weaker function-space norm. -/
theorem isCompact_image_closedBall_of_isCompactOperator
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : IsCompactOperator T) (r : ℝ) :
    IsCompact (T '' Metric.closedBall 0 r) :=
  isCompact_image_of_isCompactOperator_of_isClosed_convex_of_isBounded
    inclusionInDoubleDual_surjective T hT Metric.isClosed_closedBall
    (convex_closedBall (0 : X) r) Metric.isBounded_closedBall

end PDE.Analysis
