/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.GlobalGraphChart
public import PDE.Elliptic.Regularity.Boundary.Construction
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# A concrete operational `C²` atlas for the Euclidean unit ball

The boundary `H²` regularity theory in this library is stated for domains carrying a
`SobolevSpace.C2BoundaryAtlas`: a finite family of boundary charts, each a `C²` diffeomorphism
onto a bounded target that straightens the boundary to the hyperplane `{yₙ = 0}` and maps the
domain to the upper half-space, together with cutoffs subordinate to the chart sources. We
construct such an atlas for the open Euclidean unit ball `B(0, 1) ⊆ ℝ^n` in every positive
dimension, so that the abstract regularity theorems apply to a domain. The charts are the
classical graph charts of the sphere over its coordinate caps, as in the definition of a `C^k`
boundary in Evans's Appendix C.1.

The construction uses the `2n` signed coordinate caps `{±xᵢ > 0}` covering the sphere. For the
cap at coordinate `i`, an orthogonal coordinate permutation moves `i` to the last (normal) slot.
Compactness of the subordinate cutoff support gives a strict tangential radius `r < 1`, and the
spherical height `sqrt (1 - ‖x'‖²)` is replaced by a globally smooth total function agreeing with
it exactly on the closed tangential cylinder of radius `r` (`GlobalGraphChart`). Conjugating the
triangular graph-flattening homeomorphism of `GlobalGraphChart` by the permutation produces charts
whose forward and inverse maps are globally `C²`, and the exact height identity on the cylinder
shows that the chart sends the ball to the upper half-space on its source.

No geometric chart family is assumed as input; everything is built from the cover and cutoffs of
`PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall`.

## Main results

* `c2BoundaryAtlas`: the operational `C²` boundary atlas on the open unit ball.

## Implementation notes

All intermediate objects (coordinate swaps, quantitative chart sources, conjugated charts, and the
per-index package bundling each chart with its `C²` and half-space properties) are private. Only
the assembled atlas and its instance are exported.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.1, the definition of a `C^k` boundary, p. 710.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Boundary.Atlas.UnitBall.ConcreteAtlas

open Metric Set
open PDE.Common
open SobolevSpace.Extension
open scoped BigOperators

variable (n : ℕ) [Fact (0 < n)]

/-!
## Coordinate permutations
-/

/-- The coordinate swap as Mathlib's canonical linear isometry induced by
`Equiv.swap`. -/
private def coordinateSwap (i : Fin n) : ℝ^n ≃L[ℝ] ℝ^n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.swap i (lastIndex (n := n)))).toContinuousLinearEquiv

@[simp]
private theorem coordinateSwap_apply (i j : Fin n) (x : ℝ^n) :
    coordinateSwap n i x j = x ((Equiv.swap i (lastIndex (n := n))) j) := by
  simp [coordinateSwap, Equiv.piCongrLeft']

private theorem coordinateSwap_apply_normal (i : Fin n) (x : ℝ^n) :
    coordinateSwap n i x (lastIndex (n := n)) = x i := by
  simp [coordinateSwap_apply]

@[simp]
private theorem coordinateSwap_involutive (i : Fin n) :
    Function.Involutive (coordinateSwap n i) := by
  intro x
  ext j
  simp [coordinateSwap_apply]

@[simp]
private theorem coordinateSwap_symm_apply (i : Fin n) (x : ℝ^n) :
    (coordinateSwap n i).symm x = coordinateSwap n i x := by
  apply (coordinateSwap n i).injective
  rw [(coordinateSwap n i).apply_symm_apply]
  exact (coordinateSwap_involutive n i x).symm

private theorem coordinateSwap_norm (i : Fin n) (x : ℝ^n) :
    ‖coordinateSwap n i x‖ = ‖x‖ := by
  exact
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap i (lastIndex (n := n)))).norm_map x

private theorem coordinateSwap_contDiff (i : Fin n) (m : ℕ∞) :
    ContDiff ℝ m (coordinateSwap n i) :=
  (coordinateSwap n i).contDiff

/-!
## Tangential geometry and compact support shrinking
-/

/-- Tangential projection after moving coordinate `i` to the normal slot. -/
private def tangentialProjection (i : Fin n) (x : ℝ^n) : ℝ^n :=
  HalfSpace.boundaryProjection n (coordinateSwap n i x)

private theorem tangentialProjection_contDiff (i : Fin n) (m : ℕ∞) :
    ContDiff ℝ m (tangentialProjection n i) :=
  (HalfSpace.contDiff_boundaryProjection n m).comp
    (coordinateSwap_contDiff n i m)

private theorem norm_sq_eq_normal_add_tangential (x : ℝ^n) :
    ‖x‖ ^ 2 =
      x (lastIndex (n := n)) ^ 2 + ‖HalfSpace.boundaryProjection n x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have htangent :
      ∑ j : Fin n, (HalfSpace.boundaryProjection n x j) ^ 2 =
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase (lastIndex (n := n)), x j ^ 2 := by
    have hnormal :
        HalfSpace.boundaryProjection n x (lastIndex (n := n)) = 0 := by
      exact HalfSpace.boundaryProjection_apply_last n x
    calc
      ∑ j : Fin n, (HalfSpace.boundaryProjection n x j) ^ 2 =
          ∑ j ∈ (Finset.univ : Finset (Fin n)).erase (lastIndex (n := n)),
              (HalfSpace.boundaryProjection n x j) ^ 2 +
            (HalfSpace.boundaryProjection n x (lastIndex (n := n))) ^ 2 :=
        (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
          (fun j ↦ (HalfSpace.boundaryProjection n x j) ^ 2)
          (Finset.mem_univ (lastIndex (n := n)))).symm
      _ = ∑ j ∈ (Finset.univ : Finset (Fin n)).erase (lastIndex (n := n)),
              (HalfSpace.boundaryProjection n x j) ^ 2 := by
        rw [hnormal]
        norm_num
      _ = ∑ j ∈ (Finset.univ : Finset (Fin n)).erase (lastIndex (n := n)),
              x j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≠ lastIndex (n := n) := by
          simpa using hj
        rw [HalfSpace.boundaryProjection_apply_of_ne_last n x hjn]
  rw [htangent]
  exact
    (Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun j : Fin n ↦ x j ^ 2) (Finset.mem_univ (lastIndex (n := n)))).symm

private theorem tangentialProjection_norm_sq (i : Fin n) (x : ℝ^n) :
    ‖tangentialProjection n i x‖ ^ 2 =
      tangentialNormSq n i x := by
  have hswap :=
    norm_sq_eq_normal_add_tangential n (coordinateSwap n i x)
  have horiginal :
      ‖x‖ ^ 2 = x i ^ 2 + tangentialNormSq n i x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [tangentialNormSq]
    exact
      (Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun j : Fin n ↦ x j ^ 2) (Finset.mem_univ i)).symm
  rw [coordinateSwap_norm, coordinateSwap_apply_normal] at hswap
  have htangent :
      ‖HalfSpace.boundaryProjection n (coordinateSwap n i x)‖ ^ 2 =
        tangentialNormSq n i x := by
    linarith
  exact htangent

/-- The support of either signed cutoff at coordinate `i`, transported to
the tangential hyperplane, is contained in the open unit ball. -/
private theorem tangentialProjection_support_subset_ball
    (k : Fin (n + n)) (i : Fin n)
    (hk :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inl i ∨
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inr i) :
    tangentialProjection n i ''
        tsupport ((boundaryCover n).boundaryCutoff k).toFun ⊆
      ball 0 1 := by
  rintro y ⟨x, hx, rfl⟩
  have hxcap : x ∈ boundaryCap n k := by
    simpa [boundaryCover] using
      (boundaryCover n).boundaryCutoff_support k hx
  have htan : tangentialNormSq n i x < 1 := by
    rcases hk with hk | hk
    · rw [boundaryCap, hk] at hxcap
      exact hxcap.1.2
    · rw [boundaryCap, hk] at hxcap
      exact hxcap.1.2
  rw [mem_ball, dist_zero_right]
  have hnorm0 := norm_nonneg (tangentialProjection n i x)
  rw [← tangentialProjection_norm_sq n i] at htan
  nlinarith

/-- Every signed cutoff support admits a positive uniform tangential radius
strictly below the singular radius `1`. -/
private theorem exists_supportRadius
    (k : Fin (n + n)) (i : Fin n)
    (hk :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inl i ∨
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inr i) :
    ∃ r ∈ Ioo (0 : ℝ) 1,
      ∀ x ∈ tsupport ((boundaryCover n).boundaryCutoff k).toFun,
        ‖tangentialProjection n i x‖ < r := by
  let K : Set (ℝ^n) :=
    tangentialProjection n i ''
      tsupport ((boundaryCover n).boundaryCutoff k).toFun
  have hKcompact : IsCompact K :=
    ((boundaryCover n).boundaryCutoff k).hasCompactSupport.image
      (tangentialProjection_contDiff n i 0).continuous
  obtain ⟨r, hr, hKr⟩ :=
    exists_pos_lt_subset_ball (r := (1 : ℝ))
      zero_lt_one hKcompact.isClosed
      (tangentialProjection_support_subset_ball n k i hk)
  refine ⟨r, hr, ?_⟩
  intro x hx
  have := hKr ⟨x, hx, rfl⟩
  simpa [mem_ball, dist_zero_right] using this

/-!
## Quantitative chart sources
-/

/-- A positive signed graph source at coordinate `i`. -/
private def positiveSource (i : Fin n) (r : ℝ) : Set (ℝ^n) :=
  ({x | 0 < x i} ∩ {x | ‖tangentialProjection n i x‖ < r}) ∩
    ball 0 2

/-- A negative signed graph source at coordinate `i`. -/
private def negativeSource (i : Fin n) (r : ℝ) : Set (ℝ^n) :=
  ({x | x i < 0} ∩ {x | ‖tangentialProjection n i x‖ < r}) ∩
    ball 0 2

private theorem isOpen_positiveSource (i : Fin n) (r : ℝ) :
    IsOpen (positiveSource n i r) := by
  apply IsOpen.inter
  · apply IsOpen.inter
    · exact isOpen_Ioi.preimage (EuclideanSpace.proj i).continuous
    · exact isOpen_Iio.preimage
        (tangentialProjection_contDiff n i 0).continuous.norm
  · exact isOpen_ball

private theorem isOpen_negativeSource (i : Fin n) (r : ℝ) :
    IsOpen (negativeSource n i r) := by
  apply IsOpen.inter
  · apply IsOpen.inter
    · exact isOpen_Iio.preimage (EuclideanSpace.proj i).continuous
    · exact isOpen_Iio.preimage
        (tangentialProjection_contDiff n i 0).continuous.norm
  · exact isOpen_ball

private theorem bounded_positiveSource (i : Fin n) (r : ℝ) :
    Bornology.IsBounded (positiveSource n i r) :=
  Metric.isBounded_ball.subset inter_subset_right

private theorem bounded_negativeSource (i : Fin n) (r : ℝ) :
    Bornology.IsBounded (negativeSource n i r) :=
  Metric.isBounded_ball.subset inter_subset_right

private theorem positiveCutoff_support_subset_source
    (k : Fin (n + n)) (i : Fin n)
    (hk :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inl i)
    {r : ℝ}
    (hr :
      ∀ x ∈ tsupport ((boundaryCover n).boundaryCutoff k).toFun,
        ‖tangentialProjection n i x‖ < r) :
    tsupport ((boundaryCover n).boundaryCutoff k).toFun ⊆
      positiveSource n i r := by
  intro x hx
  have hxcap : x ∈ boundaryCap n k := by
    simpa [boundaryCover] using
      (boundaryCover n).boundaryCutoff_support k hx
  rw [boundaryCap, hk] at hxcap
  exact ⟨⟨hxcap.1.1, hr x hx⟩, hxcap.2⟩

private theorem negativeCutoff_support_subset_source
    (k : Fin (n + n)) (i : Fin n)
    (hk :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inr i)
    {r : ℝ}
    (hr :
      ∀ x ∈ tsupport ((boundaryCover n).boundaryCutoff k).toFun,
        ‖tangentialProjection n i x‖ < r) :
    tsupport ((boundaryCover n).boundaryCutoff k).toFun ⊆
      negativeSource n i r := by
  intro x hx
  have hxcap : x ∈ boundaryCap n k := by
    simpa [boundaryCover] using
      (boundaryCover n).boundaryCutoff_support k hx
  rw [boundaryCap, hk] at hxcap
  exact ⟨⟨hxcap.1.1, hr x hx⟩, hxcap.2⟩

/-!
## Exact spherical graph identity
-/

/-- Inside the spherical graph region, membership in the unit ball is
equivalent to the normal coordinate lying strictly between the two sphere
graphs. -/
private theorem mem_domain_iff_abs_normal_lt_sphereHeight
    (x : ℝ^n)
    (htan : ‖HalfSpace.boundaryProjection n x‖ < 1) :
    x ∈ domain n ↔
      |x (lastIndex (n := n))| < GraphChart.sphereHeight n x := by
  have hdecomp := norm_sq_eq_normal_add_tangential n x
  have hrad :
      0 < GraphChart.sphereRadicand n x := by
    change 0 < 1 - ‖HalfSpace.boundaryProjection n x‖ ^ 2
    nlinarith [norm_nonneg (HalfSpace.boundaryProjection n x)]
  have hsqrt_nonneg :
      0 ≤ GraphChart.sphereHeight n x := by
    exact Real.sqrt_nonneg _
  have hsqrt_sq :
      (GraphChart.sphereHeight n x) ^ 2 =
        1 - ‖HalfSpace.boundaryProjection n x‖ ^ 2 := by
    exact Real.sq_sqrt hrad.le
  rw [domain, mem_ball, dist_zero_right]
  constructor
  · intro hnorm
    apply
      (sq_lt_sq₀ (abs_nonneg (x (lastIndex (n := n)))) hsqrt_nonneg).mp
    rw [sq_abs, hsqrt_sq]
    nlinarith [norm_nonneg x]
  · intro habs
    have habs_sq :
        |x (lastIndex (n := n))| ^ 2 <
          (GraphChart.sphereHeight n x) ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg (x (lastIndex (n := n)))) hsqrt_nonneg).mpr habs
    rw [sq_abs, hsqrt_sq] at habs_sq
    nlinarith [norm_nonneg x]

/-!
## Coordinate-conjugated graph charts
-/

/-- Positive spherical graph flattening after moving coordinate `i` to the
normal slot. -/
private def positiveGlobalHomeomorph
    (i : Fin n) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    ℝ^n ≃ₜ ℝ^n :=
  (coordinateSwap n i).toHomeomorph.trans
    (GraphChart.positiveHomeomorph n g hg)

/-- Negative spherical graph flattening after moving coordinate `i` to the
normal slot. -/
private def negativeGlobalHomeomorph
    (i : Fin n) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    ℝ^n ≃ₜ ℝ^n :=
  (coordinateSwap n i).toHomeomorph.trans
    (GraphChart.negativeHomeomorph n g hg)

@[simp]
private theorem positiveGlobalHomeomorph_symm_apply
    (i : Fin n) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) (y : ℝ^n) :
    (positiveGlobalHomeomorph n i g hg).symm y =
      coordinateSwap n i (GraphChart.positiveMap n g y) := by
  rw [positiveGlobalHomeomorph, Homeomorph.symm_trans_apply]
  exact coordinateSwap_symm_apply n i _

@[simp]
private theorem negativeGlobalHomeomorph_symm_apply
    (i : Fin n) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) (y : ℝ^n) :
    (negativeGlobalHomeomorph n i g hg).symm y =
      coordinateSwap n i (GraphChart.negativeMapInverse n g y) := by
  rw [negativeGlobalHomeomorph, Homeomorph.symm_trans_apply]
  exact coordinateSwap_symm_apply n i _

/-- The positive graph chart restricted to its quantitative source. -/
private def positiveChart
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  GraphChart.restrictHomeomorph n
    (positiveGlobalHomeomorph n i g hg)
    (positiveSource n i r) (isOpen_positiveSource n i r)

/-- The negative graph chart restricted to its quantitative source. -/
private def negativeChart
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  GraphChart.restrictHomeomorph n
    (negativeGlobalHomeomorph n i g hg)
    (negativeSource n i r) (isOpen_negativeSource n i r)

@[simp]
private theorem positiveChart_source
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    (positiveChart n i r g hg).source = positiveSource n i r :=
  rfl

@[simp]
private theorem negativeChart_source
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    (negativeChart n i r g hg).source = negativeSource n i r :=
  rfl

@[simp]
private theorem positiveChart_symm_apply
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (y : ℝ^n) :
    (positiveChart n i r g hg).symm y =
      coordinateSwap n i (GraphChart.positiveMap n g y) :=
  positiveGlobalHomeomorph_symm_apply n i g hg y

@[simp]
private theorem negativeChart_symm_apply
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (y : ℝ^n) :
    (negativeChart n i r g hg).symm y =
      coordinateSwap n i (GraphChart.negativeMapInverse n g y) :=
  negativeGlobalHomeomorph_symm_apply n i g hg y

private theorem positiveChart_contDiff
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ∞) :
    ContDiff ℝ m fun x ↦
      positiveChart n i r g (hg.of_le (by norm_num)) x := by
  exact
    (GraphChart.positiveMap_contDiff n m
      (hg.of_le (by exact_mod_cast le_top))).comp
      (coordinateSwap_contDiff n i m)

private theorem positiveChart_symm_contDiff
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ∞) :
    ContDiff ℝ m fun y ↦
      (positiveChart n i r g (hg.of_le (by norm_num))).symm y := by
  have hfun :
      (fun y ↦
        (positiveChart n i r g (hg.of_le (by norm_num))).symm y) =
        coordinateSwap n i ∘ GraphChart.positiveMap n g := by
    funext y
    simp only [positiveChart_symm_apply, Function.comp_apply]
  rw [hfun]
  exact
    (coordinateSwap_contDiff n i m).comp
      (GraphChart.positiveMap_contDiff n m
        (hg.of_le (by exact_mod_cast le_top)))

private theorem negativeChart_contDiff
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ∞) :
    ContDiff ℝ m fun x ↦
      negativeChart n i r g (hg.of_le (by norm_num)) x := by
  exact
    (GraphChart.negativeMap_contDiff n m
      (hg.of_le (by exact_mod_cast le_top))).comp
      (coordinateSwap_contDiff n i m)

private theorem negativeChart_symm_contDiff
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ∞) :
    ContDiff ℝ m fun y ↦
      (negativeChart n i r g (hg.of_le (by norm_num))).symm y := by
  have hfun :
      (fun y ↦
        (negativeChart n i r g (hg.of_le (by norm_num))).symm y) =
        coordinateSwap n i ∘ GraphChart.negativeMapInverse n g := by
    funext y
    simp only [negativeChart_symm_apply, Function.comp_apply]
  rw [hfun]
  exact
    (coordinateSwap_contDiff n i m).comp
      (GraphChart.negativeMapInverse_contDiff n m
        (hg.of_le (by exact_mod_cast le_top)))

private theorem positiveChart_target_bounded
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    Bornology.IsBounded (positiveChart n i r g hg).target :=
  GraphChart.restrictHomeomorph_target_bounded n
    (positiveGlobalHomeomorph n i g hg)
    (positiveSource n i r) (isOpen_positiveSource n i r)
    (bounded_positiveSource n i r)

private theorem negativeChart_target_bounded
    (i : Fin n) (r : ℝ) (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    Bornology.IsBounded (negativeChart n i r g hg).target :=
  GraphChart.restrictHomeomorph_target_bounded n
    (negativeGlobalHomeomorph n i g hg)
    (negativeSource n i r) (isOpen_negativeSource n i r)
    (bounded_negativeSource n i r)

/-- Exact agreement of a global sphere-height extension at every
tangential point in the quantitative chart cylinder. -/
private theorem globalHeight_at_boundaryProjection
    {r : ℝ} {g : ℝ^n → ℝ}
    (hEq :
      Set.EqOn g (GraphChart.sphereHeight n)
        (GraphChart.tangentialCylinder n r))
    {x : ℝ^n}
    (hx : ‖HalfSpace.boundaryProjection n x‖ < r) :
    g (HalfSpace.boundaryProjection n x) =
      GraphChart.sphereHeight n x := by
  have hmem :
      HalfSpace.boundaryProjection n x ∈
        GraphChart.tangentialCylinder n r := by
    change
      ‖HalfSpace.boundaryProjection n
        (HalfSpace.boundaryProjection n x)‖ ≤ r
    rw [HalfSpace.boundaryProjection_idempotent]
    exact hx.le
  calc
    g (HalfSpace.boundaryProjection n x) =
        GraphChart.sphereHeight n (HalfSpace.boundaryProjection n x) :=
      hEq hmem
    _ = GraphChart.sphereHeight n x := by
      simp [GraphChart.sphereHeight, GraphChart.sphereRadicand]

/-- On a positive quantitative source, the conjugated graph chart flattens
the unit ball exactly to the upper half-space. -/
private theorem positiveChart_mem_iff_upper
    (i : Fin n) {r : ℝ} (hr : r < 1)
    {g : ℝ^n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hEq :
      Set.EqOn g (GraphChart.sphereHeight n)
        (GraphChart.tangentialCylinder n r))
    (x : ℝ^n) (hx : x ∈ positiveSource n i r) :
    (x ∈ domain n ↔
      positiveChart n i r g (hg.of_le (by norm_num)) x ∈
        SobolevSpace.HalfSpace.upper n) := by
  let y := coordinateSwap n i x
  have htan : ‖HalfSpace.boundaryProjection n y‖ < r := hx.1.2
  have htan_one : ‖HalfSpace.boundaryProjection n y‖ < 1 :=
    htan.trans hr
  have hheight :
      g (HalfSpace.boundaryProjection n y) =
        GraphChart.sphereHeight n y :=
    globalHeight_at_boundaryProjection n hEq htan
  calc
    x ∈ domain n ↔ y ∈ domain n := by
      simp only [domain, mem_ball, dist_zero_right, y, coordinateSwap_norm]
    _ ↔ |y (lastIndex (n := n))| < GraphChart.sphereHeight n y :=
      mem_domain_iff_abs_normal_lt_sphereHeight n y htan_one
    _ ↔ x i < GraphChart.sphereHeight n y := by
      rw [coordinateSwap_apply_normal, abs_of_pos hx.1.1]
    _ ↔ x i < g (HalfSpace.boundaryProjection n y) := by
      rw [hheight]
    _ ↔ GraphChart.positiveMap n g y ∈
          SobolevSpace.HalfSpace.upper n := by
      symm
      simpa only [coordinateSwap_apply_normal, y] using
        GraphChart.positiveMap_mem_upper_iff n g y
    _ ↔ positiveChart n i r g (hg.of_le (by norm_num)) x ∈
          SobolevSpace.HalfSpace.upper n := by
      rfl

/-- On a negative quantitative source, the conjugated graph chart flattens
the unit ball exactly to the upper half-space. -/
private theorem negativeChart_mem_iff_upper
    (i : Fin n) {r : ℝ} (hr : r < 1)
    {g : ℝ^n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hEq :
      Set.EqOn g (GraphChart.sphereHeight n)
        (GraphChart.tangentialCylinder n r))
    (x : ℝ^n) (hx : x ∈ negativeSource n i r) :
    (x ∈ domain n ↔
      negativeChart n i r g (hg.of_le (by norm_num)) x ∈
        SobolevSpace.HalfSpace.upper n) := by
  let y := coordinateSwap n i x
  have htan : ‖HalfSpace.boundaryProjection n y‖ < r := hx.1.2
  have htan_one : ‖HalfSpace.boundaryProjection n y‖ < 1 :=
    htan.trans hr
  have hheight :
      g (HalfSpace.boundaryProjection n y) =
        GraphChart.sphereHeight n y :=
    globalHeight_at_boundaryProjection n hEq htan
  calc
    x ∈ domain n ↔ y ∈ domain n := by
      simp only [domain, mem_ball, dist_zero_right, y, coordinateSwap_norm]
    _ ↔ |y (lastIndex (n := n))| < GraphChart.sphereHeight n y :=
      mem_domain_iff_abs_normal_lt_sphereHeight n y htan_one
    _ ↔ -x i < GraphChart.sphereHeight n y := by
      rw [coordinateSwap_apply_normal, abs_of_neg hx.1.1]
    _ ↔ -x i < g (HalfSpace.boundaryProjection n y) := by
      rw [hheight]
    _ ↔ GraphChart.negativeMap n g y ∈
          SobolevSpace.HalfSpace.upper n := by
      symm
      simpa only [coordinateSwap_apply_normal, y] using
        GraphChart.negativeMap_mem_upper_iff n g y
    _ ↔ negativeChart n i r g (hg.of_le (by norm_num)) x ∈
          SobolevSpace.HalfSpace.upper n := by
      rfl

/-!
## Finite chart family and operational atlas
-/

/-- The complete data carried by one signed coordinate chart. -/
private structure ChartPackage (k : Fin (n + n)) where
  chart : OpenPartialHomeomorph (ℝ^n) (ℝ^n)
  cutoff_support_subset_source :
    tsupport ((boundaryCover n).boundaryCutoff k).toFun ⊆ chart.source
  chart_mem_iff_upper :
    ∀ x ∈ chart.source,
      (x ∈ domain n ↔ chart x ∈ SobolevSpace.HalfSpace.upper n)
  chart_target_bounded :
    Bornology.IsBounded chart.target
  chart_contDiff_two :
    ContDiff ℝ 2 fun x ↦ chart x
  chart_symm_contDiff_two :
    ContDiff ℝ 2 fun y ↦ chart.symm y

/-- Construction of the positive chart package for a positive signed
coordinate index. -/
private theorem nonempty_positiveChartPackage
    (k : Fin (n + n)) (i : Fin n)
    (hk :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inl i) :
    Nonempty (ChartPackage n k) := by
  obtain ⟨r, hr, hsupport⟩ :=
    exists_supportRadius n k i (Or.inl hk)
  obtain ⟨g, hg, hEq⟩ :=
    GraphChart.exists_globalSphereHeight_contDiff_eqOn n hr.2
  let hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  refine ⟨{
    chart := positiveChart n i r g hg1
    cutoff_support_subset_source := ?_
    chart_mem_iff_upper := ?_
    chart_target_bounded := ?_
    chart_contDiff_two := ?_
    chart_symm_contDiff_two := ?_ }⟩
  · rw [positiveChart_source]
    exact positiveCutoff_support_subset_source n k i hk hsupport
  · intro x hx
    rw [positiveChart_source] at hx
    simpa only [hg1] using
      positiveChart_mem_iff_upper n i hr.2 hg hEq x hx
  · exact positiveChart_target_bounded n i r g hg1
  · simpa only [hg1] using
      (positiveChart_contDiff n i r g hg 2).of_le (by norm_num)
  · simpa only [hg1] using
      (positiveChart_symm_contDiff n i r g hg 2).of_le (by norm_num)

/-- Construction of the negative chart package for a negative signed
coordinate index. -/
private theorem nonempty_negativeChartPackage
    (k : Fin (n + n)) (i : Fin n)
    (hk :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k =
        Sum.inr i) :
    Nonempty (ChartPackage n k) := by
  obtain ⟨r, hr, hsupport⟩ :=
    exists_supportRadius n k i (Or.inr hk)
  obtain ⟨g, hg, hEq⟩ :=
    GraphChart.exists_globalSphereHeight_contDiff_eqOn n hr.2
  let hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  refine ⟨{
    chart := negativeChart n i r g hg1
    cutoff_support_subset_source := ?_
    chart_mem_iff_upper := ?_
    chart_target_bounded := ?_
    chart_contDiff_two := ?_
    chart_symm_contDiff_two := ?_ }⟩
  · rw [negativeChart_source]
    exact negativeCutoff_support_subset_source n k i hk hsupport
  · intro x hx
    rw [negativeChart_source] at hx
    simpa only [hg1] using
      negativeChart_mem_iff_upper n i hr.2 hg hEq x hx
  · exact negativeChart_target_bounded n i r g hg1
  · simpa only [hg1] using
      (negativeChart_contDiff n i r g hg 2).of_le (by norm_num)
  · simpa only [hg1] using
      (negativeChart_symm_contDiff n i r g hg 2).of_le (by norm_num)

/-- Every one of the `2n` signed coordinate indices carries an explicitly
constructed chart package. -/
private theorem nonempty_chartPackage (k : Fin (n + n)) :
    Nonempty (ChartPackage n k) := by
  generalize hs :
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm k = s
  rcases s with i | i
  · exact nonempty_positiveChartPackage n k i hs
  · exact nonempty_negativeChartPackage n k i hs

/-- The constructed chart package at a signed coordinate index. -/
private def chartPackage (k : Fin (n + n)) : ChartPackage n k :=
  Classical.choice (nonempty_chartPackage n k)

/-- The globally represented order-two flattening family attached to
the unit-ball boundary cover. No external chart hypothesis is used. -/
@[no_expose]
def c2FlatteningCharts :
    Boundary.C2FlatteningCharts (boundaryCover n) where
  chart := fun k ↦ (chartPackage n k).chart
  cutoff_support_subset_source := fun k ↦
    (chartPackage n k).cutoff_support_subset_source
  chart_contDiff_two := fun k ↦
    (chartPackage n k).chart_contDiff_two
  chart_symm_contDiff_two := fun k ↦
    (chartPackage n k).chart_symm_contDiff_two
  chart_mem_iff_upper := fun k ↦
    (chartPackage n k).chart_mem_iff_upper
  chart_target_bounded := fun k ↦
    (chartPackage n k).chart_target_bounded

/-- The concrete operational `C²` boundary atlas on the open Euclidean
unit ball in dimension `n`. -/
@[reducible]
def c2BoundaryAtlas :
    SobolevSpace.C2BoundaryAtlas n (domain n) :=
  (c2FlatteningCharts n).toC2BoundaryAtlas

end SobolevSpace.Boundary.Atlas.UnitBall.ConcreteAtlas
