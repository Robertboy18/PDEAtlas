/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialEmbedding
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator

/-!
# Surface measure for Sobolev traces

The trace operator of a `C¹` domain takes values in `Lᵖ(∂Ω)` with respect to `(n-1)`-dimensional
surface measure on the boundary (Evans, PDE, §5.5; the same measure `dS` appears in the
Gauss–Green formula, Evans, PDE, Appendix C.2). We fix that measure intrinsically as
Mathlib's normalized codimension-one Euclidean Hausdorff measure `μH[n-1]` restricted to the
topological frontier of `Ω`. The normalization is the one for which `μH[n]` on `ℝ^n` is Lebesgue
measure, so on a flat hyperplane the surface measure is ordinary Lebesgue measure in tangential
coordinates.

For the boundary `{xₙ₊₁ = 0}` of the upper half-space in `ℝ^(n+1)` this is made precise:
the tangential embedding `y ↦ (y, 0)` is an isometry onto the
hyperplane, so it pushes Lebesgue measure on `ℝ^n` forward to `flatSurfaceMeasure`, and integrals
over the hyperplane are integrals in tangential coordinates. The tangential projection is then
measure preserving from the hyperplane to `ℝ^n`, which lifts `Lᵖ(ℝ^n)` isometrically to
`Lᵖ(flatSurfaceMeasure)`. Composing with the half-space trace of
`Trace.HalfSpace` gives a trace `H¹(ℝ^(n+1)₊) → L²` of the hyperplane surface measure, with the
same operator norm bound.

## Main results

* `surfaceMeasure`: `μH[n-1]` restricted to `frontier Ω`.
* `flatEmbedding`, `isometry_flatEmbedding`, `range_flatEmbedding`: the isometric inclusion of
  `ℝ^n` as the hyperplane.
* `surfaceMeasure_upperHalfSpace`, `map_flatEmbedding_volume`, `integral_flatSurfaceMeasure`:
  on the half-space, surface measure is the pushforward of tangential Lebesgue measure.
* `flatProjection`, `measurePreserving_flatProjection`, `liftLp`: the tangential projection and
  the induced isometric lift of `Lᵖ` functions.
* `flatTrace`, `norm_flatTrace_le`: the half-space trace valued in `L²` of the hyperplane.

## Implementation notes

In dimension `0` the codimension `n - 1` is truncated to `0` by natural subtraction; this case is
never used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, pp. 272-273, for traces in `L^p(∂U)`, and
  App. C.2, Theorem 1, pp. 711-712, for the Gauss-Green theorem with the surface measure `dS`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Boundary.Geometry.SurfaceMeasure

open MeasureTheory Set
open scoped ENNReal MeasureTheory Sobolev

variable {n : ℕ}

/-- Intrinsic codimension-one surface measure on the boundary of a subset of
`ℝ^n`.  In dimension zero the codimension is truncated to zero. -/
noncomputable def surfaceMeasure (Ω : Set (ℝ^n)) : Measure (ℝ^n) :=
  (Measure.euclideanHausdorffMeasure (n - 1)).restrict (frontier Ω)

/-- The standard inclusion of `ℝ^n` as the final-coordinate-zero hyperplane
in `ℝ^(n+1)`. -/
def flatEmbedding (y : ℝ^n) : ℝ^(n + 1) :=
  Trace.HalfSpace.tangentialEmbedding y

/-- The standard flat embedding as a continuous linear map. -/
noncomputable def flatEmbeddingContinuousLinearMap :
    ℝ^n →L[ℝ] ℝ^(n + 1) :=
  Trace.HalfSpace.tangentialEmbedding.toContinuousLinearMap

/-- The continuous linear flat embedding acts as `flatEmbedding`. -/
@[simp]
theorem flatEmbeddingContinuousLinearMap_apply (y : ℝ^n) :
    flatEmbeddingContinuousLinearMap y = flatEmbedding y := rfl

/-- The flat embedding has zero normal coordinate. -/
@[simp]
theorem flatEmbedding_apply_last (y : ℝ^n) :
    flatEmbedding y (Fin.last n) = 0 := by
  simp [flatEmbedding]

/-- The flat embedding preserves each tangential coordinate. -/
@[simp]
theorem flatEmbedding_apply_castSucc (y : ℝ^n) (i : Fin n) :
    flatEmbedding y i.castSucc = y i := by
  simp [flatEmbedding]

/-- The flat inclusion preserves Euclidean norms. -/
theorem norm_flatEmbedding (y : ℝ^n) : ‖flatEmbedding y‖ = ‖y‖ :=
  Trace.HalfSpace.tangentialEmbedding.norm_map y

/-- The flat inclusion is an isometry. -/
theorem isometry_flatEmbedding : Isometry (flatEmbedding (n := n)) :=
  (Trace.HalfSpace.tangentialEmbedding (n := n)).isometry

/-- The range of the flat inclusion is exactly the final-coordinate-zero
hyperplane. -/
theorem range_flatEmbedding :
    Set.range (flatEmbedding (n := n)) =
      {x : ℝ^(n + 1) | x (Fin.last n) = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact flatEmbedding_apply_last y
  · intro hx
    refine ⟨(Trace.HalfSpace.splitTangentialNormal x).1, ?_⟩
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [flatEmbedding] using hx.symm
    · simp [flatEmbedding]

/-- Normalized `n`-dimensional Hausdorff measure on the flat hyperplane. -/
noncomputable def flatSurfaceMeasure : Measure (ℝ^(n + 1)) :=
  (Measure.euclideanHausdorffMeasure n).restrict
    {x : ℝ^(n + 1) | x (Fin.last n) = 0}

/-- The topological boundary of the upper half-space is its zero-normal
hyperplane. -/
theorem frontier_upperHalfSpace :
    frontier (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩) =
      {x : ℝ^(n + 1) | x (Fin.last n) = 0} := by
  have : Fact (0 < n + 1) := ⟨Nat.zero_lt_succ n⟩
  have hlast : @PDE.Common.lastIndex (n := n + 1) ⟨Nat.zero_lt_succ n⟩ = Fin.last n := by
    apply Fin.ext
    simp [PDE.Common.lastIndex]
  rw [HalfSpace.frontier_upper (n := n + 1)]
  simp [HalfSpace.boundary, hlast]

/-- On the upper half-space, intrinsic codimension-one surface measure is the
flat hyperplane measure used above. -/
theorem surfaceMeasure_upperHalfSpace :
    surfaceMeasure (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩) =
      flatSurfaceMeasure (n := n) := by
  simp [surfaceMeasure, flatSurfaceMeasure, frontier_upperHalfSpace]

/-- Flat surface measure is exactly the pushforward of tangential Lebesgue
measure. -/
theorem map_flatEmbedding_volume :
    Measure.map (flatEmbedding (n := n)) (volume : Measure (ℝ^n)) =
      flatSurfaceMeasure (n := n) := by
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
  rw [(isometry_flatEmbedding (n := n)).map_euclideanHausdorffMeasure]
  exact congrArg
    (fun s : Set (ℝ^(n + 1)) ↦
      (Measure.euclideanHausdorffMeasure n).restrict s)
    (range_flatEmbedding (n := n))

/-- Bounded pieces of the flat hyperplane have finite surface measure. -/
theorem flatSurfaceMeasure_lt_top_of_bounded {s : Set (ℝ^(n + 1))}
    (hsBounded : Bornology.IsBounded s) :
    flatSurfaceMeasure (n := n) s < ∞ := by
  rw [← map_flatEmbedding_volume (n := n),
    (isometry_flatEmbedding (n := n)).isClosedEmbedding.measurableEmbedding.map_apply]
  exact
    ((isometry_flatEmbedding (n := n)).antilipschitzWith.isBounded_preimage
      hsBounded).measure_lt_top

/-- Integration over the flat surface is integration in tangential
coordinates. -/
theorem integral_flatSurfaceMeasure (f : ℝ^(n + 1) → ℝ) :
    (∫ x, f x ∂flatSurfaceMeasure (n := n)) =
      ∫ y : ℝ^n, f (flatEmbedding y) := by
  rw [← map_flatEmbedding_volume (n := n)]
  exact (isometry_flatEmbedding (n := n)).isClosedEmbedding.measurableEmbedding.integral_map f

/-- Tangential projection from the ambient space.  Only its values on the flat
hyperplane matter for `flatSurfaceMeasure`. -/
def flatProjection (x : ℝ^(n + 1)) : ℝ^n :=
  (Trace.HalfSpace.splitTangentialNormal x).1

/-- Tangential projection as a continuous real-linear map. -/
noncomputable def flatProjectionContinuousLinearMap :
    ℝ^(n + 1) →L[ℝ] ℝ^n :=
  (ContinuousLinearMap.fst ℝ (ℝ^n) ℝ).comp
    (Trace.HalfSpace.tangentialNormalContinuousLinearEquiv
      (n := n)).toContinuousLinearMap

/-- The continuous linear tangential projection acts as `flatProjection`. -/
@[simp]
theorem flatProjectionContinuousLinearMap_apply (x : ℝ^(n + 1)) :
    flatProjectionContinuousLinearMap x = flatProjection x := rfl

/-- Tangential projection is a left inverse of the flat embedding. -/
@[simp]
theorem flatProjection_flatEmbedding (y : ℝ^n) :
    flatProjection (flatEmbedding y) = y := by
  simp [flatProjection, flatEmbedding]

/-- On the flat hyperplane, tangential projection followed by inclusion is
the identity. -/
theorem flatEmbedding_flatProjection_of_last_eq_zero
    {x : ℝ^(n + 1)} (hx : x (Fin.last n) = 0) :
    flatEmbedding (flatProjection x) = x := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using hx.symm
  · simp [flatEmbedding, flatProjection]

/-- The tangential projection is continuous. -/
theorem continuous_flatProjection : Continuous (flatProjection (n := n)) :=
  continuous_fst.comp
    (Trace.HalfSpace.tangentialNormalContinuousLinearEquiv (n := n)).continuous

/-- Tangential projection preserves measure when its source is equipped with
flat surface measure. -/
theorem measurePreserving_flatProjection :
    MeasurePreserving (flatProjection (n := n))
      (flatSurfaceMeasure (n := n)) (volume : Measure (ℝ^n)) := by
  refine ⟨continuous_flatProjection (n := n) |>.measurable, ?_⟩
  rw [← map_flatEmbedding_volume (n := n)]
  rw [Measure.map_map
    (continuous_flatProjection (n := n)).measurable
    (isometry_flatEmbedding (n := n)).continuous.measurable]
  have hcomp : flatProjection (n := n) ∘ flatEmbedding (n := n) = id := by
    funext y
    exact flatProjection_flatEmbedding y
  rw [hcomp, Measure.map_id]

/-- Isometric lifting of a tangential `Lᵖ` function with values in a real normed space
to the flat hyperplane. -/
noncomputable def liftLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MeasureTheory.Lp F p (volume : Measure (ℝ^n)) →ₗᵢ[ℝ]
      MeasureTheory.Lp F p (flatSurfaceMeasure (n := n)) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (flatProjection (n := n)) (measurePreserving_flatProjection (n := n))

/-- Almost-everywhere formula for lifting a tangential `Lᵖ` function to the
flat hyperplane. -/
theorem liftLp_apply_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : MeasureTheory.Lp F p (volume : Measure (ℝ^n))) :
    liftLp (n := n) p g =ᵐ[flatSurfaceMeasure (n := n)]
      fun x ↦ g (flatProjection x) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving g
    (measurePreserving_flatProjection (n := n))

/-- The flat trace, valued intrinsically in `L²` of the hyperplane surface
measure. -/
noncomputable def flatTrace :
    H¹(@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (flatSurfaceMeasure (n := n)) :=
  (liftLp (n := n) 2).toContinuousLinearMap.comp
    (Trace.HalfSpace.trace n)

/-- The intrinsic flat trace has the same norm estimate as its tangential
coordinate form. -/
theorem norm_flatTrace_le
    (u : H¹(@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩)) :
    ‖flatTrace u‖ ≤ ‖u‖ := by
  change ‖liftLp (n := n) 2 (Trace.HalfSpace.trace n u)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact Trace.HalfSpace.norm_trace_le n u

end Boundary.Geometry.SurfaceMeasure
end SobolevSpace
