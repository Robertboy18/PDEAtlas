/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.CoordinateReflection
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Euclidean half-space geometry

The open upper half-space `ℝ^n₊ = {x | xₙ > 0}` is the model domain for boundary questions. The
extension theorem for `W^{1,p}` of a bounded `C¹` domain is proved by flattening the boundary and
reflecting across the hyperplane `{xₙ = 0}` (Evans, PDE, §5.4), and the trace theorem is proved
first on the half-space and then transported by charts (Evans, PDE, §5.5). We collect the
geometry those arguments need, with the last coordinate `PDE.Common.lastIndex` playing the role of
the normal direction.

The reflection `reflect x = (x', -xₙ)` is a linear isometry, hence preserves Lebesgue measure,
exchanges the upper and lower half-spaces, and fixes the boundary hyperplane pointwise. Reflection
in a tangential coordinate `xᵢ ↦ -xᵢ` (`i ≠ n`) preserves the upper half-space and the restricted
measure. The distance from a point to the hyperplane, and to the frontier of the half-space, is
`|xₙ|`, and the hyperplane itself is Lebesgue-null, so up to a null set the complement of the upper
half-space is the lower one.

## Main results

* `upper`, `lower`, `boundary`, `boundaryProjection`: the two open half-spaces, the hyperplane
  `{xₙ = 0}`, and orthogonal projection onto it, which is smooth (`contDiff_boundaryProjection`).
* `infDist_boundary`, `infDist_frontier_upper_eq_last`: `dist(x, {xₙ = 0}) = |xₙ|`.
* `reflect`, `reflectLinearIsometryEquiv`, `measurePreserving_reflect`,
  `measurePreserving_reflect_restrict_lower`: reflection as a measure-preserving linear isometry,
  also between `volume.restrict lower` and `volume.restrict upper`.
* `frontier_upper`, `volume_boundary`, `compl_upper_ae_eq_lower`: the frontier of the upper
  half-space is the hyperplane, which has measure zero.
* `coordinateReflection_mem_upper_iff`, `measurePreserving_coordinateReflection_restrict_upper`:
  tangential coordinate reflections preserve the upper half-space and its restricted measure.

## Implementation notes

The hypothesis `[Fact (0 < n)]` is needed to name the last coordinate. The notations `ℝ^n₊` and
`ℝ^n₋` abbreviate `upper n` and `lower n`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, for extension by reflection
  across `{x_n = 0}`, and §5.5, Theorem 1, pp. 272-273, for the trace theorem, proved first near a
  flat boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace

open Set MeasureTheory

namespace HalfSpace

variable (n : ℕ) [Fact (0 < n)]

/-- The (open) upper half-space `{x | xₙ > 0}` in `ℝ^n`, using the last coordinate. -/
def upper : Set (ℝ^n) :=
  {x | x (PDE.Common.lastIndex (n := n)) > 0}

/-- The (open) lower half-space `{x | xₙ < 0}` in `ℝ^n`, using the last coordinate. -/
def lower : Set (ℝ^n) :=
  {x | x (PDE.Common.lastIndex (n := n)) < 0}

/-- The boundary hyperplane `{x | xₙ = 0}` of the upper half-space. -/
def boundary : Set (ℝ^n) :=
  {x | x (PDE.Common.lastIndex (n := n)) = 0}

/-- The closed upper half-plane is the closure of the open one. -/
theorem closure_upper_two : closure (upper 2) = {x : ℝ^2 | 0 ≤ x 1} :=
  PDE.Common.closure_coordinateUpperHalfSpace (1 : Fin 2)

/-- Orthogonal projection onto the boundary hyperplane of the upper
half-space. -/
def boundaryProjection (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    if i = PDE.Common.lastIndex (n := n) then 0 else x i

/-- The boundary projection has zero normal coordinate. -/
@[simp]
theorem boundaryProjection_apply_last (x : ℝ^n) :
    boundaryProjection n x (PDE.Common.lastIndex (n := n)) = 0 := by
  simp [boundaryProjection]

/-- The boundary projection leaves every tangential coordinate unchanged. -/
@[simp]
theorem boundaryProjection_apply_of_ne_last
    (x : ℝ^n) {i : Fin n}
    (hi : i ≠ PDE.Common.lastIndex (n := n)) :
    boundaryProjection n x i = x i := by
  simp [boundaryProjection, hi]

/-- Projecting twice onto the boundary hyperplane is the same as projecting once. -/
@[simp]
theorem boundaryProjection_idempotent (x : ℝ^n) :
    boundaryProjection n (boundaryProjection n x) = boundaryProjection n x := by
  ext i
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst i
    simp
  · simp [boundaryProjection_apply_of_ne_last, hi]

/-- The boundary projection is smooth to every requested order. -/
theorem contDiff_boundaryProjection (m : ℕ∞) :
    ContDiff ℝ m (boundaryProjection n) := by
  rw [show boundaryProjection n =
      (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
        (fun x : ℝ^n ↦ fun i ↦ if i = PDE.Common.lastIndex (n := n) then 0 else x i) by
    funext x
    rfl]
  exact
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp <|
      contDiff_pi' fun i ↦ by
        by_cases hi : i = PDE.Common.lastIndex (n := n)
        · simpa [hi] using
            (contDiff_const : ContDiff ℝ m fun _ : ℝ^n ↦ (0 : ℝ))
        · simpa [hi] using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- The boundary projection lies on the boundary hyperplane. -/
theorem boundaryProjection_mem_boundary (x : ℝ^n) :
    boundaryProjection n x ∈ boundary n := by
  simp [boundary]

/-- Projecting to the boundary changes only the normal coordinate. -/
theorem dist_boundaryProjection (x : ℝ^n) :
    dist x (boundaryProjection n x) =
      |x (PDE.Common.lastIndex (n := n))| := by
  rw [dist_eq_norm]
  classical
  have hdiff :
      x - boundaryProjection n x =
        x (PDE.Common.lastIndex (n := n)) •
          EuclideanSpace.single
            (PDE.Common.lastIndex (n := n)) (1 : ℝ) := by
    ext i
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst hi
      simp [boundaryProjection]
    · simp [boundaryProjection, hi]
  rw [hdiff, norm_smul]
  simp

/-- Every boundary point is at least the absolute normal-coordinate
distance away. -/
theorem abs_last_le_dist_of_mem_boundary
    (x : ℝ^n) {y : ℝ^n} (hy : y ∈ boundary n) :
    |x (PDE.Common.lastIndex (n := n))| ≤ dist x y := by
  rw [dist_eq_norm]
  have h := EuclideanSpace.abs_apply_le_norm (n := n) (x - y)
    (PDE.Common.lastIndex (n := n))
  change y (PDE.Common.lastIndex (n := n)) = 0 at hy
  rw [PiLp.sub_apply, hy, sub_zero] at h
  exact h

/-- The boundary hyperplane is nonempty. -/
theorem boundary_nonempty : (boundary n).Nonempty :=
  ⟨0, by simp [boundary]⟩

/-- Distance to the boundary hyperplane is the absolute value of the
normal coordinate. -/
theorem infDist_boundary (x : ℝ^n) :
    Metric.infDist x (boundary n) =
      |x (PDE.Common.lastIndex (n := n))| := by
  apply le_antisymm
  · calc
      Metric.infDist x (boundary n)
          ≤ dist x (boundaryProjection n x) :=
        Metric.infDist_le_dist_of_mem
          (boundaryProjection_mem_boundary (n := n) x)
      _ = |x (PDE.Common.lastIndex (n := n))| :=
        dist_boundaryProjection (n := n) x
  · rw [Metric.le_infDist (boundary_nonempty (n := n))]
    intro y hy
    exact abs_last_le_dist_of_mem_boundary (n := n) x hy

/-- The open upper half-space in `ℝ^n`. -/
notation:arg "ℝ^" n:arg "₊" => SobolevSpace.HalfSpace.upper n

/-- The open lower half-space in `ℝ^n`. -/
notation:arg "ℝ^" n:arg "₋" => SobolevSpace.HalfSpace.lower n

/-- Reflection in the last coordinate hyperplane. -/
def reflect : ℝ^n → ℝ^n :=
  fun x ↦
    WithLp.toLp 2 (fun i ↦ if i = PDE.Common.lastIndex (n := n) then -x i else x i)

/-- Reflection negates the last coordinate. -/
@[simp] theorem reflect_apply_last (x : ℝ^n) :
    reflect n x (PDE.Common.lastIndex (n := n)) =
      -x (PDE.Common.lastIndex (n := n)) := by
  simp [reflect]

/-- Reflection fixes every coordinate other than the last one. -/
@[simp] theorem reflect_apply_of_ne_last (x : ℝ^n) {i : Fin n}
    (hi : i ≠ PDE.Common.lastIndex (n := n)) :
    reflect n x i = x i := by
  simp [reflect, hi]

/-- Reflection across the boundary hyperplane is an involution. -/
theorem reflect_involutive : Function.Involutive (reflect n) := by
  intro x
  ext i
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst hi
    simp [reflect]
  · simp [reflect, hi]

/-- Reflection exchanges membership in the upper and lower half-spaces. -/
theorem mem_upper_reflect_iff (x : ℝ^n) : reflect n x ∈ upper n ↔ x ∈ lower n := by
  simp [upper, lower]

/-- Reflection exchanges membership in the lower and upper half-spaces. -/
theorem mem_lower_reflect_iff (x : ℝ^n) : reflect n x ∈ lower n ↔ x ∈ upper n := by
  simp [upper, lower]

/-- The open upper half-space is convex. -/
theorem convex_upper : Convex ℝ (upper n) := by
  let q : ℝ^n →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).toLinearMap
  change Convex ℝ (q ⁻¹' Ioi (0 : ℝ))
  exact (convex_Ioi (0 : ℝ)).linear_preimage q

/-- Two points in the upper half-space cannot be related by reflection across its boundary. -/
theorem ne_reflect_of_mem_upper {x y : ℝ^n} (hx : x ∈ upper n) (hy : y ∈ upper n) :
    y ≠ reflect n x := by
  intro hxy
  have hcoord := congrArg (fun z : ℝ^n ↦ z (PDE.Common.lastIndex (n := n))) hxy
  simp only [reflect_apply_last] at hcoord
  have hxpos : 0 < x (PDE.Common.lastIndex (n := n)) := hx
  have hypos : 0 < y (PDE.Common.lastIndex (n := n)) := hy
  linarith

/-- Translation by a vector with zero normal component preserves the upper
half-space exactly.  This is the geometric reason that boundary difference
quotients may be taken in tangential directions without crossing the
flattened boundary. -/
theorem add_mem_upper_iff_of_last_eq_zero
    (x a : ℝ^n) (ha : a (PDE.Common.lastIndex (n := n)) = 0) :
    x + a ∈ upper n ↔ x ∈ upper n := by
  simp only [upper, Set.mem_ofPred_eq, PiLp.add_apply, ha, add_zero]

/-- Set-level form of tangential translation invariance of the upper
half-space. -/
theorem preimage_add_eq_upper_of_last_eq_zero
    (a : ℝ^n) (ha : a (PDE.Common.lastIndex (n := n)) = 0) :
    (fun x : ℝ^n ↦ x + a) ⁻¹' upper n = upper n := by
  ext x
  exact add_mem_upper_iff_of_last_eq_zero n x a ha

/-- The lower half-space is the reflection preimage of the upper half-space. -/
theorem lower_eq_preimage_reflect_upper : lower n = (reflect n) ⁻¹' upper n := by
  ext x
  simp [mem_upper_reflect_iff (n := n) (x := x)]

/-- The upper half-space is the reflection preimage of the lower half-space. -/
theorem upper_eq_preimage_reflect_lower : upper n = (reflect n) ⁻¹' lower n := by
  ext x
  simp [mem_lower_reflect_iff (n := n) (x := x)]

/-- Reflection across the final coordinate hyperplane as a linear equivalence. -/
noncomputable def reflectLinearEquiv : ℝ^n ≃ₗ[ℝ] ℝ^n where
  toFun := reflect n
  invFun := reflect n
  left_inv := (reflect_involutive (n := n))
  right_inv := (reflect_involutive (n := n))
  map_add' := by
    classical
    intro x y
    ext i
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst hi
      simp [reflect, add_comm]
    · simp [reflect, hi]
  map_smul' := by
    classical
    intro c x
    ext i
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst hi
      simp [reflect]
    · simp [reflect, hi]

/-- Reflection across the boundary hyperplane preserves the Euclidean norm. -/
theorem norm_reflect (x : ℝ^n) : ‖reflect n x‖ = ‖x‖ := by
  classical
  have hsq : ‖reflect n x‖ ^ 2 = ‖x‖ ^ 2 := by
    -- Compare squared norms as sums of squares of coordinates.
    simp [EuclideanSpace.norm_sq_eq, reflect]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- The linear reflection acts by `reflect`. -/
@[simp]
theorem reflectLinearEquiv_apply (x : ℝ^n) :
    reflectLinearEquiv n x = reflect n x :=
  rfl

/-- Reflection preserves subtraction. -/
theorem reflect_sub (x y : ℝ^n) :
    reflect n (x - y) = reflect n x - reflect n y := by
  simpa using (reflectLinearEquiv n).map_sub x y

/-- Reflection fixes every point on the boundary hyperplane. -/
theorem reflect_eq_self_of_mem_boundary {x : ℝ^n} (hx : x ∈ boundary n) :
    reflect n x = x := by
  ext i
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst hi
    simp [boundary] at hx
    simp [hx]
  · exact reflect_apply_of_ne_last n x hi

/-- Subtracting a reflected point from a boundary point reflects the original difference. -/
theorem sub_reflect_eq_reflect_sub_of_mem_boundary (x : ℝ^n) {y : ℝ^n}
    (hy : y ∈ boundary n) :
    y - reflect n x = reflect n (y - x) := by
  rw [reflect_sub, reflect_eq_self_of_mem_boundary n hy]

/-- Reflection gives equal distances from a boundary point to a point and its image. -/
theorem norm_sub_reflect_eq_of_mem_boundary (x : ℝ^n) {y : ℝ^n}
    (hy : y ∈ boundary n) :
    ‖y - reflect n x‖ = ‖y - x‖ := by
  rw [sub_reflect_eq_reflect_sub_of_mem_boundary n x hy, norm_reflect]

/-- Reflection across the final coordinate hyperplane as a linear isometry equivalence. -/
noncomputable def reflectLinearIsometryEquiv : ℝ^n ≃ₗᵢ[ℝ] ℝ^n :=
  LinearIsometryEquiv.mk (reflectLinearEquiv (n := n)) (norm_reflect (n := n))

/-- The linear-isometry reflection acts by `reflect`. -/
@[simp]
theorem reflectLinearIsometryEquiv_apply (x : ℝ^n) :
    reflectLinearIsometryEquiv n x = reflect n x :=
  rfl

/-- The function underlying the linear-isometry reflection is `reflect`. -/
@[simp]
theorem coe_reflectLinearIsometryEquiv :
    ⇑(reflectLinearIsometryEquiv n) = reflect n :=
  rfl

/-- Reflection across the boundary hyperplane preserves Lebesgue measure. -/
theorem measurePreserving_reflect :
    MeasurePreserving (reflect n : ℝ^n → ℝ^n) (volume : Measure (ℝ^n)) (volume : Measure (ℝ^n))
      :=
  LinearIsometryEquiv.measurePreserving (reflectLinearIsometryEquiv (n := n))

/-- Reflecting a coordinate other than the normal coordinate preserves the
upper half-space. -/
theorem coordinateReflection_mem_upper_iff
    {i : Fin n} (hi : i ≠ PDE.Common.lastIndex (n := n)) (x : ℝ^n) :
    PDE.Common.coordinateReflection i x ∈ upper n ↔ x ∈ upper n := by
  simp only [upper, Set.mem_ofPred_eq]
  rw [PDE.Common.coordinateReflection_apply_of_ne]
  exact Ne.symm hi

/-- The upper half-space is invariant under reflection in a tangential
coordinate hyperplane. -/
theorem preimage_coordinateReflection_upper
    {i : Fin n} (hi : i ≠ PDE.Common.lastIndex (n := n)) :
    PDE.Common.coordinateReflection i ⁻¹' upper n = upper n := by
  ext x
  exact coordinateReflection_mem_upper_iff n hi x

/-- Tangential coordinate reflection commutes with reflection across the
boundary of the upper half-space. -/
theorem coordinateReflection_reflect_comm
    {i : Fin n} (hi : i ≠ PDE.Common.lastIndex (n := n)) (x : ℝ^n) :
    PDE.Common.coordinateReflection i (reflect n x) =
      reflect n (PDE.Common.coordinateReflection i x) := by
  ext j
  by_cases hjlast : j = PDE.Common.lastIndex (n := n)
  · subst j
    rw [PDE.Common.coordinateReflection_apply_of_ne _ _ (Ne.symm hi)]
    simp only [reflect_apply_last, neg_inj]
    exact
      (PDE.Common.coordinateReflection_apply_of_ne i
        (PDE.Common.lastIndex (n := n)) (Ne.symm hi) x).symm
  · by_cases hji : j = i
    · subst j
      rw [PDE.Common.coordinateReflection_apply_same]
      rw [reflect_apply_of_ne_last _ _ hi]
      rw [reflect_apply_of_ne_last _ _ hi]
      exact (PDE.Common.coordinateReflection_apply_same i x).symm
    · rw [PDE.Common.coordinateReflection_apply_of_ne _ _ hji]
      rw [reflect_apply_of_ne_last _ _ hjlast]
      rw [reflect_apply_of_ne_last _ _ hjlast]
      exact (PDE.Common.coordinateReflection_apply_of_ne i j hji x).symm

/-- The upper half-space is open. -/
theorem isOpen_upper : IsOpen (upper n) := by
  have hcont : Continuous fun x : ℝ^n ↦ x (PDE.Common.lastIndex (n := n)) := by
    simpa using
      (EuclideanSpace.proj (PDE.Common.lastIndex (n := n)) : ℝ^n →L[ℝ] ℝ).continuous
  simpa [upper, Set.preimage, Set.mem_preimage] using (isOpen_Ioi.preimage hcont)

/-- The lower half-space is open. -/
theorem isOpen_lower : IsOpen (lower n) := by
  have hcont : Continuous fun x : ℝ^n ↦ x (PDE.Common.lastIndex (n := n)) := by
    simpa using
      (EuclideanSpace.proj (PDE.Common.lastIndex (n := n)) : ℝ^n →L[ℝ] ℝ).continuous
  simpa [lower, Set.preimage, Set.mem_preimage] using (isOpen_Iio.preimage hcont)

/-- The topological boundary of the upper half-space is its zero-normal
hyperplane. -/
theorem frontier_upper :
    frontier (upper n) = boundary n := by
  let q : ℝ^n →L[ℝ] ℝ :=
    EuclideanSpace.proj (PDE.Common.lastIndex (n := n))
  have hupper : upper n = q ⁻¹' Set.Ioi (0 : ℝ) := by
    ext x
    simp [upper, q]
  have hsurj : Function.Surjective q := by
    intro t
    refine
      ⟨t • EuclideanSpace.single
        (PDE.Common.lastIndex (n := n)) (1 : ℝ), ?_⟩
    simp [q]
  rw [hupper, q.frontier_preimage hsurj, frontier_Ioi]
  ext x
  simp [boundary, q]

/-- The boundary hyperplane has zero ambient Lebesgue measure. -/
theorem volume_boundary :
    volume (boundary n) = 0 := by
  rw [← frontier_upper (n := n)]
  let q : ℝ^n →L[ℝ] ℝ :=
    EuclideanSpace.proj (PDE.Common.lastIndex (n := n))
  have hupper : upper n = q ⁻¹' Set.Ioi (0 : ℝ) := by
    ext x
    simp [upper, q]
  rw [hupper]
  exact ((convex_Ioi (0 : ℝ)).is_linear_preimage q.isLinear).addHaar_frontier volume

/-- Up to a Lebesgue-null boundary, the complement of the upper half-space
is the lower half-space. -/
theorem compl_upper_ae_eq_lower :
    (upper n)ᶜ =ᵐ[volume] lower n := by
  filter_upwards [compl_mem_ae_iff.mpr (volume_boundary (n := n))] with x hx
  apply propext
  change (¬0 < x (PDE.Common.lastIndex (n := n))) ↔
    x (PDE.Common.lastIndex (n := n)) < 0
  change x (PDE.Common.lastIndex (n := n)) ≠ 0 at hx
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · exact hneg
    · exact (h hpos).elim
  · intro hneg hpos
    linarith

/-- Distance to the topological boundary of the upper half-space is the
absolute normal coordinate. -/
theorem infDist_frontier_upper (x : ℝ^n) :
    Metric.infDist x (frontier (upper n)) =
      |x (PDE.Common.lastIndex (n := n))| := by
  rw [frontier_upper (n := n), infDist_boundary]

/-- Inside the upper half-space, distance to the boundary is the positive
normal coordinate. -/
theorem infDist_frontier_upper_eq_last
    {x : ℝ^n} (hx : x ∈ upper n) :
    Metric.infDist x (frontier (upper n)) =
      x (PDE.Common.lastIndex (n := n)) := by
  rw [infDist_frontier_upper]
  exact abs_of_pos hx

/-- The upper half-space is Lebesgue measurable. -/
theorem measurableSet_upper : MeasurableSet (upper n) :=
  (isOpen_upper n).measurableSet

/-- The lower half-space is Lebesgue measurable. -/
theorem measurableSet_lower : MeasurableSet (lower n) :=
  (isOpen_lower n).measurableSet

/-- Tangential coordinate reflection preserves Lebesgue measure restricted
to the upper half-space. -/
theorem measurePreserving_coordinateReflection_restrict_upper
    {i : Fin n} (hi : i ≠ PDE.Common.lastIndex (n := n)) :
    MeasurePreserving (PDE.Common.coordinateReflection i : ℝ^n → ℝ^n)
      (volume.restrict (upper n)) (volume.restrict (upper n)) := by
  simpa [preimage_coordinateReflection_upper n hi] using
    (PDE.Common.measurePreserving_coordinateReflection i).restrict_preimage
      (s := upper n) (measurableSet_upper (n := n))

/-- Reflection preserves measure after restricting the source to the lower half-space and the
target to the upper half-space. -/
theorem measurePreserving_reflect_restrict_lower :
    MeasurePreserving (reflect n : ℝ^n → ℝ^n)
      (volume.restrict (lower n)) (volume.restrict (upper n)) := by
  -- `MeasurePreserving.restrict_preimage` is exactly the needed lemma:
  -- if `f` is measure-preserving, then it is also measure-preserving between restrictions
  -- `μ.restrict (f ⁻¹' s)` and `ν.restrict s`.
  simpa [lower_eq_preimage_reflect_upper (n := n)] using
    (measurePreserving_reflect (n := n)).restrict_preimage (s := upper n) (measurableSet_upper (n :=
      n))

end HalfSpace

end SobolevSpace
