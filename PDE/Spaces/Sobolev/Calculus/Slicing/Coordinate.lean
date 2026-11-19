/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Common.Euclidean.SpaceTime
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Slices along arbitrary Euclidean coordinates

We separate any selected coordinate of `ℝ^(n + 1)` from its
complementary coordinates. The resulting continuous linear and measurable
equivalences preserve Euclidean volume. We also treat the corresponding
one-dimensional slices and identify their derivatives with the selected
partial derivative.

Unlike the tangential-normal coordinates used for the upper half-space, the
selected coordinate here is arbitrary. This is the coordinate geometry used
by the Euclidean ACL theorem (`Slicing.ACL` and `Slicing.ACLConverse`): a
function on `ℝ^(n + 1)` is viewed as a function of `(y, t) ∈ ℝ^n × ℝ`, with
`t` the coordinate along which one differentiates, and Fubini's theorem over
the volume-preserving split reduces statements about `∂ᵢ` to statements about
the one-variable functions `t ↦ f (y, t)` for almost every `y`.

## Main results

* `splitCoordinate`, `joinCoordinate`: the split `x ↦ (x without xᵢ, xᵢ)` and
  its inverse, with `split_joinCoordinate` and `join_splitCoordinate`.
* `coordinateContinuousLinearEquiv`, `coordinateMeasurableEquiv`: the same
  split as a continuous linear equivalence and as a measurable equivalence.
* `measurePreserving_coordinateMeasurableEquiv`: the split carries Lebesgue
  measure on `ℝ^(n + 1)` to the product measure on `ℝ^n × ℝ`.
* `coordinateSlice`, `coordinateDerivativeInSplit`, `deriv_coordinateSlice`:
  the slice `t ↦ f (y, t)` and the identity `d/dt f (y, t) = ∂ᵢ f (y, t)` for
  `C¹` functions `f`.
* Continuity and compact-support lemmas for slices and for the split partial
  derivative, as needed to apply Fubini and pass to limits in the ACL
  theorems.
-/

@[expose] public section

open PDE (SpaceTime partialDeriv coordinateLine)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Slices

open MeasureTheory Set

variable {n : ℕ}

/-- Split off the coordinate indexed by `i`, placing the remaining
coordinates first. -/
def splitCoordinate (i : Fin (n + 1)) (x : ℝ^(n + 1)) : ℝ^n × ℝ :=
  (WithLp.toLp 2 (i.removeNth x), x i)

/-- Reassemble a point from the coordinates complementary to `i` and the
`i`-th coordinate. -/
def joinCoordinate (i : Fin (n + 1)) (p : ℝ^n × ℝ) : ℝ^(n + 1) :=
  WithLp.toLp 2 (i.insertNth p.2 (fun j ↦ p.1 j))

/-- The complementary part of the split lists the coordinates of `x` other
than `xᵢ`, in order, through `Fin.succAbove`. -/
@[simp]
theorem splitCoordinate_fst_apply (i : Fin (n + 1))
    (x : ℝ^(n + 1)) (j : Fin n) :
    (splitCoordinate i x).1 j = x (i.succAbove j) := by
  simp [splitCoordinate, Fin.removeNth_apply]

/-- The selected part of the split is the `i`-th coordinate. -/
@[simp]
theorem splitCoordinate_snd (i : Fin (n + 1)) (x : ℝ^(n + 1)) :
    (splitCoordinate i x).2 = x i :=
  rfl

/-- Joining places the real parameter in the `i`-th coordinate. -/
@[simp]
theorem joinCoordinate_apply_same (i : Fin (n + 1))
    (p : ℝ^n × ℝ) :
    joinCoordinate i p i = p.2 := by
  simp [joinCoordinate]

/-- Joining places the complementary coordinates in the positions other than
`i`. -/
@[simp]
theorem joinCoordinate_apply_succAbove (i : Fin (n + 1))
    (p : ℝ^n × ℝ) (j : Fin n) :
    joinCoordinate i p (i.succAbove j) = p.1 j := by
  simp [joinCoordinate]

/-- Splitting after joining is the identity. -/
@[simp]
theorem split_joinCoordinate (i : Fin (n + 1)) (p : ℝ^n × ℝ) :
    splitCoordinate i (joinCoordinate i p) = p := by
  apply Prod.ext
  · ext j
    simp
  · simp

/-- Joining after splitting is the identity. -/
@[simp]
theorem join_splitCoordinate (i : Fin (n + 1)) (x : ℝ^(n + 1)) :
    joinCoordinate i (splitCoordinate i x) = x := by
  ext j
  rcases i.eq_self_or_eq_succAbove j with (rfl | ⟨k, rfl⟩) <;> simp

/-- Continuous linear equivalence separating the coordinate indexed by
`i`. -/
noncomputable def coordinateContinuousLinearEquiv (i : Fin (n + 1)) :
    ℝ^(n + 1) ≃L[ℝ] ℝ^n × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := splitCoordinate i
      invFun := joinCoordinate i
      left_inv := join_splitCoordinate i
      right_inv := split_joinCoordinate i
      map_add' := by
        intro x y
        apply Prod.ext
        · ext j
          change (x + y) (i.succAbove j) =
            x (i.succAbove j) + y (i.succAbove j)
          simp
        · simp [splitCoordinate]
      map_smul' := by
        intro c x
        apply Prod.ext
        · ext j
          change (c • x) (i.succAbove j) =
            c * x (i.succAbove j)
          simp
        · simp [splitCoordinate] }

/-- The continuous linear split acts by `splitCoordinate`. -/
@[simp]
theorem coordinateContinuousLinearEquiv_apply (i : Fin (n + 1))
    (x : ℝ^(n + 1)) :
    coordinateContinuousLinearEquiv i x = splitCoordinate i x :=
  rfl

/-- The inverse of the continuous linear split acts by `joinCoordinate`. -/
@[simp]
theorem coordinateContinuousLinearEquiv_symm_apply (i : Fin (n + 1))
    (p : ℝ^n × ℝ) :
    (coordinateContinuousLinearEquiv i).symm p = joinCoordinate i p :=
  rfl

/-- Measurable equivalence separating the coordinate indexed by `i`. -/
noncomputable def coordinateMeasurableEquiv (i : Fin (n + 1)) :
    ℝ^(n + 1) ≃ᵐ ℝ^n × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm |>.trans
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) i) |>.trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ))) |>.trans
    MeasurableEquiv.prodComm

/-- The measurable split acts by `splitCoordinate`. -/
@[simp]
theorem coordinateMeasurableEquiv_apply (i : Fin (n + 1))
    (x : ℝ^(n + 1)) :
    coordinateMeasurableEquiv i x = splitCoordinate i x := by
  apply Prod.ext
  · ext j
    simp [coordinateMeasurableEquiv, splitCoordinate,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth_apply]
    rfl
  · simp [coordinateMeasurableEquiv, splitCoordinate,
      MeasurableEquiv.piFinSuccAbove_apply]
    rfl

/-- The inverse of the measurable split acts by `joinCoordinate`. -/
@[simp]
theorem coordinateMeasurableEquiv_symm_apply (i : Fin (n + 1))
    (p : ℝ^n × ℝ) :
    (coordinateMeasurableEquiv i).symm p = joinCoordinate i p :=
  (coordinateMeasurableEquiv i).injective (by simp)

/-- Separating any Euclidean coordinate preserves canonical volume. -/
theorem measurePreserving_coordinateMeasurableEquiv
    (i : Fin (n + 1)) :
    MeasurePreserving (coordinateMeasurableEquiv i) := by
  let eRaw : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
  let eProd : ℝ × (Fin n → ℝ) ≃ᵐ ℝ × ℝ^n :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ))
  have h₁ : MeasurePreserving
      (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm :=
    PiLp.volume_preserving_ofLp (Fin (n + 1))
  have h₂ : MeasurePreserving eRaw := by
    simpa [eRaw] using
      (volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ ℝ) i)
  have h₃ : MeasurePreserving
      eProd
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ^n))) := by
    apply (MeasurePreserving.prod
      (MeasurePreserving.id (volume : Measure ℝ))
      (PiLp.volume_preserving_toLp (Fin n))).congr
    · exact eProd.measurable
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have h₄ : MeasurePreserving
      (MeasurableEquiv.prodComm : ℝ × ℝ^n ≃ᵐ ℝ^n × ℝ)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ^n)))
      ((volume : Measure (ℝ^n)).prod (volume : Measure ℝ)) := by
    apply (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ^n)))).congr
    · exact MeasurableEquiv.prodComm.measurable
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  rw [Measure.volume_eq_prod (ℝ^n) ℝ]
  exact ((h₁.trans h₂).trans h₃).trans h₄

/-- Continuous linear parametrization of the coordinate axis indexed by
`i`. -/
noncomputable def coordinateAxisContinuousLinearMap
    (i : Fin (n + 1)) : ℝ →L[ℝ] ℝ^(n + 1) :=
  (coordinateContinuousLinearEquiv i).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (ℝ^n) ℝ)

/-- A joined point is its zero-coordinate base plus displacement along the
selected coordinate axis. -/
theorem joinCoordinate_eq_base_add_axis
    (i : Fin (n + 1)) (y : ℝ^n) (t : ℝ) :
    joinCoordinate i (y, t) =
      joinCoordinate i (y, 0) + coordinateAxisContinuousLinearMap i t := by
  ext j
  rcases i.eq_self_or_eq_succAbove j with (rfl | ⟨k, rfl⟩) <;>
    simp [coordinateAxisContinuousLinearMap]

/-- Restriction of a function to the line parallel to coordinate `i` above
the complementary-coordinate point `y`. -/
def coordinateSlice (i : Fin (n + 1))
    (f : ℝ^(n + 1) → ℝ) (y : ℝ^n) (t : ℝ) : ℝ :=
  f (joinCoordinate i (y, t))

/-- The `i`-th partial derivative in the corresponding split coordinates. -/
def coordinateDerivativeInSplit (i : Fin (n + 1))
    (f : ℝ^(n + 1) → ℝ) (p : ℝ^n × ℝ) : ℝ :=
  (∂[i] f) (joinCoordinate i p)

private theorem coordinateLine_joinCoordinate
    (i : Fin (n + 1)) (y : ℝ^n) (t s : ℝ) :
    coordinateLine i (joinCoordinate i (y, t)) s =
      joinCoordinate i (y, s) := by
  ext j
  rcases i.eq_self_or_eq_succAbove j with (rfl | ⟨k, rfl⟩)
  · simp [coordinateLine]
  · simp [coordinateLine, i.succAbove_ne k]

/-- Differentiating a coordinate slice gives the corresponding partial
derivative in split coordinates. -/
theorem deriv_coordinateSlice
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) (y : ℝ^n) (t : ℝ) :
    deriv (coordinateSlice i f y) t =
      coordinateDerivativeInSplit i f (y, t) := by
  let x := joinCoordinate i (y, t)
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiable (by norm_num)).differentiableAt
  have hpartial := PDE.partialDeriv_eq_deriv_coordinateLine i x hdiff
  have hxi : x i = t := by simp [x]
  have hline : f ∘ coordinateLine i x = coordinateSlice i f y := by
    funext s
    simp [x, coordinateSlice, coordinateLine_joinCoordinate]
  rw [hxi, hline] at hpartial
  exact hpartial.symm

/-- A coordinate slice of a `C^m` function is `C^m`. -/
theorem coordinateSlice_contDiff {m : WithTop ℕ∞}
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ m f) (y : ℝ^n) :
    ContDiff ℝ m (coordinateSlice i f y) := by
  apply hf.comp
  rw [show (fun t ↦ joinCoordinate i (y, t)) =
      fun t ↦
        joinCoordinate i (y, 0) + coordinateAxisContinuousLinearMap i t by
    funext t
    exact joinCoordinate_eq_base_add_axis i y t]
  exact contDiff_const.add (coordinateAxisContinuousLinearMap i).contDiff

/-- A coordinate slice of a compactly supported function has compact
support. -/
theorem coordinateSlice_hasCompactSupport
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hfc : HasCompactSupport f) (y : ℝ^n) :
    HasCompactSupport (coordinateSlice i f y) := by
  let K : Set ℝ := (fun x : ℝ^(n + 1) ↦ x i) '' tsupport f
  have hK : IsCompact K := hfc.image (EuclideanSpace.proj i).continuous
  apply HasCompactSupport.intro hK
  intro t ht
  by_contra hne
  apply ht
  refine ⟨joinCoordinate i (y, t), subset_tsupport _ hne, ?_⟩
  simp

/-- The split-coordinate representation of a continuous function is
continuous on the product space. -/
theorem coordinateSlice_product_continuous
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : Continuous f) :
    Continuous (fun p : ℝ^n × ℝ ↦ coordinateSlice i f p.1 p.2) := by
  change Continuous (f ∘ (coordinateContinuousLinearEquiv i).symm)
  exact hf.comp (coordinateContinuousLinearEquiv i).symm.continuous

/-- The split-coordinate representation preserves compact support. -/
theorem coordinateSlice_product_hasCompactSupport
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport
      (fun p : ℝ^n × ℝ ↦ coordinateSlice i f p.1 p.2) := by
  change HasCompactSupport (f ∘ (coordinateContinuousLinearEquiv i).symm)
  exact hfc.comp_homeomorph
    (coordinateContinuousLinearEquiv i).symm.toHomeomorph

/-- The selected partial derivative of a `C¹` function is continuous in
split coordinates. -/
theorem coordinateDerivativeInSplit_continuous
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) :
    Continuous (coordinateDerivativeInSplit i f) := by
  have hd : Continuous (fun x ↦ (∂[i] f) x) := by
    have hfd : Continuous (fderiv ℝ f) :=
      hf.continuous_fderiv (by norm_num)
    simpa [partialDeriv] using
      hfd.clm_apply
        (continuous_const :
          Continuous
            (fun _ : ℝ^(n + 1) ↦
              EuclideanSpace.single i (1 : ℝ)))
  change Continuous
    ((fun x ↦ (∂[i] f) x) ∘
      (coordinateContinuousLinearEquiv i).symm)
  exact hd.comp (coordinateContinuousLinearEquiv i).symm.continuous

/-- The selected partial derivative of a compactly supported `C¹` function
has compact support in split coordinates. -/
theorem coordinateDerivativeInSplit_hasCompactSupport
    (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (coordinateDerivativeInSplit i f) := by
  have hd :
      HasCompactSupport
        (fun x ↦ (∂[i] f) x) := by
    simpa [partialDeriv] using
      hfc.fderiv_apply (𝕜 := ℝ)
        (v := EuclideanSpace.single i (1 : ℝ))
  change HasCompactSupport
    ((fun x ↦ (∂[i] f) x) ∘
      (coordinateContinuousLinearEquiv i).symm)
  exact hd.comp_homeomorph
    (coordinateContinuousLinearEquiv i).symm.toHomeomorph

end SobolevSpace.Slices
