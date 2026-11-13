/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Tangential-normal coordinates for a flat boundary

The proof of the trace inequality on the half-space writes a point of `ℝ^(n+1)` as `(x', xₙ₊₁)` with
`x' ∈ ℝ^n` tangential and `xₙ₊₁` normal, integrates the fundamental theorem of calculus in the
normal variable, and then integrates over `x'` (Evans, PDE, §5.5). We set up that coordinate split.
The maps `splitTangentialNormal : ℝ^(n+1) → ℝ^n × ℝ` and its inverse `joinTangentialNormal` form a
continuous linear equivalence and a measurable equivalence, and the latter carries Euclidean volume
on `ℝ^(n+1)` to the product of Euclidean volume on `ℝ^n` with Lebesgue measure on `ℝ`, which is what
makes Fubini available.

Under these coordinates the upper half-space is the preimage of `Set.Ioi 0` under the normal
component, so an integral over `ℝ^(n+1)₊` becomes an integral over `ℝ^n × (0, ∞)`.

## Main results

* `splitTangentialNormal`, `joinTangentialNormal`: the coordinate split and its inverse, with
  `split_joinTangentialNormal` and `join_splitTangentialNormal`.
* `tangentialNormalContinuousLinearEquiv`, `tangentialNormalMeasurableEquiv`: the split as a
  continuous linear equivalence and as a measurable equivalence.
* `measurePreserving_tangentialNormalMeasurableEquiv`: the split sends `volume` on `ℝ^(n+1)` to
  `volume.prod volume` on `ℝ^n × ℝ`.
* `upper_eq_preimage_split_snd_Ioi`: the upper half-space in these coordinates.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, step 1 of the proof, (1), p. 272, the flat
  trace estimate obtained by integrating in `x_n` and then in `x'`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.HalfSpace

open MeasureTheory Set

variable {n : ℕ}

/-- Split a point into its first `n` coordinates and its final coordinate. -/
def splitTangentialNormal (x : ℝ^(n + 1)) : ℝ^n × ℝ :=
  (WithLp.toLp 2 (fun i : Fin n ↦ x i.castSucc), x (Fin.last n))

/-- Assemble tangential coordinates and a final normal coordinate. -/
def joinTangentialNormal (p : ℝ^n × ℝ) : ℝ^(n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i ↦ p.1 i))

/-- Splitting a point recovers each tangential coordinate. -/
@[simp]
theorem splitTangentialNormal_fst_apply (x : ℝ^(n + 1)) (i : Fin n) :
    (splitTangentialNormal x).1 i = x i.castSucc := by
  simp [splitTangentialNormal]

/-- Splitting a point recovers its final, normal coordinate. -/
@[simp]
theorem splitTangentialNormal_snd (x : ℝ^(n + 1)) :
    (splitTangentialNormal x).2 = x (Fin.last n) :=
  rfl

/-- Joining tangential and normal data preserves each tangential coordinate. -/
@[simp]
theorem joinTangentialNormal_castSucc (p : ℝ^n × ℝ) (i : Fin n) :
    joinTangentialNormal p i.castSucc = p.1 i := by
  simp [joinTangentialNormal]

/-- Joining tangential and normal data places the scalar in the final coordinate. -/
@[simp]
theorem joinTangentialNormal_last (p : ℝ^n × ℝ) :
    joinTangentialNormal p (Fin.last n) = p.2 := by
  simp [joinTangentialNormal]

/-- Splitting after joining tangential and normal coordinates is the identity. -/
@[simp]
theorem split_joinTangentialNormal (p : ℝ^n × ℝ) :
    splitTangentialNormal (joinTangentialNormal p) = p := by
  ext i <;> simp

/-- Joining after splitting Euclidean coordinates is the identity. -/
@[simp]
theorem join_splitTangentialNormal (x : ℝ^(n + 1)) :
    joinTangentialNormal (splitTangentialNormal x) = x := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

/-- Continuous linear equivalence corresponding to the coordinate split. -/
noncomputable def tangentialNormalContinuousLinearEquiv :
    ℝ^(n + 1) ≃L[ℝ] ℝ^n × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := splitTangentialNormal
      invFun := joinTangentialNormal
      left_inv := join_splitTangentialNormal
      right_inv := split_joinTangentialNormal
      map_add' := by
        intro x y
        apply Prod.ext
        · ext i
          simp [splitTangentialNormal]
        · simp [splitTangentialNormal]
      map_smul' := by
        intro c x
        apply Prod.ext
        · ext i
          simp [splitTangentialNormal]
        · simp [splitTangentialNormal] }

/-- The continuous linear coordinate decomposition acts as `splitTangentialNormal`. -/
@[simp]
theorem tangentialNormalContinuousLinearEquiv_apply (x : ℝ^(n + 1)) :
    tangentialNormalContinuousLinearEquiv x = splitTangentialNormal x :=
  rfl

/-- The inverse continuous linear decomposition acts as `joinTangentialNormal`. -/
@[simp]
theorem tangentialNormalContinuousLinearEquiv_symm_apply (p : ℝ^n × ℝ) :
    tangentialNormalContinuousLinearEquiv.symm p = joinTangentialNormal p :=
  rfl

/-- Continuous linear parametrization of the final coordinate axis. -/
noncomputable def normalAxisContinuousLinearMap : ℝ →L[ℝ] ℝ^(n + 1) :=
  tangentialNormalContinuousLinearEquiv.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (ℝ^n) ℝ)

/-- A joined point is its zero-normal base point plus its displacement along the normal axis. -/
theorem joinTangentialNormal_eq_base_add_normal (y : ℝ^n) (t : ℝ) :
    joinTangentialNormal (y, t) =
      joinTangentialNormal (y, 0) + normalAxisContinuousLinearMap (n := n) t := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
    simp [normalAxisContinuousLinearMap]

/-- Measurable equivalence corresponding to the tangential-normal coordinate split. -/
noncomputable def tangentialNormalMeasurableEquiv :
    ℝ^(n + 1) ≃ᵐ ℝ^n × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm |>.trans
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)) |>.trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ))) |>.trans
    MeasurableEquiv.prodComm

/-- The measurable coordinate decomposition acts as `splitTangentialNormal`. -/
@[simp]
theorem tangentialNormalMeasurableEquiv_apply (x : ℝ^(n + 1)) :
    tangentialNormalMeasurableEquiv x = splitTangentialNormal x := by
  apply Prod.ext
  · ext i
    simp [tangentialNormalMeasurableEquiv, splitTangentialNormal,
      MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  · simp [tangentialNormalMeasurableEquiv, splitTangentialNormal,
      MeasurableEquiv.piFinSuccAbove_apply]
    rfl

/-- The inverse measurable coordinate decomposition acts as `joinTangentialNormal`. -/
@[simp]
theorem tangentialNormalMeasurableEquiv_symm_apply (p : ℝ^n × ℝ) :
    tangentialNormalMeasurableEquiv.symm p = joinTangentialNormal p :=
  (tangentialNormalMeasurableEquiv (n := n)).injective
    (by simp [tangentialNormalMeasurableEquiv_apply])

/-- Tangential-normal coordinates send Euclidean volume to product volume. -/
theorem measurePreserving_tangentialNormalMeasurableEquiv :
    MeasurePreserving (tangentialNormalMeasurableEquiv (n := n)) := by
  let eRaw : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
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
        (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n))
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
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ^n)))).congr
    · exact MeasurableEquiv.prodComm.measurable
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  rw [Measure.volume_eq_prod (ℝ^n) ℝ]
  exact ((h₁.trans h₂).trans h₃).trans h₄

/-- Tangential-normal coordinates identify the open upper half-space with
`ℝ^n × (0, ∞)`. -/
theorem upper_eq_preimage_split_snd_Ioi :
    @HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩ =
      splitTangentialNormal ⁻¹' (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
  have : Fact (0 < n + 1) := ⟨Nat.zero_lt_succ n⟩
  have hlast : PDE.Common.lastIndex (n := n + 1) = Fin.last n := by
    apply Fin.ext
    simp [PDE.Common.lastIndex]
  ext x
  simp [HalfSpace.upper, hlast, splitTangentialNormal]

end Trace.HalfSpace
end SobolevSpace
