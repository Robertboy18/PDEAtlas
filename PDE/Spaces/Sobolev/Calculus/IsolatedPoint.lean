/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.ACLConverse
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Weak derivatives across an isolated point

In dimension at least two, almost every coordinate line avoids a given point.
A function `C¹` off that point therefore has `C¹` slices on almost every line.
Local integrability of the function and its classical partial derivative
then suffices for the global weak-derivative identity. No continuity at the
exceptional point is assumed.
-/

@[expose] public noncomputable section

namespace SobolevSpace

open MeasureTheory Set Slices
open scoped Topology

private theorem joinCoordinate_ne_of_ne {n : ℕ} (i : Fin (n + 1)) {z : ℝ^(n + 1)}
    {y : ℝ^n} (hy : y ≠ (splitCoordinate i z).1) (t : ℝ) : joinCoordinate i (y, t) ≠ z := by
  intro h
  apply hy
  simpa using congrArg (fun x ↦ (splitCoordinate i x).1) h

private theorem contDiff_joinCoordinate_line {n : ℕ} (i : Fin (n + 1)) (y : ℝ^n) :
    ContDiff ℝ 1 (fun t ↦ joinCoordinate i (y, t)) := by
  rw [show (fun t ↦ joinCoordinate i (y, t)) =
      (fun t ↦ joinCoordinate i (y, 0) + coordinateAxisContinuousLinearMap i t) from
    funext (joinCoordinate_eq_base_add_axis i y)]
  exact contDiff_const.add (coordinateAxisContinuousLinearMap i).contDiff

private theorem hasDerivAt_joinCoordinate_line {n : ℕ} (i : Fin (n + 1))
    (y : ℝ^n) (t : ℝ) :
    HasDerivAt (fun s ↦ joinCoordinate i (y, s)) (EuclideanSpace.single i (1 : ℝ)) t := by
  have haxis : coordinateAxisContinuousLinearMap i (1 : ℝ) =
      EuclideanSpace.single i (1 : ℝ) := by
    ext j
    rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩ <;>
      simp [coordinateAxisContinuousLinearMap]
  have hd := ((coordinateAxisContinuousLinearMap i).hasDerivAt (x := t)).const_add
    (joinCoordinate i (y, 0))
  simpa only [haxis, ← joinCoordinate_eq_base_add_axis] using hd

/-- A function `C¹` off one point has its classical partial derivative as a global weak
partial derivative when both are locally integrable, in dimension at least two. -/
theorem hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_point
    {n : ℕ} [NeZero n] {f : ℝ^(n + 1) → ℝ} (z : ℝ^(n + 1))
    (hf : ∀ x : ℝ^(n + 1), x ≠ z → ContDiffAt ℝ 1 f x)
    (hlocal : LocallyIntegrableOn f univ volume) (i : Fin (n + 1))
    (hpartial : LocallyIntegrableOn (PDE.partialDeriv i f) univ volume) :
    HasWeakDerivativeOn univ [i] f (PDE.partialDeriv i f) := by
  have hsmooth : ∀ y : ℝ^n, y ≠ (splitCoordinate i z).1 →
      ContDiff ℝ 1 (coordinateSlice i f y) := by
    intro y hy
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (hf _ (joinCoordinate_ne_of_ne i hy t)).comp t
      (contDiff_joinCoordinate_line i y).contDiffAt
  apply hasWeakDerivativeOn_of_locallyIntegrable_ae_coordinate_acl i hlocal hpartial
    (r := coordinateSlice i f)
  · exact Filter.Eventually.of_forall fun _ ↦ Filter.EventuallyEq.rfl
  · filter_upwards [volume.ae_ne (splitCoordinate i z).1] with y hy
    intro a b
    exact (hsmooth y hy).contDiffOn.absolutelyContinuousOnInterval
  · filter_upwards [volume.ae_ne (splitCoordinate i z).1] with y hy
    apply Filter.Eventually.of_forall
    intro t
    exact ((hf _ (joinCoordinate_ne_of_ne i hy t)).differentiableAt (by norm_num)).hasFDerivAt
      |>.comp_hasDerivAt t (hasDerivAt_joinCoordinate_line i y t)

/-- The case of a function `C¹` off the origin. -/
theorem hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_zero
    {n : ℕ} [NeZero n] {f : ℝ^(n + 1) → ℝ}
    (hf : ∀ x : ℝ^(n + 1), x ≠ 0 → ContDiffAt ℝ 1 f x)
    (hlocal : LocallyIntegrableOn f univ volume) (i : Fin (n + 1))
    (hpartial : LocallyIntegrableOn (PDE.partialDeriv i f) univ volume) :
    HasWeakDerivativeOn univ [i] f (PDE.partialDeriv i f) :=
  hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_point 0 hf hlocal i hpartial

end SobolevSpace
