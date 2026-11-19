/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Diagonal.CenterProjection

/-!
# The two center coordinates of an augmented profile equation

At a simple characteristic speed, the augmented linear equation has two zero
rates: the speed parameter and the selected state coordinate. This description
uses an injective eigenvalue list and remains valid when there are no fast
coordinates.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Evolution

variable {ι : Type*}

/-- The diagonal rates of the profile equation at a selected characteristic
speed. The extra rate is zero because the speed parameter is constant. -/
def augmentedProfileRate (eig : ι → ℝ) (k : ι) : Option ι → ℝ
  | none => 0
  | some i => eig i - eig k

/-- Embed state amplitude and speed displacement into the two center
coordinates of the augmented equation. -/
def profileCenterCoordinates (k : ι) : (ℝ × ℝ) →L[ℝ] (Option ι → ℝ) := by
  classical
  exact ContinuousLinearMap.pi fun i ↦ match i with
    | none => ContinuousLinearMap.snd ℝ ℝ ℝ
    | some j => if j = k then ContinuousLinearMap.fst ℝ ℝ ℝ else 0

/-- The extra center coordinate is the speed displacement. -/
@[simp] theorem profileCenterCoordinates_none (k : ι) (z : ℝ × ℝ) :
    profileCenterCoordinates k z none = z.2 := rfl

/-- The selected state coordinate is the amplitude. -/
@[simp] theorem profileCenterCoordinates_self (k : ι) (z : ℝ × ℝ) :
    profileCenterCoordinates k z (some k) = z.1 := by
  simp [profileCenterCoordinates]

/-- All other state coordinates vanish in the center parameter. -/
theorem profileCenterCoordinates_of_ne (k : ι) (z : ℝ × ℝ) {i : ι} (hi : i ≠ k) :
    profileCenterCoordinates k z (some i) = 0 := by
  simp [profileCenterCoordinates, hi]

/-- Both parameter directions lie in the kernel of the augmented diagonal operator, for arbitrary
fast rates. -/
theorem rate_mul_profileCenterCoordinates (eig : ι → ℝ) (k : ι) (z : ℝ × ℝ) (i : Option ι) :
    augmentedProfileRate eig k i * profileCenterCoordinates k z i = 0 := by
  classical
  cases i with
  | none => simp [augmentedProfileRate]
  | some i =>
    by_cases hi : i = k
    · subst i
      simp [augmentedProfileRate]
    · rw [profileCenterCoordinates_of_ne k z hi, mul_zero]

/-- For a simple eigenvalue list, projection onto the center space is exactly
reconstruction from the amplitude and speed coordinates. -/
theorem diagonalCenterProjection_augmentedProfileRate
    (eig : ι → ℝ) (heig : Function.Injective eig) (k : ι) (x : Option ι → ℝ) :
    diagonalCenterProjection (augmentedProfileRate eig k) x =
      profileCenterCoordinates k (x (some k), x none) := by
  classical
  ext i
  cases i with
  | none => simp [diagonalCenterProjection_apply, augmentedProfileRate]
  | some i =>
    by_cases hi : i = k
    · subst i
      simp [diagonalCenterProjection_apply, augmentedProfileRate]
    · have hrate : eig i - eig k ≠ 0 := sub_ne_zero.mpr (fun h ↦ hi (heig h))
      simp [diagonalCenterProjection_apply, augmentedProfileRate, hrate,
        profileCenterCoordinates_of_ne k _ hi]

end PDE.Hyperbolic.ConservationLaw.System
