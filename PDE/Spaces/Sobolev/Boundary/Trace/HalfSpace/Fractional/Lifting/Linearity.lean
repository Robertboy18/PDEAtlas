/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Formula

/-!
# Linearity and representative independence

The mollified extension depends only on the almost-everywhere class of its
boundary data. It is linear on locally integrable functions. These identities
let the same formula descend to Sobolev classes once its norm bound is proved.
-/

@[expose] public section

open MeasureTheory
open scoped Convolution

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Changing the boundary data on a null set leaves the extension unchanged everywhere. -/
theorem mollifiedExtension_congr_ae (μ : Mollifier n) {f g : ℝ^n → F}
    (hfg : f =ᵐ[volume] g) :
    mollifiedExtension μ f = mollifiedExtension μ g := by
  funext z
  unfold mollifiedExtension mollifyVector
  rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hfg]

/-- Zero boundary data give the zero extension. -/
@[simp]
theorem mollifiedExtension_zero (μ : Mollifier n) :
    mollifiedExtension μ (0 : ℝ^n → F) = 0 := by
  funext z
  simp [mollifiedExtension, mollifyVector]

/-- The mollified extension is additive on locally integrable boundary data. -/
theorem mollifiedExtension_add (μ : Mollifier n) {f g : ℝ^n → F}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    mollifiedExtension μ (f + g) = mollifiedExtension μ f + mollifiedExtension μ g := by
  funext z
  by_cases ht : 0 < (splitTangentialNormal z).2
  · simp only [mollifiedExtension, mollifyVector_add_of_pos μ ht f g hf hg, Pi.add_apply,
      smul_add]
  · have hs : scaled μ (splitTangentialNormal z).2 = 0 := by
      unfold scaled
      rw [ite_eq_left (le_of_not_gt ht)]
    simp only [mollifiedExtension, mollifyVector, hs, zero_convolution, Pi.zero_apply,
      smul_zero, Pi.add_apply, add_zero]

/-- Scalar multiplication commutes with the extension, without an integrability assumption. -/
theorem mollifiedExtension_smul (μ : Mollifier n) (c : ℝ) (g : ℝ^n → F) :
    mollifiedExtension μ (c • g) = c • mollifiedExtension μ g := by
  funext z
  simp only [mollifiedExtension, mollifyVector, convolution_smul, Pi.smul_apply]
  exact smul_comm _ _ _

end SobolevSpace.Trace.HalfSpace
