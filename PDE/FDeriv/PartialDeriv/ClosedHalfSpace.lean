/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# Coordinate derivatives determined on a closed half-space

A closed coordinate half-space `{x | 0 ≤ x j}` has unique derivatives at all of its points, so two
functions that agree on it and are differentiable at one of its points have the same coordinate
derivatives there, and two `C²` functions that agree on it have the same second coordinate
derivatives there.

## Main results

* `partialDeriv_eq_of_eqOn_halfSpace`: functions equal on the half-space and differentiable at a
  point of it have the same coordinate derivatives there.
* `partialDeriv_partialDeriv_eq_of_eqOn_halfSpace`: `C²` functions equal on the half-space have
  the same second coordinate derivatives at its points.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

variable {n : ℕ} {f g : ℝ^n → ℝ}

namespace PDE

/-- Coordinate derivatives at a point of a closed half-space of functions differentiable there
and equal on the half-space agree. -/
theorem partialDeriv_eq_of_eqOn_halfSpace (i j : Fin n) {a : ℝ^n} (ha : 0 ≤ a j)
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a)
    (heq : ∀ y : ℝ^n, 0 ≤ y j → f y = g y) : (∂[i] f) a = (∂[i] g) a := by
  have h : fderiv ℝ f a = fderiv ℝ g a :=
    (PDE.Analysis.uniqueDiffOn_coordinateHalfSpace j a ha).eq hf.hasFDerivAt.hasFDerivWithinAt
      (hg.hasFDerivAt.hasFDerivWithinAt.congr (fun y hy ↦ heq y hy) (heq a ha))
  simp only [PDE.partialDeriv, h]

/-- Second coordinate derivatives at a point of a closed half-space of `C²` functions equal on
the half-space agree. -/
theorem partialDeriv_partialDeriv_eq_of_eqOn_halfSpace (i k j : Fin n) {a : ℝ^n} (ha : 0 ≤ a j)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (heq : ∀ y : ℝ^n, 0 ≤ y j → f y = g y) :
    (∂[i] (fun x ↦ (∂[k] f) x)) a = (∂[i] (fun x ↦ (∂[k] g) x)) a := by
  have hf1 : ContDiff ℝ 1 (∂[k] f) := contDiff_partialDeriv_of_succ (m := 1) hf
  have hg1 : ContDiff ℝ 1 (∂[k] g) := contDiff_partialDeriv_of_succ (m := 1) hg
  exact partialDeriv_eq_of_eqOn_halfSpace i j ha (hf1.differentiable (by norm_num) a)
    (hg1.differentiable (by norm_num) a) fun y hy ↦
      partialDeriv_eq_of_eqOn_halfSpace k j hy (hf.differentiable (by norm_num) y)
        (hg.differentiable (by norm_num) y) heq

end PDE
