/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Even projection of a real function

Averaging `f(r)` with its reflection `f(-r)` gives an even function. Its
derivative is half the difference of the reflected derivatives, so it
vanishes at zero whenever `f` is differentiable there.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Calculus.RadialSymmetrization

/-- Exact averaging of a radial slice with its reflection. -/
def evenProjection (f : ℝ → ℝ) (r : ℝ) : ℝ := (f r + f (-r)) / 2

/-- The projected slice is invariant under radial reflection. -/
theorem evenProjection_neg (f : ℝ → ℝ) (r : ℝ) :
    evenProjection f (-r) = evenProjection f r := by
  simp only [evenProjection, neg_neg, add_comm]

/-- Radial differentiation takes the difference of the reflected first derivatives. -/
theorem hasDerivAt_evenProjection
    {f : ℝ → ℝ} {r forwardDerivative reflectedDerivative : ℝ}
    (hforward : HasDerivAt f forwardDerivative r)
    (hreflected : HasDerivAt f reflectedDerivative (-r)) :
    HasDerivAt (evenProjection f) ((forwardDerivative - reflectedDerivative) / 2) r := by
  unfold evenProjection
  have hsum : HasDerivAt (fun y ↦ f y + f (-y))
      (forwardDerivative + reflectedDerivative * (-1)) r :=
    hforward.add (hreflected.comp r (hasDerivAt_neg r))
  apply (hsum.div_const 2).congr_deriv
  simp only [mul_neg_one, sub_eq_add_neg]

/-- If `f` is differentiable at the axis, the projected slice has derivative zero there. -/
theorem hasDerivAt_evenProjection_zero {f : ℝ → ℝ} {d : ℝ}
    (h : HasDerivAt f d 0) : HasDerivAt (evenProjection f) 0 0 := by
  have hneg : HasDerivAt f d (-0) := by simpa only [neg_zero] using h
  convert hasDerivAt_evenProjection h hneg using 1
  simp

end PDE.Analysis.Calculus.RadialSymmetrization
