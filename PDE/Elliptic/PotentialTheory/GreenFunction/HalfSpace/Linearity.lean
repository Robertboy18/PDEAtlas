/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential

/-!
# Linearity of the half-space Green integral

The Green integral is additive on sources with integrable kernels at every
evaluation point, and it commutes with negation of the source. The integrability
hypotheses prevent invalid use of linearity for Mathlib's total integral outside its
integrable domain.

## Main results

* `HasIntegrableHalfSpaceGreenPotential.add`, `HasIntegrableHalfSpaceGreenPotential.sub`: sources
  with integrable Green kernels are closed under addition and subtraction.
* `halfSpaceGreenPotential_add`, `halfSpaceGreenPotential_sub`: on such sources the Green potential
  is additive and subtractive at every evaluation point.
* `halfSpaceGreenPotential_neg`: the potential of `-f` is minus the potential of `f`, with no
  integrability hypothesis.
-/

@[expose] public noncomputable section

namespace GreenFunction

open MeasureTheory

variable {n : ℕ} [Fact (0 < n)] {f g : ℝ^n → ℝ}

/-- The domain of the pointwise Green integral is closed under source addition. -/
theorem HasIntegrableHalfSpaceGreenPotential.add
    (hf : HasIntegrableHalfSpaceGreenPotential f) (hg : HasIntegrableHalfSpaceGreenPotential g) :
    HasIntegrableHalfSpaceGreenPotential (fun y ↦ f y + g y) := by
  intro x
  simpa only [mul_add] using (hf x).fun_add (hg x)

/-- The domain of the pointwise Green integral is closed under source subtraction. -/
theorem HasIntegrableHalfSpaceGreenPotential.sub
    (hf : HasIntegrableHalfSpaceGreenPotential f) (hg : HasIntegrableHalfSpaceGreenPotential g) :
    HasIntegrableHalfSpaceGreenPotential (fun y ↦ f y - g y) := by
  intro x
  simpa only [mul_sub] using (hf x).fun_sub (hg x)

/-- Integrable Green potentials preserve source addition at every evaluation point. -/
theorem halfSpaceGreenPotential_add
    (hf : HasIntegrableHalfSpaceGreenPotential f) (hg : HasIntegrableHalfSpaceGreenPotential g)
    (x : ℝ^n) :
    halfSpaceGreenPotential (fun y ↦ f y + g y) x =
      halfSpaceGreenPotential f x + halfSpaceGreenPotential g x := by
  simp only [halfSpaceGreenPotential, mul_add]
  exact integral_add (hf x) (hg x)

/-- Integrable Green potentials preserve source subtraction at every evaluation point. -/
theorem halfSpaceGreenPotential_sub
    (hf : HasIntegrableHalfSpaceGreenPotential f) (hg : HasIntegrableHalfSpaceGreenPotential g)
    (x : ℝ^n) :
    halfSpaceGreenPotential (fun y ↦ f y - g y) x =
      halfSpaceGreenPotential f x - halfSpaceGreenPotential g x := by
  simp only [halfSpaceGreenPotential, mul_sub]
  exact integral_sub (hf x) (hg x)

/-- The Green potential of `-f` is the negative of the Green potential of `f`, without any
integrability hypothesis. -/
theorem halfSpaceGreenPotential_neg (f : ℝ^n → ℝ) (x : ℝ^n) :
    halfSpaceGreenPotential (fun y ↦ -f y) x = -halfSpaceGreenPotential f x := by
  simp only [halfSpaceGreenPotential, mul_neg, integral_neg]

end GreenFunction
