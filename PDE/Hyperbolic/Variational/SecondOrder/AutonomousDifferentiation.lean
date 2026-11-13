/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.SecondOrder.Basic
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity -- shake: keep
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Differentiating autonomous second-order systems

For an autonomous stiffness operator, an absolutely continuous forcing lets
the velocity of a second-order solution be viewed as a solution of the
differentiated equation.  The proof combines the two almost-everywhere state
equations without differentiating an almost-everywhere identity formally.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, equation (16), and §7.2.3, proof of Theorem 5,
  step 2, equation (53).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set

namespace Hyperbolic.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/--
The velocity of an autonomous second-order solution solves the
differentiated second-order equation.

Let

`q''(t) + K q(t) = f(t)`,

where the bounded operator `K` is independent of time.  If `f` is absolutely
continuous with derivative `fdot`, then

`p := q'`

is a Carathéodory solution of

`p''(t) + K p(t) = fdot(t)`,

with initial data

`p(a) = p₀`, `p'(a) = f(a) - K q₀`.

This is the differentiation of the Galerkin identity (16) of Evans, §7.2.2, that gives (53)
in §7.2.3, in coordinate-free form.  The original velocity equation identifies
`p'`, absolute continuity of `f` proves that this derivative is itself
absolutely continuous, and the two available almost-everywhere derivative
statements are combined.
-/
noncomputable def SecondOrderSolutionOn.timeDerivative
    {K : E →L[ℝ] E} {f fdot : ℝ → E}
    {a b : ℝ} {q₀ p₀ : E}
    (U : SecondOrderSolutionOn (fun _ ↦ K) f a b q₀ p₀)
    (hfAC : AbsolutelyContinuousOnInterval f a b)
    (hfderiv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt f (fdot t) t) :
    SecondOrderSolutionOn
      (fun _ ↦ K) fdot a b p₀ (-(K q₀) + f a) := by
  let acceleration : ℝ → E :=
    fun t ↦ -(K (U.displacement t)) + f t
  have hKqAC :
      AbsolutelyContinuousOnInterval
        (fun t ↦ -(K (U.displacement t))) a b := by
    have hcomp :=
      (-K).lipschitzWith.comp_absolutelyContinuousOnInterval U.displacementAbsolutelyContinuous
    simpa only [Function.comp_def, neg_apply] using! hcomp
  have haccelerationAC :
      AbsolutelyContinuousOnInterval acceleration a b := by
    refine (hKqAC.add hfAC).congr fun t _ ↦ ?_
    rfl
  have haccelerationDerivative :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt acceleration (-(K (U.velocity t)) + fdot t) t := by
    filter_upwards [U.displacementEquationAE, hfderiv] with t hq hf
    have hKq :=
      (-K).hasFDerivAt.comp_hasDerivAt t hq
    simpa only [acceleration, Pi.add_apply, Function.comp_def,
      neg_apply] using! hKq.add hf
  exact {
    displacement := U.velocity
    velocity := acceleration
    initialDisplacement := U.initialVelocity
    initialVelocity := by
      dsimp only [acceleration]
      rw [U.initialDisplacement]
    displacementAbsolutelyContinuous := U.velocityAbsolutelyContinuous
    velocityAbsolutelyContinuous := haccelerationAC
    displacementEquationAE := by
      filter_upwards [U.velocityEquationAE] with t ht
      simpa only [acceleration] using ht
    velocityEquationAE := haccelerationDerivative
  }

end Hyperbolic.Variational
