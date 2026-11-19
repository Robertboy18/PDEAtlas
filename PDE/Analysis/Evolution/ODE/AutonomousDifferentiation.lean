/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity -- shake: keep
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Differentiating autonomous affine Carathéodory systems

For an autonomous system in a real Banach space

`u'(t) = A u(t) + f(t)`,

an absolutely continuous forcing with weak derivative `fDot` makes

`v(t) = A u(t) + f(t)`

an absolutely continuous solution of

`v'(t) = A v(t) + fDot(t)`.

This is the differentiation step in the proof of Evans §7.1.3, Theorem 5 (step 4,
equation (50)).
The trajectory is only a Carathéodory solution, with no `C²` hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, proof of Theorem 5, step 4, equation (50).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace AffineCaratheodorySolutionOn

/-- The velocity `t ↦ A u(t) + f(t)` of an autonomous affine trajectory. -/
def autonomousVelocity
    {a b : ℝ} {A : E →L[ℝ] E} {f : ℝ → E} {x₀ : E}
    (U : AffineCaratheodorySolutionOn (fun _ ↦ A) f a b x₀) :
    ℝ → E :=
  fun t ↦ A (U.trajectory t) + f t

/--
Differentiate an autonomous affine Carathéodory solution.

The returned trajectory is the right-hand side `A u + f`, hence it
agrees almost everywhere with `u'`.  Its initial value is the compatibility
value `A x₀ + f(a)`, and its forcing is the supplied weak derivative
`fDot`.
-/
def autonomousVelocitySolution
    {a b : ℝ} {A : E →L[ℝ] E} {f fDot : ℝ → E} {x₀ : E}
    (U : AffineCaratheodorySolutionOn (fun _ ↦ A) f a b x₀)
    (hfAC : AbsolutelyContinuousOnInterval f a b)
    (hfDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt f (fDot t) t) :
    AffineCaratheodorySolutionOn
      (fun _ ↦ A) fDot a b (A x₀ + f a) := by
  let v : ℝ → E := U.autonomousVelocity
  have hAtrajectoryAC :
      AbsolutelyContinuousOnInterval (fun t ↦ A (U.trajectory t)) a b := by
    have hcomp :=
      A.lipschitzWith.comp_absolutelyContinuousOnInterval U.absolutely_continuous
    simpa only [Function.comp_def] using hcomp
  have hvAC : AbsolutelyContinuousOnInterval v a b := by
    change
      AbsolutelyContinuousOnInterval
        ((fun t ↦ A (U.trajectory t)) + f) a b
    exact hAtrajectoryAC.add hfAC
  have hvInitial : v a = A x₀ + f a := by
    simp [v, autonomousVelocity, U.initial_value]
  have hvEquation :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt v (A (v t) + fDot t) t := by
    filter_upwards [U.equation_ae, hfDeriv] with t hu hf
    have hAu :
        HasDerivAt (fun s ↦ A (U.trajectory s))
          (A (A (U.trajectory t) + f t)) t :=
      A.hasFDerivAt.comp_hasDerivAt t hu
    have hadd := hAu.add hf
    change
      HasDerivAt ((fun s ↦ A (U.trajectory s)) + f)
        (A (A (U.trajectory t) + f t) + fDot t) t
    exact hadd
  exact
    { trajectory := v
      initial_value := hvInitial
      absolutely_continuous := hvAC
      equation_ae := hvEquation }

omit [CompleteSpace E] in
/--
The differentiated trajectory agrees almost everywhere with the derivative
of the original trajectory.
-/
theorem hasDerivAt_trajectory_autonomousVelocity
    {a b : ℝ} {A : E →L[ℝ] E} {f : ℝ → E} {x₀ : E}
    (U : AffineCaratheodorySolutionOn (fun _ ↦ A) f a b x₀) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt U.trajectory (U.autonomousVelocity t) t := by
  simpa only [autonomousVelocity] using U.equation_ae

end AffineCaratheodorySolutionOn

end PDE.Analysis.Evolution
