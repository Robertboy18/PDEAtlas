/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.SecondOrder.AutonomousDifferentiation
public import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients

/-!
# Differentiating autonomous Gelfand Galerkin systems

An absolutely continuous dual forcing may be differentiated through an
autonomous pivot-mass Galerkin equation.  The differentiated trajectory has
the velocity as its displacement and the mass-inverted initial residual as
its initial velocity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, step 2, equation (53).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Differentiate an autonomous pivot-mass Galerkin system.

For the projected equation

`(uₘ'',v)_H + B(uₘ,v) = ell(v)`,

the coefficient velocity solves the Galerkin system with forcing `ellDot`
and initial acceleration

`-Kₘ q₀ + Fₘ ell(a)`.

Here `Kₘ` and `Fₘ` are exactly the mass-inverted stiffness and forcing maps,
so this initial value is the trial-space representation of
`ell(a) - B q₀`.  This is Evans's equation (53) and its initial datum, in
basis-free form.
-/
noncomputable def GelfandGalerkin.timeDerivative
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {ell ellDot : ℝ → StrongDual ℝ V}
    {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn
      (fun _ ↦ gelfandGalerkinOperator T S B)
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hellAC : AbsolutelyContinuousOnInterval ell a b)
    (hellDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt ell (ellDot t) t) :
    SecondOrderSolutionOn
      (fun _ ↦ gelfandGalerkinOperator T S B)
      (gelfandGalerkinForcing T S ellDot) a b p₀
        (-(gelfandGalerkinOperator T S B) q₀ +
          gelfandGalerkinForcing T S ell a) := by
  let F : StrongDual ℝ V →L[ℝ] S :=
    gelfandGalerkinForcingMap T S
  have hforcingAC :
      AbsolutelyContinuousOnInterval
        (gelfandGalerkinForcing T S ell) a b := by
    have hcomp :=
      F.lipschitzWith.comp_absolutelyContinuousOnInterval hellAC
    simpa only [F, Function.comp_def, gelfandGalerkinForcing,
      gelfandGalerkinForcingMap_apply] using! hcomp
  have hforcingDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt (gelfandGalerkinForcing T S ell)
          (gelfandGalerkinForcing T S ellDot t) t := by
    filter_upwards [hellDeriv] with t ht
    have hcomp := F.hasFDerivAt.comp_hasDerivAt t ht
    simpa only [F, gelfandGalerkinForcing,
      gelfandGalerkinForcingMap_apply, Function.comp_def] using! hcomp
  exact SecondOrderSolutionOn.timeDerivative U hforcingAC hforcingDeriv

end Hyperbolic.Variational
