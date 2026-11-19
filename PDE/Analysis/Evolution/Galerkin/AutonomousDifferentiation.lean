/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients
public import PDE.Analysis.Evolution.Galerkin.Measurable.Approximation
public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
import PDE.Analysis.Evolution.Galerkin.Gelfand.Existence

/-!
# Differentiating autonomous Galerkin approximations

Evans proves Theorem 5(ii) of §7.1.3 by differentiating the finite-dimensional Galerkin
equation in time before passing to weak limits.

For a time-independent form `B`, an almost-everywhere Galerkin approximation on a trial space
`S` is an affine Carathéodory solution of `u' = -M_S⁻¹ A_S u + M_S⁻¹ r_S(ℓ(t))`, where `M_S`
is the pivot mass operator. If the load `ℓ` is absolutely continuous on `[a, b]` with
derivative `ℓ'` almost everywhere, then the projected load `t ↦ M_S⁻¹ r_S(ℓ(t))` is
absolutely continuous with derivative `M_S⁻¹ r_S(ℓ'(t))` almost everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, proof of Theorem 5, step 4, equations (50)
  and (51). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace AEGelfandGalerkinApproximation

variable
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V}
    {B : V →L[ℝ] StrongDual ℝ V}
    {ell ellDot : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}

/-- An autonomous Galerkin approximation is an affine Carathéodory solution
after inversion of the finite-dimensional pivot mass matrix. -/
def toAutonomousCaratheodory
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (G : AEGelfandGalerkinApproximation T S (fun _ ↦ B) ell
      a b C M u₀) :
    AffineCaratheodorySolutionOn
      (fun _ ↦ -(gelfandGalerkinOperator T S B))
      (fun t ↦ (gelfandGalerkinForcingMap T S) (ell t)) a b u₀ where
  trajectory := G.trajectory
  initial_value := G.initial
  absolutely_continuous := G.trajectory_ac
  equation_ae := by
    filter_upwards [G.derivative_ae, G.equation_ae] with t hderiv heq
    have hvelocity :
        G.coefficientDerivative t =
          gelfandGalerkinVectorField T S (fun _ ↦ B) ell t
            (G.trajectory t) :=
      gelfandGalerkin_derivative_eq_vectorField
        T S (fun _ ↦ B) ell t (G.trajectory t)
          (G.coefficientDerivative t) heq
    apply hderiv.congr_deriv
    rw [hvelocity]
    exact
      (neg_gelfandGalerkinOperator_add_forcing
        T S (fun _ ↦ B) ell t (G.trajectory t)).symm

omit [CompleteSpace V] [CompleteSpace H] in
/-- If `ℓ` is absolutely continuous on `[a, b]`, so is the projected load
`t ↦ M_S⁻¹ r_S(ℓ(t))`. -/
theorem absolutelyContinuousOnInterval_gelfandGalerkinForcing
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (hellAC : AbsolutelyContinuousOnInterval ell a b) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ (gelfandGalerkinForcingMap T S) (ell t)) a b := by
  have hcomp :=
    (gelfandGalerkinForcingMap T S).lipschitzWith.comp_absolutelyContinuousOnInterval hellAC
  simpa only [Function.comp_def] using hcomp

omit [CompleteSpace V] [CompleteSpace H] in
/-- If `ℓ' = ℓDot` almost everywhere on `(a, b]`, then the projected load has derivative
`M_S⁻¹ r_S(ℓDot(t))` almost everywhere. -/
theorem hasDerivAt_gelfandGalerkinForcing_ae
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (hellDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt ell (ellDot t) t) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt
        (fun s ↦ (gelfandGalerkinForcingMap T S) (ell s))
        ((gelfandGalerkinForcingMap T S) (ellDot t)) t := by
  filter_upwards [hellDeriv] with t ht
  have hcomp :=
    (gelfandGalerkinForcingMap T S).hasFDerivAt.comp_hasDerivAt t ht
  simpa only [Function.comp_def] using hcomp

end AEGelfandGalerkinApproximation

end PDE.Analysis.Evolution
