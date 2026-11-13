/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients
public import PDE.Hyperbolic.Variational.SecondOrder.Basic
import PDE.Hyperbolic.Variational.SecondOrder.WellPosedness

/-!
# Second-order Gelfand Galerkin systems

We specialize second-order Carathéodory systems to the pivot-mass
Galerkin operator of a Gelfand triple.  We prove finite-dimensional existence
for measurable spatial forms and the projected weak wave equation
satisfied by the acceleration.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 1 and equations (13)-(18).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Existence of the finite-dimensional pivot-mass Galerkin approximation for
the weak wave equation.

This is the coordinate-free counterpart of Evans's coefficient equations
in §7.2.2.  The ambient form is bounded and strongly measurable in time.
The dual forcing is merely Bochner integrable; Evans's
`f ∈ L²(0,T;L²(U))`, embedded into `V*` through the pivot space, is a
special case on a finite interval.
-/
theorem GelfandGalerkin.exists (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V) {a b : ℝ}
    (hab : a ≤ b) (hB : AEStronglyMeasurable B (volume.restrict (Set.Icc a b)))
    (hell : IntegrableOn ell (Set.Icc a b) volume) (MB : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB) (q₀ p₀ : S) :
    Nonempty (SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  let K : ℝ → S →L[ℝ] S := fun t ↦ gelfandGalerkinOperator T S (B t)
  let fS : ℝ → S := gelfandGalerkinForcing T S ell
  let MK := gelfandGalerkinLipschitzBound T S MB
  have hK :
      AEStronglyMeasurable K (volume.restrict (Set.Icc a b)) := by
    simpa only [K, gelfandGalerkinOperatorMap_apply] using
      (gelfandGalerkinOperatorMap T S).continuous.comp_aestronglyMeasurable hB
  have hfS :
      IntegrableOn fS (Set.Icc a b) volume := by
    have h := (gelfandGalerkinForcingMap T S).integrable_comp hell
    apply h.congr
    filter_upwards with t
    rfl
  have hK_bound : ∀ t ∈ Set.Icc a b, ‖K t‖ ≤ MK := by
    intro t ht
    change ‖gelfandGalerkinOperator T S (B t)‖ ≤ MK
    rw [← norm_neg (gelfandGalerkinOperator T S (B t))]
    exact norm_neg_gelfandGalerkinOperator_le T S (B t) MB (hB_bound t ht)
  exact SecondOrderSolutionOn.exists hab K fS hK hfS MK hK_bound q₀ p₀

/--
The acceleration in a Gelfand Galerkin solution satisfies Evans's projected
weak wave equation almost everywhere:

`(uₘ''(t),v)_H + B(t)(uₘ(t),v) = ell(t)(v)` for every `v ∈ S`.

The theorem records the derivative and the projected identity together, so
the vector appearing as `uₘ''` cannot be disconnected from the weak
equation.
-/
theorem GelfandGalerkin.projectedEquationAE (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] [CompleteSpace S] (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt U.velocity
        (-(gelfandGalerkinOperator T S (B t)) (U.displacement t) +
          gelfandGalerkinForcing T S ell t) t ∧
      ∀ v : S,
        inner ℝ
            (T.inclusion
              ((-(gelfandGalerkinOperator T S (B t))
                  (U.displacement t) +
                gelfandGalerkinForcing T S ell t : S) : V))
            (T.inclusion (v : V)) +
          B t (U.displacement t : V) (v : V) =
            ell t (v : V) := by
  filter_upwards [U.velocityEquationAE] with t ht
  constructor
  · exact ht
  · have hfield : -(gelfandGalerkinOperator T S (B t)) (U.displacement t) +
            gelfandGalerkinForcing T S ell t =
          gelfandGalerkinVectorField T S B ell t (U.displacement t) :=
      neg_gelfandGalerkinOperator_add_forcing T S B ell t (U.displacement t)
    rw [hfield]
    exact gelfandGalerkinVectorField_equation T S B ell t (U.displacement t)

end Hyperbolic.Variational
