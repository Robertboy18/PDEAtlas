/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.BackwardEstimate

/-!
# Weak-wave energy theorems

Existential forms of the backward energy identity and estimate of `BackwardEstimate`
on the initial interval `[a, σ]`. Starting from a zero-data weak wave of the homogeneous
equation `u'' + B(t) u = 0` with `B = A + R`, each theorem constructs the continuous `H`-valued
displacement evolution `E` with `E.representative a = 0` and returns, for the backward primitive
`v(t) = ∫ₜ^σ u(r) dr`, either the exact balance

`½ ‖E(σ)‖² + ½ A(a)(v(a), v(a)) + ½ ∫ₐ^σ Adot(t)(v, v) dt + ∫ₐ^σ R(t)(u, v) dt = 0`

or, under coercivity of `A` and bounds on `Adot` and `R`, the coercive estimate with the
squared norms of `v` and `J u` on the right. These are the abstract forms of the identity and
estimate in the uniqueness proof of Evans, §7.2.2.

## Main results

* `exists_continuousDisplacementEvolution_with_evans_backward_energy`: the exact identity,
  for forms of either sign; the scalar integrability hypotheses are what the
  nonautonomous quadratic-form chain rule needs.
* `exists_continuousDisplacementEvolution_with_evans_backward_estimate`: the estimate under
  `c ‖x‖² ≤ A(t)(x, x)`, `|Adot(t)(x, x)| ≤ L_A ‖x‖²` and `|R(t)(x, y)| ≤ L_R ‖J x‖_H ‖y‖_V`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, equations (39)-(40).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}
/--
Evans's exact backward energy identity after separating the principal and
lower-order parts of the wave operator.

Suppose `B(t) = A(t) + R(t)`, where `A(t)` is symmetric and absolutely
continuous in time with derivative `Adot(t)`.  For the backward primitive

`v(t) = ∫ₜ^σ u(r) dr`,

the homogeneous weak-wave identity becomes

`1/2 ‖u_H(σ)‖²
  + 1/2 A(a)(v(a),v(a))
  + 1/2 ∫ₐ^σ Adot(t)(v(t),v(t)) dt
  + ∫ₐ^σ R(t)(u(t),v(t)) dt = 0`.

This is the exact identity underlying Evans, 2nd ed., §7.2.2, equations
(39)-(40). Coercivity of `A` and bounds on `Adot` and `R` enter only the subsequent estimate. The
scalar integrability hypotheses are the consequences needed from those coefficient bounds; stating
them keeps this theorem independent of any one set of coefficient hypotheses.
-/
theorem exists_continuousDisplacementEvolution_with_evans_backward_energy [MeasurableSpace V]
    [BorelSpace V] [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace V] [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) (hBsplit : ∀ t ∈ Set.uIcc a σ, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A a σ)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc a σ), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.uIcc a σ, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : IntervalIntegrable (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hAIntegrable :
      IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hRIntegrable :
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ) :
    ∃ E : ContinuousPivotEvolutionOn T
        (fun t ↦ u t)
        (fun t ↦
          T.pivotToDual.compLpL 2
            (volume.restrict (Set.Ioc a b)) velocity t)
        a b,
      E.representative a = 0 ∧
        (1 / 2 : ℝ) * ‖E.representative σ‖ ^ 2 +
            (1 / 2 : ℝ) *
              A a
                (backwardTimePrimitive (fun r ↦ u r) σ a)
                (backwardTimePrimitive (fun r ↦ u r) σ a) +
            (1 / 2 : ℝ) *
              (∫ t in a..σ,
                Adot t
                  (backwardTimePrimitive (fun r ↦ u r) σ t)
                  (backwardTimePrimitive (fun r ↦ u r) σ t)) +
            (∫ t in a..σ,
              R t (u t)
                (backwardTimePrimitive (fun r ↦ u r) σ t)) =
          0 := by
  obtain ⟨Edisplacement, hdisplacementInitial⟩ := h.exists_continuousDisplacementEvolution
  obtain ⟨Evelocity, _hvelocityWeak, hvelocityInitial⟩ := h.exists_continuousRieszVelocityEvolution
  have hdisplacementZero :
      Edisplacement.representative a = 0 := by
    simpa using hdisplacementInitial
  have hvelocityZero :
      Evelocity.representative a = 0 := by
    rw [hvelocityInitial]
    simp
  refine ⟨Edisplacement, hdisplacementZero, ?_⟩
  exact h.evans_backward_energy_on_subinterval hab Edisplacement Evelocity
    (c := a) (σ := σ) ⟨le_rfl, hab.le⟩ hσ hσ.1
    hdisplacementZero hvelocityZero hBsplit hAAC hAderiv hAsymm
    hAdotIntegrable hAIntegrable hRIntegrable

/--
Abstract form of Evans's backward estimate (40).

The estimate uses three coefficient bounds:

* `A` is coercive in the energy-space norm;
* the time variation `Adot` is bounded quadratically on `V`;
* the lower-order form is bounded in `H × V`.

The last choice is essential: the weak-wave regularity controls `u(t)` in
the pivot space at the endpoint and in `L²(a,σ;H)`, while the backward
primitive is controlled in `V`.  Young's inequality converts the mixed
lower-order work into the two squared norms displayed below.
-/
theorem exists_continuousDisplacementEvolution_with_evans_backward_estimate [MeasurableSpace V]
    [BorelSpace V] [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace V] [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) (hBsplit : ∀ t ∈ Set.uIcc a σ, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A a σ)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc a σ), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.uIcc a σ, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : IntervalIntegrable (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hAIntegrable :
      IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hRIntegrable :
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (c LA LR : ℝ) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.uIcc a σ, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.uIcc a σ, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.uIcc a σ, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖) :
    ∃ E : ContinuousPivotEvolutionOn T
        (fun t ↦ u t)
        (fun t ↦
          T.pivotToDual.compLpL 2
            (volume.restrict (Set.Ioc a b)) velocity t)
        a b,
      E.representative a = 0 ∧
        (1 / 2 : ℝ) * ‖E.representative σ‖ ^ 2 +
            (1 / 2 : ℝ) * c *
              ‖backwardTimePrimitive (fun r ↦ u r) σ a‖ ^ 2 ≤
          (1 / 2 : ℝ) * LA *
              (∫ t in a..σ,
                ‖backwardTimePrimitive (fun r ↦ u r) σ t‖ ^ 2) +
            (1 / 2 : ℝ) * LR *
              ((∫ t in a..σ, ‖T.inclusion (u t)‖ ^ 2) +
                (∫ t in a..σ,
                  ‖backwardTimePrimitive (fun r ↦ u r) σ t‖ ^ 2)) := by
  obtain ⟨Edisplacement, hdisplacementInitial⟩ := h.exists_continuousDisplacementEvolution
  obtain ⟨Evelocity, _hvelocityWeak, hvelocityInitial⟩ := h.exists_continuousRieszVelocityEvolution
  have hdisplacementZero :
      Edisplacement.representative a = 0 := by
    simpa using hdisplacementInitial
  have hvelocityZero :
      Evelocity.representative a = 0 := by
    rw [hvelocityInitial]
    simp
  refine ⟨Edisplacement, hdisplacementZero, ?_⟩
  exact h.evans_backward_estimate_on_subinterval hab Edisplacement Evelocity
    (d := a) (σ := σ) ⟨le_rfl, hab.le⟩ hσ hσ.1
    hdisplacementZero hvelocityZero hBsplit hAAC hAderiv hAsymm
    hAdotIntegrable hAIntegrable hRIntegrable c LA LR hLR hcoercive hAdotBound hRBound

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
