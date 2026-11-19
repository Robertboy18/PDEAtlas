/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Energy

/-!
# Canonical Evans backward estimate

The representative-independent form of Evans's backward energy estimate used
by the short-interval uniqueness argument. The estimate is (40) in step 1 of the proof of
Evans, §7.2.2, Theorem 4, for the backward primitive `v(t) = ∫_t^σ u`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, step 1, equation (40).
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
Evans's backward estimate for a fixed canonical displacement evolution.

The preceding theorem constructs an evolution together with the estimate.
Canonical-representative uniqueness shows that the endpoint norm is
independent of that construction, so the same inequality holds for any
`ContinuousPivotEvolutionOn` representing the displacement.  This
nonexistential form is the one used by the Grönwall and interval-restart
arguments.
-/
theorem evans_backward_estimate [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b)
    (hBsplit : ∀ t ∈ Set.uIcc a σ, ∀ x y : V, B t x y = A t x y + R t x y)
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
  obtain ⟨E', _hinitial, hestimate⟩ :=
    h.exists_continuousDisplacementEvolution_with_evans_backward_estimate
      hab hσ hBsplit hAAC hAderiv hAsymm hAdotIntegrable hAIntegrable hRIntegrable
      c LA LR hLR hcoercive hAdotBound hRBound
  have hrepresentative : E'.representative σ = E.representative σ :=
    (E'.representative_eqOn E hab) hσ
  simpa only [hrepresentative] using hestimate

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
