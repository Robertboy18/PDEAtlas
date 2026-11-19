/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.FinitePartition

/-!
# Homogeneous weak-wave uniqueness

A weak wave of the homogeneous equation `u'' + B(t) u = 0` with zero initial displacement and
velocity is zero: `u = 0`, `velocity = 0` and `acceleration = 0` as Bochner classes. This is the
content of the uniqueness theorem for weak solutions of second-order hyperbolic equations in
Evans, §7.2.2, stated on a Gelfand triple `V ↪ H ↪ V*` under Evans's coefficient
hypotheses: `B = A + R` with `A` symmetric, absolutely continuous in time and coercive, its time
derivative bounded quadratically on `V`, and `R` bounded on `H × V`.

The proof combines the earlier results. The continuous displacement and Riesz velocity
evolutions are constructed from the weak solution; a uniform finite partition with short cells
is chosen; the backward energy estimate and Grönwall argument are run on each cell, restarting
from the zero traces at each partition point; and finally the vanishing of the continuous
displacement representative is upgraded to the three `Lp` equalities.

## Main results

* `homogeneous_eq_zero_of_continuousDisplacement_eq_zero`: if the continuous `H`-valued
  displacement representative vanishes on `[a, b]`, then `u = 0` (almost-everywhere
  identification and injectivity of `J`), `velocity = 0` (the integrated derivative is zero and
  `J*` is injective), and `acceleration = 0` (the homogeneous equation).
* `homogeneous_eq_zero_of_evans_coefficients`: the full homogeneous uniqueness theorem under
  the coefficient hypotheses.

## Implementation notes

The three interval-integrability families (for `Adot(v, v)`, `A(u, v)`, `R(u, v)` with `v` the
backward primitive) are integrability conditions for the quadratic-form chain rule; they follow
from the coefficient bounds and energy-class membership in concrete realizations
(`EvansCoefficientIntegrability`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 4.
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
Upgrade vanishing of the canonical displacement representative to vanishing
of all three Bochner trajectories of a homogeneous weak wave.

The displacement follows from almost-everywhere identification with the
continuous representative and injectivity of the Gelfand inclusion.  Its
integrated derivative is then zero almost everywhere, so injectivity of
`pivotToDual` gives zero velocity.  Finally the homogeneous wave equation
gives zero acceleration.
-/
theorem homogeneous_eq_zero_of_continuousDisplacement_eq_zero
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (hzero : ∀ t ∈ Set.Icc a b, E.representative t = 0) :
    u = 0 ∧ velocity = 0 ∧ acceleration = 0 := by
  let μab := volume.restrict (Set.Ioc a b)
  let velocityDual : Lp (StrongDual ℝ V) 2 μab := T.pivotToDual.compLpL 2 μab velocity
  have hIocSubsetUIcc : Set.Ioc a b ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    exact Set.Ioc_subset_Icc_self
  have hrepresentativeAE : E.representative =ᵐ[μab] fun t ↦ T.inclusion (u t) :=
    E.ae_eq_inclusion.filter_mono (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hIocSubsetUIcc))
  have huAE :
      (u : ℝ → V) =ᵐ[μab] (fun _ ↦ (0 : V)) := by
    filter_upwards [hrepresentativeAE, ae_restrict_mem measurableSet_Ioc] with t hrep ht
    apply T.injective
    have hrepZero : E.representative t = 0 := hzero t ⟨ht.1.le, ht.2⟩
    simpa only [map_zero] using hrep.symm.trans hrepZero
  have hu : u = 0 := by
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    exact huAE
  have hderivativeZeroIcc : (fun t ↦ velocityDual t) =ᵐ[volume.restrict (Set.Icc a b)]
        (fun _ ↦ (0 : StrongDual ℝ V)) := by
    simpa only [velocityDual, μab] using E.integratedDerivative_ae_eq_zero_of_representative_eq_zero
        hab Set.left_mem_uIcc Set.right_mem_uIcc hzero
  have hderivativeZero : (fun t ↦ velocityDual t) =ᵐ[μab]
        (fun _ ↦ (0 : StrongDual ℝ V)) := by
    have hconverted := (ae_restrict_congr_set Ioc_ae_eq_Icc).2 hderivativeZeroIcc
    filter_upwards [hconverted] with t ht using ht
  have hvelocityDualAE : (velocityDual : ℝ → StrongDual ℝ V) =ᵐ[μab]
        fun t ↦ T.pivotToDual (velocity t) := by
    simpa only [velocityDual, μab] using T.pivotToDual.coeFn_compLpL velocity
  have hvelocityAE :
      (velocity : ℝ → H) =ᵐ[μab] (fun _ ↦ (0 : H)) := by
    filter_upwards [hvelocityDualAE, hderivativeZero] with t hdual hzeroDual
    apply T.pivotToDual_injective
    rw [← hdual, hzeroDual, map_zero]
  have hvelocity : velocity = 0 := by
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    exact hvelocityAE
  have haccelerationAE : (acceleration : ℝ → StrongDual ℝ V) =ᵐ[μab]
        (fun _ ↦ (0 : StrongDual ℝ V)) := by
    filter_upwards [h.equationAE, huAE, Lp.coeFn_zero (StrongDual ℝ V) 2 μab]
      with t hequation huZero hzeroDual
    rw [huZero, map_zero, add_zero] at hequation
    exact hequation.trans hzeroDual
  have hacceleration : acceleration = 0 := by
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    exact haccelerationAE
  exact ⟨hu, hvelocity, hacceleration⟩

/--
Global homogeneous uniqueness under Evans's coefficient hypotheses.

This theorem is the assembly behind §7.2.2, Theorem 4.  It does not
assume that homogeneous solutions vanish.  Instead it:

1. constructs the canonical continuous displacement and Riesz-velocity
   evolutions from the weak solution;
2. chooses a sufficiently fine uniform finite time partition;
3. applies the backward-energy identity and estimate on each cell;
4. restarts from the zero endpoint traces; and
5. upgrades pointwise vanishing of the continuous displacement
   representative to equality of the displacement, velocity, and
   acceleration Bochner classes.

The three interval-integrability assumptions are the scalar products needed
by the nonautonomous quadratic-form chain rule. In concrete coefficient realizations they follow
from the stated coefficient regularity and the energy-class bounds.
-/
theorem homogeneous_eq_zero_of_evans_coefficients [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (hBsplit : ∀ t ∈ Set.Icc a b, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.Icc a b, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable
      (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hAIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b →
      IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hRIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b →
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (κ LA LR : ℝ) (hκ : 0 < κ) (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ x : V, κ * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.Icc a b, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖) :
    u = 0 ∧ velocity = 0 ∧ acceleration = 0 := by
  obtain ⟨Edisplacement, hdisplacementInitial⟩ := h.exists_continuousDisplacementEvolution
  obtain ⟨Evelocity, _hvelocityWeak, hvelocityInitial⟩ := h.exists_continuousRieszVelocityEvolution
  have hdisplacementZero :
      Edisplacement.representative a = 0 := by
    simpa using hdisplacementInitial
  have hvelocityZero :
      Evelocity.representative a = 0 := by
    rw [hvelocityInitial]
    simp
  let α : ℝ := 2 * (LA + LR) / κ
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg
      (mul_nonneg (by positivity) (add_nonneg hLA hLR)) hκ.le
  obtain ⟨N, τ, hτzero, hτN, hτmem, hτstep, hcover, hshort⟩ :=
    exists_uniform_finite_short_partition hab hα
  have hrepresentativeZero : ∀ t ∈ Set.Icc a b, Edisplacement.representative t = 0 :=
    h.continuousDisplacement_eq_zero_of_finite_short_partition
      hab Edisplacement Evelocity hdisplacementZero hvelocityZero N τ hτzero hτmem hτstep hcover
      hBsplit hAAC hAderiv hAsymm hAdotIntegrable hAIntegrable hRIntegrable κ LA LR hκ hLA hLR
      hcoercive hAdotBound hRBound
      (by
        intro n hn
        simpa only [α] using hshort n hn)
  exact h.homogeneous_eq_zero_of_continuousDisplacement_eq_zero
    hab Edisplacement hrepresentativeZero

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
