/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.Homogeneous

/-!
# Weak-wave uniqueness by subtraction

Uniqueness of weak solutions of the abstract second-order hyperbolic equation
`u'' + B(t) u = ell`, `u(a) = q₀`, `u'(a) = p₀` on a Gelfand triple `V ↪ H ↪ V*`: two weak waves
with the same operator, forcing and initial data have the same displacement, velocity and
acceleration classes. This is the uniqueness theorem for weak solutions of second-order
hyperbolic equations in Evans, §7.2.2. The argument is linear: the difference of two
solutions is a zero-data weak wave of the homogeneous equation, and `Homogeneous` shows such a
wave vanishes.

## Main results

* `sub_same_data`: the difference of two weak waves with the same data is a weak wave for the
  homogeneous equation with zero forcing and zero initial traces.
* `eq_of_evans_coefficients`: the uniqueness theorem under Evans's coefficient hypotheses
  (`B = A + R`, `A` symmetric, absolutely continuous and coercive, `Adot` bounded quadratically,
  `R` bounded on `H × V`).
* `eq_of_homogeneous_eq_zero`: the reduction in isolation. If every zero-data homogeneous weak
  wave vanishes, any two weak waves with equal data coincide.

## Implementation notes

All three trajectories are Bochner equivalence classes, so subtraction is justified through
`Lp.coeFn_sub` and the scalar integrals in the separated-test identities are split only after
their integrability has been established. The interval-integrability hypotheses of
`eq_of_evans_coefficients` refer to the difference `u₁ - u₂` and its backward primitives, since
those are the objects the energy identity is applied to.

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

/-- A tested integral of a difference of `L²` classes splits into the two tested integrals,
for an integrand `F t` that is additive in the class value. -/
private theorem integral_sub_of_ae {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ}
    {x x₁ x₂ : ℝ → E} (hx : x =ᵐ[μ] x₁ - x₂) (F : ℝ → E → ℝ)
    (hF : ∀ t y z, F t (y - z) = F t y - F t z) (h₁ : Integrable (fun t ↦ F t (x₁ t)) μ)
    (h₂ : Integrable (fun t ↦ F t (x₂ t)) μ) :
    ∫ t, F t (x t) ∂μ = (∫ t, F t (x₁ t) ∂μ) - ∫ t, F t (x₂ t) ∂μ := by
  rw [← integral_sub h₁ h₂]
  exact integral_congr_ae (hx.mono fun t ht ↦ by simp only [ht, Pi.sub_apply, hF])

/--
Difference reduction for weak solutions in the sense of Evans, §7.2.1.

If two weak waves have the same operator, forcing, and initial data, their
difference is a weak wave for the homogeneous equation with zero displacement
and velocity traces.  This is the first step of Evans, §7.2.2, Theorem 4.

All three trajectories are Bochner equivalence classes rather than pointwise
functions, so each subtraction is justified through `Lp.coeFn_sub`, and the
scalar integrals are split only after proving their integrability.
-/
theorem sub_same_data {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {velocity₁ velocity₂ : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration₁ acceleration₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : IsGelfandWeakWaveSolution T B ell u₁ velocity₁ acceleration₁ q₀ p₀)
    (h₂ : IsGelfandWeakWaveSolution T B ell u₂ velocity₂ acceleration₂ q₀ p₀) :
    IsGelfandWeakWaveSolution
      T B 0 (u₁ - u₂) (velocity₁ - velocity₂) (acceleration₁ - acceleration₂) 0 0 := by
  have hpivot (w : V) (τ : TimeTest a b) (v : Lp H 2 (volume.restrict (Set.Ioc a b))) :
      Integrable (fun t ↦ T.pivotToDual (v t) w * τ.toLp t) (volume.restrict (Set.Ioc a b)) := by
    simpa only [GelfandTriple.pivotToDual_apply] using integrable_pivotVelocityTimeTest T w τ.toLp v
  refine ⟨h₁.interval_nonempty, ⟨h₁.interval_nonempty, by simp, fun w τ ↦ hpivot w τ _,
    fun w τ ↦ ?_⟩, fun w τ ↦ ?_, ?_⟩
  · have hd₁ := h₁.displacementIdentity.equation w τ
    have hd₂ := h₂.displacementIdentity.equation w τ
    simp only [zero_apply, zero_mul, integral_zero, map_zero, inner_zero_left] at hd₁ hd₂ ⊢
    rw [integral_sub_of_ae (Lp.coeFn_sub u₁ u₂)
        (fun t y ↦ inner ℝ (T.inclusion y) (T.inclusion w) * τ.derivToLp t)
        (fun _ _ _ ↦ by rw [map_sub, inner_sub_left, sub_mul])
        (integrable_gelfandPivotTimeTest T w τ.derivToLp u₁)
        (integrable_gelfandPivotTimeTest T w τ.derivToLp u₂),
      integral_sub_of_ae (Lp.coeFn_sub velocity₁ velocity₂) (fun t y ↦ T.pivotToDual y w * τ.toLp t)
        (fun _ _ _ ↦ by rw [map_sub, sub_apply, sub_mul]) (hpivot w τ _) (hpivot w τ _)]
    linarith
  · simp only [inner_zero_left, zero_mul]
    rw [integral_sub_of_ae (Lp.coeFn_sub velocity₁ velocity₂)
        (fun t y ↦ inner ℝ y (T.inclusion w) * τ.derivToLp t)
        (fun _ _ _ ↦ by rw [inner_sub_left, sub_mul])
        (integrable_pivotVelocityTimeTest T w τ.derivToLp velocity₁)
        (integrable_pivotVelocityTimeTest T w τ.derivToLp velocity₂),
      integral_sub_of_ae (Lp.coeFn_sub acceleration₁ acceleration₂) (fun t y ↦ y w * τ.toLp t)
        (fun _ _ _ ↦ by rw [sub_apply, sub_mul]) (integrable_dualTimeTest w τ.toLp acceleration₁)
        (integrable_dualTimeTest w τ.toLp acceleration₂)]
    linarith [h₁.velocityIdentity w τ, h₂.velocityIdentity w τ]
  · filter_upwards [h₁.equationAE, h₂.equationAE, Lp.coeFn_sub u₁ u₂,
      Lp.coeFn_sub acceleration₁ acceleration₂, Lp.coeFn_zero (StrongDual ℝ V) 2 _] with
        t heq₁ heq₂ hu ha hzero
    rw [hu, ha, hzero, Pi.sub_apply, Pi.sub_apply, Pi.zero_apply, map_sub,
      show acceleration₁ t - acceleration₂ t + (B t (u₁ t) - B t (u₂ t)) =
        (acceleration₁ t + B t (u₁ t)) - (acceleration₂ t + B t (u₂ t)) by abel, heq₁, heq₂,
      sub_self]

/--
Evans, §7.2.2, Theorem 4: uniqueness of the weak wave.

Two weak waves with the same operator, forcing, and initial traces coincide
in all three energy-class trajectories.  The proof subtracts the solutions,
constructs the continuous displacement and velocity representatives for the
homogeneous difference, derives the backward-energy estimate from the
coefficient hypotheses, constructs a finite short-time partition, restarts
the estimate across the full interval, and finally identifies the three
Bochner equivalence classes.

Unlike `eq_of_homogeneous_eq_zero`, this theorem proves homogeneous
uniqueness rather than assuming it.  The interval-integrability clauses state
that the three scalar coefficient pairings for the difference are
well-defined; the quadratic-form chain rule in Evans's energy identity needs
them.
-/
theorem eq_of_evans_coefficients [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {velocity₁ velocity₂ : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration₁ acceleration₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : IsGelfandWeakWaveSolution T B ell u₁ velocity₁ acceleration₁ q₀ p₀)
    (h₂ : IsGelfandWeakWaveSolution T B ell u₂ velocity₂ acceleration₂ q₀ p₀)
    (hBsplit : ∀ t ∈ Set.Icc a b, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.Icc a b, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable
      (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t)
      (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t)) volume a σ)
    (hAIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable
      (fun t ↦ A t ((u₁ - u₂) t) (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t)) volume a σ)
    (hRIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable
      (fun t ↦ R t ((u₁ - u₂) t) (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t)) volume a σ)
    (κ LA LR : ℝ) (hκ : 0 < κ) (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ x : V, κ * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.Icc a b, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖) :
    u₁ = u₂ ∧ velocity₁ = velocity₂ ∧ acceleration₁ = acceleration₂ := by
  obtain ⟨hu, hvelocity, hacceleration⟩ :=
    (h₁.sub_same_data h₂).homogeneous_eq_zero_of_evans_coefficients h₁.interval_nonempty hBsplit
      hAAC hAderiv hAsymm hAdotIntegrable hAIntegrable hRIntegrable κ LA LR hκ hLA hLR hcoercive
      hAdotBound hRBound
  exact ⟨sub_eq_zero.mp hu, sub_eq_zero.mp hvelocity, sub_eq_zero.mp hacceleration⟩

/--
Evans's reduction of uniqueness to the homogeneous zero-data problem.

Once every weak solution with zero forcing and zero initial traces is known to
vanish, subtraction identifies the displacement, velocity, and acceleration
of any two solutions with the same data.  The analytic content of Theorem 4
is therefore isolated in `hhomogeneous`; this theorem performs the exact
linearity argument and no regularity shortcut.
-/
theorem eq_of_homogeneous_eq_zero
    (hhomogeneous : ∀ (w : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (z : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
        IsGelfandWeakWaveSolution T B 0 w z g 0 0 → w = 0 ∧ z = 0 ∧ g = 0)
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {velocity₁ velocity₂ : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration₁ acceleration₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : IsGelfandWeakWaveSolution T B ell u₁ velocity₁ acceleration₁ q₀ p₀)
    (h₂ : IsGelfandWeakWaveSolution T B ell u₂ velocity₂ acceleration₂ q₀ p₀) :
    u₁ = u₂ ∧ velocity₁ = velocity₂ ∧ acceleration₁ = acceleration₂ := by
  obtain ⟨hu, hvelocity, hacceleration⟩ := hhomogeneous _ _ _ (h₁.sub_same_data h₂)
  exact ⟨sub_eq_zero.mp hu, sub_eq_zero.mp hvelocity, sub_eq_zero.mp hacceleration⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
