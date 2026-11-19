/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative

/-!
# Backward integration by parts for weak waves

The uniqueness proof for weak solutions of second-order hyperbolic equations in Evans,
§7.2.2 tests the homogeneous equation against the backward primitive

`v(t) = ∫ₜ^σ u(r) dr`  (`backwardTimePrimitive u σ t`),

which vanishes at the terminal time `σ` and has derivative `-u`. Pairing the acceleration with
`v` and integrating in time then produces the boundary terms `⟪u'(y), v(y)⟫ - ⟪u'(x), v(x)⟫` and
the interior term `-∫ ⟪u', u⟫`. We prove that integration-by-parts formula for a weak
wave, with the velocity represented by its continuous Riesz representative `z` in `V`:

`⟪z(y), v(y)⟫ - ⟪z(x), v(x)⟫ = ∫ₓʸ [acceleration(r)(v(r)) - ⟪z(r), u(r)⟫] dr`

for all `x, y ∈ [a, b]`, including the endpoints.

## Main results

* `backwardPrimitive_integrationByParts`: the formula for a fixed continuous Riesz velocity
  evolution `Evelocity`, valid simultaneously for every `σ ∈ [a, b]` and every pair of
  endpoints `x, y ∈ [a, b]`. Keeping the evolution fixed matters for the short-interval
  restart argument, which advances the left endpoint without choosing new representatives.
* `exists_continuousRieszVelocity_with_backward_integrationByParts`: the endpoint-inclusive
  form for a weak wave, with `z(a)` equal to the Riesz representative of `J* p₀`. In the
  uniqueness theorem `p₀ = 0`, so the boundary term at `a` vanishes.

## Implementation notes

Both `v` and `z` are canonical Bochner primitives with strong almost-everywhere derivatives, so
the product rule is applied to differentiable functions; no pointwise value of an
arbitrary `Lp` representative is differentiated.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4.
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
Backward-primitive integration by parts for a fixed canonical velocity
evolution.

This is the analytic core of Evans's uniqueness test. Once the
continuous Riesz representative of the velocity has been constructed, the
formula holds simultaneously for every terminal time `σ` and every pair of
endpoints `x,y ∈ [a,b]`.  Keeping the evolution fixed is important for the
short-interval restart argument: no new representative is chosen when the
left endpoint advances.
-/
theorem backwardPrimitive_integrationByParts [CompleteSpace V]
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    (hab : a < b) (huAB : IntervalIntegrable (fun r ↦ u r) volume a b) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) :
    ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      inner ℝ (Evelocity.representative y) (backwardTimePrimitive (fun r ↦ u r) σ y) -
          inner ℝ (Evelocity.representative x) (backwardTimePrimitive (fun r ↦ u r) σ x) =
        ∫ r in x..y, acceleration r (backwardTimePrimitive (fun q ↦ u q) σ r) -
          inner ℝ (Evelocity.representative r) (u r) := by
  intro x y hx hy
  have hxySubset : uIcc x y ⊆ uIcc a b := uIcc_subset_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
  let c : ℝ → StrongDual ℝ V :=
    fun t ↦ (GelfandTriple.identity V).pivotToDual (Evelocity.representative t)
  let v : ℝ → V := backwardTimePrimitive (fun r ↦ u r) σ
  have hcFTC : ∀ t ∈ uIcc x y, c t = c x + ∫ r in x..t, acceleration r := fun t ht ↦ by
    simpa only [c, dualPrimitive] using (Evelocity.integratedDerivative.subinterval
      (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)).eq_add_integral t ht
  have hvFTC : ∀ t ∈ uIcc x y, v t = v x + ∫ r in x..t, -u r := fun t ht ↦ by
    dsimp only [v, backwardTimePrimitive]
    rw [intervalIntegral.integral_neg]
    simpa only [sub_eq_add_neg] using (intervalIntegral.integral_interval_sub_left
      (huAB.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hσ)))
      (huAB.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hx) (hxySubset ht)))).symm
  have hvDerivRestrict := ae_hasDerivAt_backwardTimePrimitive huAB (Icc_subset_uIcc hσ)
  rw [uIoc_of_le hab.le] at hvDerivRestrict
  have hlift {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume.restrict (Ioc a b), P t) :
      ∀ᵐ t ∂volume, t ∈ uIcc x y → P t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hP,
      (by simp [ae_iff, measure_singleton] : ∀ᵐ t ∂volume, t ≠ a)] with t ht hta htXY
    have htAB : t ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hxySubset htXY
    exact ht ⟨lt_of_le_of_ne htAB.1 (Ne.symm hta), htAB.2⟩
  simpa only [c, v, GelfandTriple.pivotToDual_apply, GelfandTriple.identity_inclusion_apply,
    Pi.neg_apply, inner_neg_right, sub_eq_add_neg] using integrated_duality_product_rule
      ((intervalIntegrable_coeFn_L2_restrict_Ioc acceleration hab.le).mono_set hxySubset)
      (huAB.mono_set hxySubset).neg hcFTC hvFTC
      (hlift (Evelocity.integratedDerivative.ae_hasDerivAt_pivotToDual hab)) (hlift hvDerivRestrict)

/--
Evans's endpoint-inclusive backward-primitive integration-by-parts formula
for a weak wave.

Fix `σ ∈ [a,b]` and put `v(t) = ∫ₜ^σ u(r) dr`.  The continuous Riesz
representative `z` of the weak velocity satisfies, for every
`x,y ∈ [a,b]`,

`⟪z(y),v(y)⟫ - ⟪z(x),v(x)⟫
  = ∫ₓʸ [uₜₜ(r)(v(r)) - ⟪u(r),z(r)⟫] dr`.

The formula reaches the initial endpoint. The proof of Evans, §7.2.2, Theorem 4
needs exactly this, since there the zero initial velocity annihilates the
boundary term at `a`. The proof uses the strong
almost-everywhere derivative of both canonical Bochner primitives; no
pointwise value of an arbitrary `Lp` representative is differentiated.
-/
theorem exists_continuousRieszVelocity_with_backward_integrationByParts [MeasurableSpace V]
    [BorelSpace V] [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace V] (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀)
    (hab : a < b) {σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    ∃ Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
        (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b,
      Evelocity.representative a = (InnerProductSpace.toDual ℝ V).symm (T.pivotToDual p₀) ∧
        ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
          inner ℝ (Evelocity.representative y) (backwardTimePrimitive (fun r ↦ u r) σ y) -
              inner ℝ (Evelocity.representative x) (backwardTimePrimitive (fun r ↦ u r) σ x) =
            ∫ r in x..y, acceleration r (backwardTimePrimitive (fun q ↦ u q) σ r) -
              inner ℝ (Evelocity.representative r) (u r) := by
  obtain ⟨Evelocity, -, hinitial⟩ := h.exists_continuousRieszVelocityEvolution
  exact ⟨Evelocity, hinitial, backwardPrimitive_integrationByParts Evelocity hab
    (intervalIntegrable_coeFn_L2_restrict_Ioc u hab.le) hσ⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
