/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.BackwardEstimate
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.BackwardVanishing

/-!
# Restarted short-interval weak-wave uniqueness

The local step of the uniqueness proof for weak solutions of second-order hyperbolic equations
(Evans, §7.2.2): a zero-data weak wave of the homogeneous equation `u'' + B(t) u = 0`
vanishes on a sufficiently short interval. The coefficient hypotheses are those of the backward
estimate, `B = A + R` with `A` symmetric, absolutely continuous in time and coercive with
constant `κ`, `|Adot(t)(x, x)| ≤ L_A ‖x‖²`, and `|R(t)(x, y)| ≤ L_R ‖J x‖_H ‖y‖_V`. The interval
`[d, e]` is short when

`(2 (L_A + L_R) / κ) (e - d) < 1`,

which is exactly the condition under which the endpoint term can be absorbed in
`continuousDisplacement_eq_zero_of_backward_estimate`. Evans's argument imposes this smallness
and then restarts; the restart is carried out in `FinitePartition`.

## Main results

* `continuousDisplacement_eq_zero_of_short_subinterval`: the restart step. The weak wave and
  its continuous displacement and Riesz velocity evolutions live on the original `[a, b]`; if
  both traces vanish at `d` and the coefficient bounds hold on `[d, e]`, the continuous
  displacement vanishes on `[d, e]` together with `∫_d^t u`.
* `exists_continuousDisplacementEvolution_eq_zero_of_short_interval`: the initial-interval
  corollary, constructing the continuous displacement evolution from the weak solution and
  concluding that it vanishes on all of `[a, b]` when `[a, b]` itself is short.

## Implementation notes

The interval-integrability families for `Adot(v, v)`, `A(u, v)` and `R(u, v)` are stated for
every terminal time `σ` because the backward primitive depends on `σ`. They are consequences of
the coefficient bounds in any concrete realization; the weak solution structure stores only the
equation and the trajectories.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, steps 2 and 3.
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
Restarted short-interval uniqueness with Evans's coefficient hypotheses.

The weak solution and its canonical displacement/velocity evolutions live on
the original interval `[a,b]`.  If both traces vanish at a later time `d`,
the coefficient assumptions on `[d,e]` imply that the displacement vanishes
throughout `[d,e]`.  This is the single restart step iterated in the global
uniqueness theorem.
-/
theorem continuousDisplacement_eq_zero_of_short_subinterval
    [CompleteSpace V] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (Edisplacement : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    {d e : ℝ} (hd : d ∈ Set.Icc a b) (he : e ∈ Set.Icc a b) (hde : d ≤ e)
    (hdisplacementD : Edisplacement.representative d = 0)
    (hvelocityD : Evelocity.representative d = 0)
    (hBsplit : ∀ t ∈ Set.Icc d e, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A d e)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc d e), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.Icc d e, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc d e → IntervalIntegrable (fun t ↦
      Adot t (backwardTimePrimitive (fun r ↦ u r) σ t) (backwardTimePrimitive (fun r ↦ u r) σ t))
        volume d σ)
    (hAIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc d e → IntervalIntegrable
      (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume d σ)
    (hRIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc d e → IntervalIntegrable
      (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume d σ)
    (κ LA LR : ℝ) (hκ : 0 < κ) (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.Icc d e, ∀ x : V, κ * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.Icc d e, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.Icc d e, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖)
    (hshort : (2 * (LA + LR) / κ) * (e - d) < 1) :
    ∀ t ∈ Set.Icc d e, Edisplacement.representative t = 0 ∧ (∫ r in d..t, u r) = 0 := by
  refine continuousDisplacement_eq_zero_of_backward_estimate hab Edisplacement hd he hde κ LA LR
    hκ hLA hLR (fun σ hσ ↦ ?_) hshort
  have hsub : uIcc d σ ⊆ uIcc d e := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hσ)
  have hmem (t : ℝ) (ht : t ∈ uIcc d σ) : t ∈ Icc d e := by
    simpa only [uIcc_of_le hde] using hsub ht
  exact h.evans_backward_estimate_on_subinterval hab Edisplacement Evelocity (d := d) (σ := σ) hd
    ⟨hd.1.trans hσ.1, hσ.2.trans he.2⟩ hσ.1 hdisplacementD hvelocityD
    (fun t ht ↦ hBsplit t (hmem t ht)) (hAAC.mono hsub)
    (ae_restrict_of_ae_restrict_of_subset (by
      rw [uIoc_of_le hσ.1]
      exact Ioc_subset_Ioc_right hσ.2) hAderiv)
    (fun t ht ↦ hAsymm t (hmem t ht)) (hAdotIntegrable hσ) (hAIntegrable hσ)
    (hRIntegrable hσ) κ LA LR hLR (fun t ht ↦ hcoercive t (hmem t ht))
    (fun t ht ↦ hAdotBound t (hmem t ht)) (fun t ht ↦ hRBound t (hmem t ht))

/--
Short-interval uniqueness for homogeneous weak solutions in the sense of Evans, §7.2.1.

This theorem assembles the complete local argument from §7.2.2:

1. use the backward test to obtain estimate (40);
2. write the backward primitive as `w(σ)-w(t)`;
3. form the continuous energy
   `e(t)=‖u_H(t)‖²+c‖w(t)‖²`;
4. absorb the endpoint term when the interval is short; and
5. apply integral Grönwall.

The three scalar-integrability families are the direct consequences of the
usual uniform coefficient bounds.  They are hypotheses because the weak
solution structure stores only the equation and trajectories.
-/
theorem exists_continuousDisplacementEvolution_eq_zero_of_short_interval [MeasurableSpace V]
    [BorelSpace V] [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace V] [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
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
    (c LA LR : ℝ) (hc : 0 < c) (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.Icc a b, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖)
    (hshort : (2 * (LA + LR) / c) * (b - a) < 1) :
    ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦
      T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b, E.representative a =
      0 ∧ ∀ t ∈ Set.Icc a b, E.representative t = 0 ∧ (∫ r in a..t, u r) = 0 := by
  obtain ⟨Edisplacement, hdisplacementInitial⟩ := h.exists_continuousDisplacementEvolution
  obtain ⟨Evelocity, -, hvelocityInitial⟩ := h.exists_continuousRieszVelocityEvolution
  have hdisplacementZero : Edisplacement.representative a = 0 := by
    simpa using hdisplacementInitial
  exact ⟨Edisplacement, hdisplacementZero, h.continuousDisplacement_eq_zero_of_short_subinterval
    hab Edisplacement Evelocity (d := a) (e := b) ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
    hdisplacementZero (by rw [hvelocityInitial]; simp) hBsplit hAAC hAderiv hAsymm
    hAdotIntegrable hAIntegrable hRIntegrable c LA LR hc hLA hLR hcoercive hAdotBound hRBound
    hshort⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
