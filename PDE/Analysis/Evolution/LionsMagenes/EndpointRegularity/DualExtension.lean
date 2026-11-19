/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.ReflectedExtension
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative

/-!
# Dual and energy endpoint extensions

Let `E` be a Lions–Magenes evolution on the open interval `(a, b)`
(`ContinuousPivotEvolutionOnOpen`): an `H`-continuous representative of a trajectory
`u ∈ L²(a, b; V)` whose weak derivative is `g ∈ L²(a, b; V*)`, with the integrated
derivative and energy identity known on every compact subinterval. To obtain traces at
`a` and `b` one has to extend `E` continuously to the closed interval. We build the
two extensions from which the endpoint theory is assembled.

Fix an anchor time `t₀ ∈ (a, b)`. The *dual endpoint extension* is
`t ↦ J(E t₀) + ∫_{t₀}^t g₀`, where `J = T.pivotToDual : H → V*` and `g₀` is the zero
extension of `g`; on `(a, b)` it equals `J(E t)`, and since `g₀ ∈ L¹(ℝ)` it is continuous
on all of `ℝ`. The *energy endpoint extension* is likewise
`t ↦ ‖E t₀‖² + 2 ∫_{t₀}^t g₀(u₀)`, which equals `‖E t‖²` on `(a, b)`. Reflecting the dual
extension evenly across both endpoints, and `g` oddly, gives a global primitive of the
odd reflection of `g` on the enlarged interval `(2a - b, 2b - a)` which agrees a.e. with
`T.energyToDual` of the evenly reflected trajectory. Evans starts the proof of §5.9.2,
Theorem 3 by extending `u` to a larger interval `[-σ, T + σ]`, without saying how; we
extend by reflection, so that mollification, or here direct evaluation, can reach `t = a`
and `t = b`.

## Main results

* `dualEndpointExtension`, `continuous_dualEndpointExtension`,
  `dualEndpointExtension_eq_pivotToDual`: the continuous `V*`-valued extension and its
  identification with `J(E t)` on the open interval.
* `energyEndpointExtension`, `continuous_energyEndpointExtension`,
  `energyEndpointExtension_eq_norm_sq`: the continuous scalar extension of `‖E t‖²`.
* `reflectedDualPrimitive`, `hasWeakTimeDerivative_reflectedDualPrimitive`: the primitive
  of the odd reflection `reflectedDerivativeExtension a b g`, and the fact that it has that
  reflection as weak derivative on all of `ℝ`.
* `reflectedDualPrimitive_eq_dualEndpointExtension`,
  `reflectedDualPrimitive_eq_reflectedDualEndpointExtension`: on `[a, b]` the reflected
  primitive is the dual endpoint extension, and globally it is the piecewise even
  reflection `reflectedDualEndpointExtension` of that extension.
* `ae_reflectedDualEndpointExtension_eq_energyToDual`: on the reflected domain the
  reflected dual extension is a.e. `T.energyToDual` of `reflectedIntervalExtension a b u`.

## Implementation notes

The anchor `t₀` is an arbitrary interior time; the extensions do not depend on it on the
open interval, but keeping it explicit avoids choosing one. Integrability hypotheses on
`g` and on the duality product `g(u)` over `Ioc a b` are stated as needed rather than
derived from `L²` membership, so the constructions apply to any integrable derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, proof of Theorem 3. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section DualExtension

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The global primitive of the reflected derivative, anchored at an
interior time. -/
noncomputable def reflectedDualPrimitive
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ) : ℝ → StrongDual ℝ V :=
  fun t ↦ T.pivotToDual (E.representative t₀) +
    dualPrimitive (reflectedDerivativeExtension a b g) t₀ t

omit [CompleteSpace V] in
/-- The reflected dual primitive has the odd reflected derivative globally
in the distributional sense.  Reflection removes endpoint junction terms:
the primitive is continuous across both junctions, while its derivative
changes sign exactly as prescribed by the chain rule. -/
theorem hasWeakTimeDerivative_reflectedDualPrimitive
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ)
    (hg : Integrable g (volume.restrict (Set.Ioc a b))) :
    HasWeakTimeDerivativeOn Set.univ
      (reflectedDualPrimitive T E t₀)
      (reflectedDerivativeExtension a b g) := by
  exact hasWeakTimeDerivativeOn_add_dualPrimitive
    (integrable_reflectedDerivativeExtension hg)
    (T.pivotToDual (E.representative t₀)) t₀

/-- Canonical continuous `V*` extension associated with an open-interval
Gelfand evolution, anchored at one interior time. -/
noncomputable def dualEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ) : ℝ → StrongDual ℝ V :=
  fun t ↦ T.pivotToDual (E.representative t₀) +
    dualPrimitive (intervalZeroExtension a b g) t₀ t

omit [CompleteSpace V] in
/-- On the original closed interval, the reflected primitive agrees with
the canonical dual endpoint extension. -/
theorem reflectedDualPrimitive_eq_dualEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) (ht : t ∈ Set.Icc a b) :
    reflectedDualPrimitive T E t₀ t = dualEndpointExtension T E t₀ t := by
  simp only [reflectedDualPrimitive, dualEndpointExtension, dualPrimitive]
  rw [intervalIntegral_reflectedDerivativeExtension_eq_zeroExtension ht₀ ht]

/-- Continuous dual extension obtained by reflecting the canonical endpoint
primitive across both endpoints. -/
noncomputable def reflectedDualEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ) : ℝ → StrongDual ℝ V :=
  fun t ↦
    if t < a then dualEndpointExtension T E t₀ (reflectTime a t)
    else if b < t then dualEndpointExtension T E t₀ (reflectTime b t)
    else dualEndpointExtension T E t₀ t

omit [CompleteSpace V] in
/-- The reflected derivative has one global integral primitive, and that
primitive is exactly the piecewise reflected endpoint extension. -/
theorem reflectedDualPrimitive_eq_reflectedDualEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    {t₀ : ℝ} (hab : a < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hg : Integrable g (volume.restrict (Set.Ioc a b))) :
    reflectedDualPrimitive T E t₀ = reflectedDualEndpointExtension T E t₀ := by
  funext t
  have hgRef : Integrable (reflectedDerivativeExtension a b g) volume :=
    integrable_reflectedDerivativeExtension hg
  have hg₀ : Integrable (intervalZeroExtension a b g) volume :=
    integrable_intervalZeroExtension hg
  by_cases hta : t < a
  · rw [reflectedDualEndpointExtension, ite_eq_left hta]
    simp only [reflectedDualPrimitive, dualEndpointExtension, dualPrimitive]
    congr 1
    calc
      (∫ r in t₀..t, reflectedDerivativeExtension a b g r) =
          (∫ r in t₀..a, reflectedDerivativeExtension a b g r) +
            ∫ r in a..t, reflectedDerivativeExtension a b g r := by
              exact (intervalIntegral.integral_add_adjacent_intervals
                hgRef.intervalIntegrable hgRef.intervalIntegrable).symm
      _ = (∫ r in t₀..a, intervalZeroExtension a b g r) +
            ∫ r in a..reflectTime a t,
              intervalZeroExtension a b g r := by
              rw [intervalIntegral_reflectedDerivativeExtension_eq_zeroExtension
                ht₀ ⟨le_rfl, hab.le⟩,
                intervalIntegral_reflectedDerivativeExtension_left hab hta]
      _ = ∫ r in t₀..reflectTime a t,
            intervalZeroExtension a b g r :=
              intervalIntegral.integral_add_adjacent_intervals
                hg₀.intervalIntegrable hg₀.intervalIntegrable
  · by_cases hbt : b < t
    · rw [reflectedDualEndpointExtension, ite_eq_right hta, ite_eq_left hbt]
      simp only [reflectedDualPrimitive, dualEndpointExtension, dualPrimitive]
      congr 1
      calc
        (∫ r in t₀..t, reflectedDerivativeExtension a b g r) =
            (∫ r in t₀..b, reflectedDerivativeExtension a b g r) +
              ∫ r in b..t, reflectedDerivativeExtension a b g r := by
                exact (intervalIntegral.integral_add_adjacent_intervals
                  hgRef.intervalIntegrable hgRef.intervalIntegrable).symm
        _ = (∫ r in t₀..b, intervalZeroExtension a b g r) +
              ∫ r in b..reflectTime b t,
                intervalZeroExtension a b g r := by
                rw [intervalIntegral_reflectedDerivativeExtension_eq_zeroExtension
                  ht₀ ⟨hab.le, le_rfl⟩,
                  intervalIntegral_reflectedDerivativeExtension_right hab hbt]
        _ = ∫ r in t₀..reflectTime b t,
              intervalZeroExtension a b g r :=
                intervalIntegral.integral_add_adjacent_intervals
                  hg₀.intervalIntegrable hg₀.intervalIntegrable
    · rw [reflectedDualEndpointExtension, ite_eq_right hta, ite_eq_right hbt]
      exact reflectedDualPrimitive_eq_dualEndpointExtension T E ht₀
        ⟨not_lt.mp hta, not_lt.mp hbt⟩

/-- Canonical continuous extension of the squared pivot norm. -/
noncomputable def energyEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ) : ℝ → ℝ :=
  fun t ↦ ‖E.representative t₀‖ ^ 2 +
    2 * ∫ r in t₀..t, intervalZeroExtension a b (fun q ↦ g q (u q)) r

omit [CompleteSpace V] in
/-- The canonical dual endpoint extension is continuous whenever the weak
derivative is Bochner integrable on the finite interval. -/
theorem continuous_dualEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ)
    (hg : Integrable g (volume.restrict (Set.Ioc a b))) :
    Continuous (dualEndpointExtension T E t₀) := by
  apply continuous_const.add
  exact intervalIntegral.continuous_primitive
    (fun s t ↦ (integrable_intervalZeroExtension hg).intervalIntegrable) t₀

omit [CompleteSpace V] in
/-- The canonical energy endpoint extension is continuous whenever the
duality product is integrable on the finite interval. -/
theorem continuous_energyEndpointExtension
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (t₀ : ℝ)
    (hgu : Integrable (fun r ↦ g r (u r))
      (volume.restrict (Set.Ioc a b))) :
    Continuous (energyEndpointExtension T E t₀) := by
  apply continuous_const.add
  apply continuous_const.mul
  exact intervalIntegral.continuous_primitive
    (fun s t ↦ (integrable_intervalZeroExtension hgu).intervalIntegrable) t₀

omit [CompleteSpace V] in
/-- On the open interval, the canonical dual endpoint extension is exactly
the pivot image of the already constructed Lions–Magenes representative. -/
theorem dualEndpointExtension_eq_pivotToDual
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    dualEndpointExtension T E t₀ t = T.pivotToDual (E.representative t) := by
  rw [dualEndpointExtension, dualPrimitive,
    intervalIntegral_intervalZeroExtension_eq ht₀ ht]
  exact (E.integratedDerivative t₀ t ht₀ ht).eq_add_integral
    t Set.right_mem_uIcc |>.symm

omit [CompleteSpace V] in
/-- On the open interval, the canonical scalar endpoint extension is the
squared pivot norm of the Lions–Magenes representative. -/
theorem energyEndpointExtension_eq_norm_sq
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    energyEndpointExtension T E t₀ t = ‖E.representative t‖ ^ 2 := by
  rw [energyEndpointExtension,
    intervalIntegral_intervalZeroExtension_eq ht₀ ht]
  linarith [E.energyIdentity t₀ t ht₀ ht]

omit [CompleteSpace V] in
/-- On the reflected time domain, the reflected dual extension is almost
everywhere the canonical `V → V*` image of the reflected `V` trajectory.
The only excluded points are the two reflection junctions, which are
Lebesgue-null. -/
theorem ae_reflectedDualEndpointExtension_eq_energyToDual
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    {t₀ : ℝ} (hab : a < b) (ht₀ : t₀ ∈ Set.Ioo a b) :
    reflectedDualEndpointExtension T E t₀ =ᵐ[volume.restrict (reflectedTimeDomain a b)]
      fun t ↦ T.energyToDual (reflectedIntervalExtension a b u t) := by
  have hbase : ∀ᵐ s ∂volume, s ∈ Set.Ioo a b →
      dualEndpointExtension T E t₀ s = T.energyToDual (u s) := by
    have hae := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).1
      E.ae_eq_inclusion
    filter_upwards [hae] with s hs
    intro hsI
    rw [dualEndpointExtension_eq_pivotToDual T E ht₀ hsI, hs hsI]
    rfl
  have hleft :=
    (measurePreserving_reflectTime a).quasiMeasurePreserving
      |>.tendsto_ae.eventually hbase
  have hright :=
    (measurePreserving_reflectTime b).quasiMeasurePreserving
      |>.tendsto_ae.eventually hbase
  have hneA : ∀ᵐ t ∂volume, t ≠ a := by
    apply MeasureTheory.ae_iff.2
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton a : volume ({a} : Set ℝ) = 0)
  have hneB : ∀ᵐ t ∂volume, t ≠ b := by
    apply MeasureTheory.ae_iff.2
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton b : volume ({b} : Set ℝ) = 0)
  change ∀ᵐ t ∂volume.restrict (reflectedTimeDomain a b),
    reflectedDualEndpointExtension T E t₀ t =
      T.energyToDual (reflectedIntervalExtension a b u t)
  rw [MeasureTheory.ae_restrict_iff' (by
    simpa only [reflectedTimeDomain] using
      (measurableSet_Ioo : MeasurableSet (Set.Ioo (2 * a - b) (2 * b - a))))]
  filter_upwards [hbase, hleft, hright, hneA, hneB] with t hm hl hr hta htb
  intro htU
  change 2 * a - b < t ∧ t < 2 * b - a at htU
  by_cases htaLt : t < a
  · have hRa : reflectTime a t ∈ Set.Ioo a b := by
      constructor <;> simp only [reflectTime] <;> linarith
    have hEq := hl hRa
    simpa [reflectedDualEndpointExtension, reflectedIntervalExtension,
      htaLt, intervalZeroExtension, Set.indicator_of_mem
        (Set.Ioo_subset_Ioc_self hRa), GelfandTriple.energyToDual] using hEq
  · by_cases hbt : b < t
    · have hRb : reflectTime b t ∈ Set.Ioo a b := by
        constructor <;> simp only [reflectTime] <;> linarith
      have hEq := hr hRb
      have hnotA : ¬t < a := not_lt_of_ge (hab.le.trans hbt.le)
      simpa [reflectedDualEndpointExtension, reflectedIntervalExtension,
        hnotA, hbt, intervalZeroExtension, Set.indicator_of_mem
          (Set.Ioo_subset_Ioc_self hRb), GelfandTriple.energyToDual] using hEq
    · have htI : t ∈ Set.Ioo a b := by
        exact ⟨lt_of_le_of_ne (not_lt.mp htaLt) (Ne.symm hta),
          lt_of_le_of_ne (not_lt.mp hbt) htb⟩
      have hEq := hm htI
      simpa [reflectedDualEndpointExtension, reflectedIntervalExtension,
        htaLt, hbt, intervalZeroExtension, Set.indicator_of_mem
          (Set.Ioo_subset_Ioc_self htI), GelfandTriple.energyToDual] using hEq

end DualExtension

end PDE.Analysis.Evolution
