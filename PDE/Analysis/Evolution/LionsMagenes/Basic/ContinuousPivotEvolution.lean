/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import PDE.Analysis.Evolution.LionsMagenes.Basic.IntegratedDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative

/-!
# Continuous pivot evolutions

Let `V ↪ H ↪ V*` be a Gelfand triple, `u : ℝ → V` a trajectory and `g : ℝ → V*` a
candidate time derivative. The conclusion of the Lions–Magenes theorem is a
representative `E : ℝ → H`, continuous in `H`, with `E = i ∘ u` a.e., whose image
`J ∘ E` in `V*` has integrated derivative `g`, and which satisfies the energy identity

`‖E(t)‖² - ‖E(s)‖² = 2 ∫ₛᵗ g(r)(u(r)) dr`.

The structures `ContinuousPivotEvolution`, `ContinuousPivotEvolutionOn` and
`ContinuousPivotEvolutionOnOpen` record this on the whole line, on a closed interval
`[a, b]` (endpoints included) and between interior times of `(a, b)`.

## Main results

* `ContinuousPivotEvolutionOn.representative_eqOn`,
  `representative_eq_of_mem_Ioo`: two continuous representatives of the same trajectory
  agree wherever both are defined.
* `ContinuousPivotEvolutionOn.subinterval`, `toOpen`,
  `ContinuousPivotEvolutionOnOpen.subinterval`, `toClosedSubinterval`: restriction.
* `ContinuousPivotEvolutionOn.cross_energy_identity`: the polarized identity
  `⟪E₁(t), E₂(t)⟫ - ⟪E₁(s), E₂(s)⟫ = ∫ₛᵗ (g₁(u₂) + g₂(u₁))`.
* `ContinuousPivotEvolutionOn.absolutelyContinuousOnInterval_norm_sq`,
  `ae_hasDerivWithinAt_norm_sq`: `‖E(t)‖²` is absolutely continuous with derivative
  `2 g(t)(u(t))` a.e.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3, and the energy identity (12) in its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Lions–Magenes time regularity on the whole time line for a trajectory `u : ℝ → V`
and a `V*`-valued derivative `g`: an `H`-continuous representative of `i ∘ u` whose
image in `V*` has integrated derivative `g` on every interval, with the energy identity
`‖E(b)‖² - ‖E(a)‖² = 2 ∫ₐᵇ g(u)` for all `a, b`. -/
structure ContinuousPivotEvolution
    (T : GelfandTriple (V := V) (H := H))
    (u : ℝ → V) (g : ℝ → StrongDual ℝ V) where
  /-- Everywhere-defined pivot-space representative. -/
  representative : ℝ → H
  /-- Strong continuity in the pivot space. -/
  continuous : Continuous representative
  /-- Identification with the original energy-space trajectory. -/
  ae_eq_inclusion : representative =ᵐ[volume] fun t ↦ T.inclusion (u t)
  /-- Fundamental theorem of calculus in `V*` on every finite interval. -/
  integratedDerivative : ∀ a b,
    HasIntegratedDualDerivativeOn T representative g a b
  /-- Exact two-time energy identity. -/
  energyIdentity : ∀ a b,
    ‖representative b‖ ^ 2 - ‖representative a‖ ^ 2 =
      2 * ∫ t in a..b, g t (u t)

/-- The Lions–Magenes conclusion on the closed interval `[a, b]`, endpoints included:
`u` has a representative continuous from `[a, b]` into `H`, that representative has the
integrated `V*` derivative `g`, and its pivot norm obeys the energy identity between any
two times of `[a, b]`. Evans gets this regularity for weak solutions from §5.9.2,
Theorem 3 (continuity into `L²(U)` and the energy identity (12)). -/
structure ContinuousPivotEvolutionOn
    (T : GelfandTriple (V := V) (H := H))
    (u : ℝ → V) (g : ℝ → StrongDual ℝ V) (a b : ℝ) where
  /-- Everywhere-defined pivot-space representative. -/
  representative : ℝ → H
  /-- Strong continuity on the closed time interval. -/
  continuousOn : ContinuousOn representative (uIcc a b)
  /-- Identification with the original energy-space trajectory on the
  interval, modulo the usual Bochner almost-everywhere equivalence. -/
  ae_eq_inclusion : representative =ᵐ[volume.restrict (uIcc a b)]
    fun t ↦ T.inclusion (u t)
  /-- Fundamental theorem of calculus in `V*`, including the endpoints. -/
  integratedDerivative : HasIntegratedDualDerivativeOn T representative g a b
  /-- Exact two-time energy balance on every subinterval. -/
  energyIdentity : ∀ s t, s ∈ uIcc a b → t ∈ uIcc a b →
    ‖representative t‖ ^ 2 - ‖representative s‖ ^ 2 =
      2 * ∫ r in s..t, g r (u r)

/-- The Lions–Magenes conclusion on an open finite time interval `(a, b)`: one
representative continuous on `(a, b)`, with the integrated derivative and the energy
identity between any two interior times. Nothing is asserted at the endpoints. -/
structure ContinuousPivotEvolutionOnOpen
    (T : GelfandTriple (V := V) (H := H))
    (u : ℝ → V) (g : ℝ → StrongDual ℝ V) (a b : ℝ) where
  /-- Everywhere-defined representative; its values outside `(a,b)` are
  irrelevant. -/
  representative : ℝ → H
  /-- Strong continuity at every interior time. -/
  continuousOn : ContinuousOn representative (Ioo a b)
  /-- Identification with the Bochner trajectory on the open interval. -/
  ae_eq_inclusion : representative =ᵐ[volume.restrict (Ioo a b)]
    fun t ↦ T.inclusion (u t)
  /-- Fundamental theorem of calculus between arbitrary interior times. -/
  integratedDerivative : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b →
    HasIntegratedDualDerivativeOn T representative g s t
  /-- Exact energy identity between arbitrary interior times. -/
  energyIdentity : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b →
    ‖representative t‖ ^ 2 - ‖representative s‖ ^ 2 =
      2 * ∫ r in s..t, g r (u r)

namespace ContinuousPivotEvolutionOn

/--
Two continuous pivot representatives of the same trajectory on `[a, b]`, `a < b`, agree
at every point of `[a, b]`, whatever their derivatives `g₁`, `g₂`. Both are a.e. equal
to `T.inclusion ∘ u`, and continuity upgrades a.e. equality to equality.
-/
theorem representative_eqOn
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g₁ g₂ : ℝ → StrongDual ℝ V}
    {a b : ℝ}
    (E₁ : ContinuousPivotEvolutionOn T u g₁ a b)
    (E₂ : ContinuousPivotEvolutionOn T u g₂ a b)
    (hab : a < b) :
    Set.EqOn E₁.representative E₂.representative (Set.Icc a b) := by
  have hae :
      E₁.representative =ᵐ[volume.restrict (Set.Icc a b)]
        E₂.representative := by
    simpa only [Set.uIcc_of_le hab.le] using
      E₁.ae_eq_inclusion.trans E₂.ae_eq_inclusion.symm
  exact MeasureTheory.Measure.eqOn_Icc_of_ae_eq
    volume hab.ne hae
    (by simpa only [Set.uIcc_of_le hab.le] using E₁.continuousOn)
    (by simpa only [Set.uIcc_of_le hab.le] using E₂.continuousOn)

/-- Restriction of an endpoint-inclusive Lions–Magenes evolution on `[a, b]` to a
closed subinterval `[c, d]`, with `c, d ∈ [a, b]`. -/
def subinterval
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b c d : ℝ}
    (E : ContinuousPivotEvolutionOn T u g a b)
    (hc : c ∈ uIcc a b) (hd : d ∈ uIcc a b) :
    ContinuousPivotEvolutionOn T u g c d := by
  have hsub : uIcc c d ⊆ uIcc a b := uIcc_subset_uIcc hc hd
  refine {
    representative := E.representative
    continuousOn := E.continuousOn.mono hsub
    ae_eq_inclusion := ?_
    integratedDerivative := E.integratedDerivative.subinterval hc hd
    energyIdentity := ?_
  }
  · exact E.ae_eq_inclusion.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hsub))
  · intro s t hs ht
    exact E.energyIdentity s t (hsub hs) (hsub ht)

/--
If a Lions–Magenes representative vanishes on a closed interval `[c, d] ⊆ [a, b]` with
`c < d`, then its derivative `g` vanishes a.e. on `[c, d]`.

At a.e. interior time, `g(t)` is the strong derivative of
`t ↦ T.pivotToDual (E.representative t)`, which is locally constant there.
-/
theorem integratedDerivative_ae_eq_zero_of_representative_eq_zero
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b c d : ℝ}
    (E : ContinuousPivotEvolutionOn T u g a b)
    (hcd : c < d)
    (hc : c ∈ uIcc a b) (hd : d ∈ uIcc a b)
    (hzero : ∀ t ∈ Icc c d, E.representative t = 0) :
    g =ᵐ[volume.restrict (Icc c d)]
      (fun _ ↦ (0 : StrongDual ℝ V)) := by
  have hderivIoc :
      ∀ᵐ t ∂volume.restrict (Ioc c d),
        HasDerivAt
          (fun s ↦ T.pivotToDual (E.representative s)) (g t) t :=
    (E.integratedDerivative.subinterval hc hd).ae_hasDerivAt_pivotToDual hcd
  have hIooSubset : Ioo c d ⊆ Ioc c d := Ioo_subset_Ioc_self
  have hderivIoo :
      ∀ᵐ t ∂volume.restrict (Ioo c d),
        HasDerivAt
          (fun s ↦ T.pivotToDual (E.representative s)) (g t) t :=
    hderivIoc.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hIooSubset))
  have hzeroIoo :
      g =ᵐ[volume.restrict (Ioo c d)]
        (fun _ ↦ (0 : StrongDual ℝ V)) := by
    filter_upwards [hderivIoo, ae_restrict_mem measurableSet_Ioo]
      with t hderiv ht
    have hlocal :
        (fun s ↦ T.pivotToDual (E.representative s)) =ᶠ[𝓝 t]
          (fun _ ↦ (0 : StrongDual ℝ V)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [hzero s ⟨hs.1.le, hs.2.le⟩, map_zero]
    have hzeroDeriv :
        HasDerivAt
          (fun s ↦ T.pivotToDual (E.representative s))
          (0 : StrongDual ℝ V) t :=
      (hasDerivAt_const t (0 : StrongDual ℝ V)).congr_of_eventuallyEq
        hlocal
    exact hderiv.unique hzeroDeriv
  exact (ae_restrict_congr_set Ioo_ae_eq_Icc).1 hzeroIoo

/--
Polarized Lions–Magenes identity for two weak Gelfand evolutions.

Suppose `E₁`, `E₂`, and `E₁₂` are the continuous pivot evolutions associated
with `(u₁,g₁)`, `(u₂,g₂)`, and their pointwise sum.  Once the representative
of the sum is identified with `E₁.representative + E₂.representative`, the
three quadratic energy identities polarize to

`⟪E₁(t),E₂(t)⟫ - ⟪E₁(s),E₂(s)⟫
  = ∫ₛᵗ (g₁(r)(u₂(r)) + g₂(r)(u₁(r))) dr`.

This is the product rule for weak Gelfand evolutions. It follows from the three energy
identities by the real polarization identity.
-/
theorem cross_energy_identity
    {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : ℝ → V}
    {g₁ g₂ : ℝ → StrongDual ℝ V}
    {a b : ℝ}
    (E₁ : ContinuousPivotEvolutionOn T u₁ g₁ a b)
    (E₂ : ContinuousPivotEvolutionOn T u₂ g₂ a b)
    (E₁₂ : ContinuousPivotEvolutionOn T
      (fun t ↦ u₁ t + u₂ t) (fun t ↦ g₁ t + g₂ t) a b)
    (hrep : ∀ t ∈ Set.uIcc a b,
      E₁₂.representative t =
        E₁.representative t + E₂.representative t)
    {s t : ℝ} (hs : s ∈ Set.uIcc a b) (ht : t ∈ Set.uIcc a b)
    (h₁₁ : IntervalIntegrable (fun r ↦ g₁ r (u₁ r)) volume s t)
    (h₁₂ : IntervalIntegrable (fun r ↦ g₁ r (u₂ r)) volume s t)
    (h₂₁ : IntervalIntegrable (fun r ↦ g₂ r (u₁ r)) volume s t)
    (h₂₂ : IntervalIntegrable (fun r ↦ g₂ r (u₂ r)) volume s t) :
    inner ℝ (E₁.representative t) (E₂.representative t) -
        inner ℝ (E₁.representative s) (E₂.representative s) =
      ∫ r in s..t, g₁ r (u₂ r) + g₂ r (u₁ r) := by
  have hsumPair :
      (∫ r in s..t,
        (g₁ r + g₂ r) (u₁ r + u₂ r)) =
      (∫ r in s..t, g₁ r (u₁ r)) +
        (∫ r in s..t, g₁ r (u₂ r)) +
        (∫ r in s..t, g₂ r (u₁ r)) +
        ∫ r in s..t, g₂ r (u₂ r) := by
    calc
      (∫ r in s..t,
          (g₁ r + g₂ r) (u₁ r + u₂ r)) =
          ∫ r in s..t,
            (g₁ r (u₁ r) + g₁ r (u₂ r)) +
              (g₂ r (u₁ r) + g₂ r (u₂ r)) := by
        apply intervalIntegral.integral_congr
        intro r _hr
        simp only [add_apply, map_add]
        ring
      _ = (∫ r in s..t, g₁ r (u₁ r) + g₁ r (u₂ r)) +
          ∫ r in s..t, g₂ r (u₁ r) + g₂ r (u₂ r) := by
        rw [intervalIntegral.integral_add (h₁₁.add h₁₂)
          (h₂₁.add h₂₂)]
      _ = ((∫ r in s..t, g₁ r (u₁ r)) +
            ∫ r in s..t, g₁ r (u₂ r)) +
          ((∫ r in s..t, g₂ r (u₁ r)) +
            ∫ r in s..t, g₂ r (u₂ r)) := by
        rw [intervalIntegral.integral_add h₁₁ h₁₂,
          intervalIntegral.integral_add h₂₁ h₂₂]
      _ = _ := by ring
  have hcrossPair :
      (∫ r in s..t, g₁ r (u₂ r) + g₂ r (u₁ r)) =
        (∫ r in s..t, g₁ r (u₂ r)) +
          ∫ r in s..t, g₂ r (u₁ r) :=
    intervalIntegral.integral_add h₁₂ h₂₁
  have henergy₁ := E₁.energyIdentity s t hs ht
  have henergy₂ := E₂.energyIdentity s t hs ht
  have henergy₁₂ := E₁₂.energyIdentity s t hs ht
  rw [hrep t ht, hrep s hs, norm_add_sq_real, norm_add_sq_real,
    hsumPair] at henergy₁₂
  rw [hcrossPair]
  nlinarith

/-- If the duality product `t ↦ g t (u t)` is interval integrable, the squared pivot norm
of a Lions–Magenes representative is absolutely continuous on `[a, b]`: by the energy
identity it is a constant plus an indefinite integral. -/
theorem absolutelyContinuousOnInterval_norm_sq
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b : ℝ}
    (E : ContinuousPivotEvolutionOn T u g a b)
    (hgu : IntervalIntegrable (fun t ↦ g t (u t)) volume a b) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ ‖E.representative t‖ ^ 2) a b := by
  apply absolutelyContinuousOnInterval_of_eq_add_integral
      (dw := fun t ↦ 2 * g t (u t))
  · exact hgu.const_mul 2
  · intro t ht
    have henergy := E.energyIdentity a t Set.left_mem_uIcc ht
    rw [intervalIntegral.integral_const_mul]
    linarith

/-- Almost-everywhere differential form of the Lions–Magenes energy law:

`d/dt ‖u(t)‖_H² = 2 ⟨u_t(t), u(t)⟩_{V*,V}`.

For a.e. `t ∈ [a, b]`, `‖E(·)‖²` has derivative `2 g(t)(u(t))` within `[a, b]` at `t`,
provided `t ↦ g t (u t)` is interval integrable. -/
theorem ae_hasDerivWithinAt_norm_sq
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b : ℝ}
    (E : ContinuousPivotEvolutionOn T u g a b)
    (hgu : IntervalIntegrable (fun t ↦ g t (u t)) volume a b) :
    ∀ᵐ t, t ∈ uIcc a b →
      HasDerivWithinAt (fun s ↦ ‖E.representative s‖ ^ 2)
        (2 * g t (u t)) (uIcc a b) t := by
  have hprimitive :=
    (hgu.const_mul 2).ae_hasDerivAt_integral
  filter_upwards [hprimitive] with t ht
  intro htI
  let P : ℝ → ℝ := fun s ↦
    ‖E.representative a‖ ^ 2 + ∫ r in a..s, 2 * g r (u r)
  have hP : HasDerivAt P (2 * g t (u t)) t := by
    change HasDerivAt
      ((fun _ : ℝ ↦ ‖E.representative a‖ ^ 2) +
        fun s ↦ ∫ r in a..s, 2 * g r (u r))
      (2 * g t (u t)) t
    simpa only [zero_add] using
      (hasDerivAt_const t (‖E.representative a‖ ^ 2)).add
        (ht htI a Set.left_mem_uIcc)
  have hEq : ∀ s ∈ uIcc a b,
      ‖E.representative s‖ ^ 2 = P s := by
    intro s hs
    have henergy := E.energyIdentity a s Set.left_mem_uIcc hs
    change ‖E.representative s‖ ^ 2 =
      ‖E.representative a‖ ^ 2 + ∫ r in a..s, 2 * g r (u r)
    rw [intervalIntegral.integral_const_mul]
    linarith
  apply hP.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact hEq s hs
  · exact hEq t htI

/-- A closed-interval Lions–Magenes evolution on `[a, b]` restricts to an
open-interval evolution on `(a, b)`. -/
def toOpen
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b : ℝ}
    (E : ContinuousPivotEvolutionOn T u g a b) :
    ContinuousPivotEvolutionOnOpen T u g a b := by
  have hsub : Ioo a b ⊆ uIcc a b :=
    Ioo_subset_Icc_self.trans Icc_subset_uIcc
  refine {
    representative := E.representative
    continuousOn := E.continuousOn.mono hsub
    ae_eq_inclusion := ?_
    integratedDerivative := ?_
    energyIdentity := ?_
  }
  · exact E.ae_eq_inclusion.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hsub))
  · intro s t hs ht
    exact E.integratedDerivative.subinterval (hsub hs) (hsub ht)
  · intro s t hs ht
    exact E.energyIdentity s t (hsub hs) (hsub ht)

/-- Two local representatives agree at every point lying in the interiors of
both (ordered) time intervals. -/
theorem representative_eq_of_mem_Ioo
    {T : GelfandTriple (V := V) (H := H)} {u : ℝ → V}
    {g₁ g₂ : ℝ → StrongDual ℝ V}
    {a₁ b₁ a₂ b₂ x : ℝ}
    (E₁ : ContinuousPivotEvolutionOn T u g₁ a₁ b₁)
    (E₂ : ContinuousPivotEvolutionOn T u g₂ a₂ b₂)
    (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hx₁ : x ∈ Ioo a₁ b₁) (hx₂ : x ∈ Ioo a₂ b₂) :
    E₁.representative x = E₂.representative x := by
  let U : Set ℝ := Ioo (max a₁ a₂) (min b₁ b₂)
  have hU₁ : U ⊆ uIcc a₁ b₁ := by
    rw [uIcc_of_le hab₁]
    intro y hy
    simp only [U, mem_Ioo, max_lt_iff, lt_min_iff] at hy
    exact ⟨hy.1.1.le, hy.2.1.le⟩
  have hU₂ : U ⊆ uIcc a₂ b₂ := by
    rw [uIcc_of_le hab₂]
    intro y hy
    simp only [U, mem_Ioo, max_lt_iff, lt_min_iff] at hy
    exact ⟨hy.1.2.le, hy.2.2.le⟩
  have hae₁ : E₁.representative =ᵐ[volume.restrict U]
      fun t ↦ T.inclusion (u t) :=
    E₁.ae_eq_inclusion.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hU₁))
  have hae₂ : E₂.representative =ᵐ[volume.restrict U]
      fun t ↦ T.inclusion (u t) :=
    E₂.ae_eq_inclusion.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hU₂))
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq
    (hae₁.trans hae₂.symm) isOpen_Ioo
      (E₁.continuousOn.mono hU₁) (E₂.continuousOn.mono hU₂)
  apply heq
  simp only [U, mem_Ioo, max_lt_iff, lt_min_iff]
  exact ⟨⟨hx₁.1, hx₂.1⟩, hx₁.2, hx₂.2⟩

end ContinuousPivotEvolutionOn

namespace ContinuousPivotEvolutionOnOpen

/-- Restriction of an open-interval Lions–Magenes evolution on `(a, b)` to `(c, d)` for
`c, d ∈ (a, b)`. -/
def subinterval
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b c d : ℝ}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) :
    ContinuousPivotEvolutionOnOpen T u g c d := by
  have hsub : Ioo c d ⊆ Ioo a b := by
    intro t ht
    exact ⟨hc.1.trans ht.1, ht.2.trans hd.2⟩
  refine {
    representative := E.representative
    continuousOn := E.continuousOn.mono hsub
    ae_eq_inclusion := ?_
    integratedDerivative := ?_
    energyIdentity := ?_
  }
  · exact E.ae_eq_inclusion.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hsub))
  · intro s t hs ht
    exact E.integratedDerivative s t (hsub hs) (hsub ht)
  · intro s t hs ht
    exact E.energyIdentity s t (hsub hs) (hsub ht)

/-- An open-interval Lions–Magenes evolution on `(a, b)` restricts to an
endpoint-inclusive evolution on the closed interval `[[c, d]]` for `c, d ∈ (a, b)`. -/
def toClosedSubinterval
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b c d : ℝ}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) :
    ContinuousPivotEvolutionOn T u g c d := by
  have hsub : uIcc c d ⊆ Ioo a b := by
    intro t ht
    rcases le_total c d with hcd | hdc
    · rw [uIcc_of_le hcd] at ht
      exact ⟨hc.1.trans_le ht.1, ht.2.trans_lt hd.2⟩
    · rw [uIcc_of_ge hdc] at ht
      exact ⟨hd.1.trans_le ht.1, ht.2.trans_lt hc.2⟩
  refine {
    representative := E.representative
    continuousOn := E.continuousOn.mono hsub
    ae_eq_inclusion := ?_
    integratedDerivative := E.integratedDerivative c d
      (hsub Set.left_mem_uIcc) (hsub Set.right_mem_uIcc)
    energyIdentity := ?_
  }
  · exact E.ae_eq_inclusion.filter_mono
      (MeasureTheory.ae_mono
        ((volume : Measure ℝ).restrict_mono_set hsub))
  · intro s t hs ht
    exact E.energyIdentity s t (hsub hs) (hsub ht)

/-- The squared pivot norm of an open-interval evolution is absolutely continuous on
`[[c, d]]` for `c, d ∈ (a, b)`, given integrability of `t ↦ g t (u t)` between `c` and
`d`. -/
theorem absolutelyContinuousOnInterval_norm_sq
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b c d : ℝ}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hgu : IntervalIntegrable (fun t ↦ g t (u t)) volume c d) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ ‖E.representative t‖ ^ 2) c d :=
  ContinuousPivotEvolutionOn.absolutelyContinuousOnInterval_norm_sq
    (E.toClosedSubinterval hc hd) hgu

/-- Local almost-everywhere differential energy identity on an open time
interval. On each compact interior interval,

`d/dt ‖u(t)‖_H² = 2 ⟨u_t(t),u(t)⟩_{V*,V}`

holds as a derivative within that interval. -/
theorem ae_hasDerivWithinAt_norm_sq
    {T : GelfandTriple (V := V) (H := H)}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {a b c d : ℝ}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b)
    (hgu : IntervalIntegrable (fun t ↦ g t (u t)) volume c d) :
    ∀ᵐ t, t ∈ uIcc c d →
      HasDerivWithinAt (fun s ↦ ‖E.representative s‖ ^ 2)
        (2 * g t (u t)) (uIcc c d) t :=
  ContinuousPivotEvolutionOn.ae_hasDerivWithinAt_norm_sq
    (E.toClosedSubinterval hc hd) hgu

end ContinuousPivotEvolutionOnOpen

end PDE.Analysis.Evolution
