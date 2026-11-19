/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.Reflection
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Reflected extensions of finite-interval trajectories

A trajectory `f` defined on a finite time interval `(a, b)` can be extended to the whole
line in three ways used by the endpoint theory: by zero, `intervalZeroExtension`; by even
reflection across both endpoints, `reflectedIntervalExtension`, so that
`f(2a - t)` is used for `t < a` and `f(2b - t)` for `t > b`; and, for a derivative `g`,
by odd reflection, `reflectedDerivativeExtension`, which carries the sign change
`-g(2a - t)`, `-g(2b - t)` dictated by the chain rule. If `f` has weak derivative `g` on
`(a, b)` then the even extension of `f` has the odd extension of `g` as weak derivative
across the junctions, with no boundary terms; that fact is proved in
`PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.DualExtension`. Evans extends
`W^{1,p}` functions across a flat boundary by the higher-order reflection (3) of §5.4,
which keeps `C¹` functions `C¹`; in one time variable, for weak derivatives, the even
reflection is enough.

## Main results

* `intervalZeroExtension`, `integrable_intervalZeroExtension`,
  `memLp_intervalZeroExtension`: the zero extension is the indicator of `Ioc a b` times
  `f`, and preserves `L¹` and `Lᵖ` membership relative to the restricted measure.
* `reflectedIntervalExtension`, `integrable_reflectedIntervalExtension`,
  `memLp_reflectedIntervalExtension`: the even extension and its `Lᵖ` bounds, using only
  that `t ↦ 2a - t` and `t ↦ 2b - t` preserve Lebesgue measure.
* `reflectedDerivativeExtension`, `integrable_reflectedDerivativeExtension`,
  `memLp_reflectedDerivativeExtension`: the same for the odd extension.
* `intervalIntegral_reflectedDerivativeExtension_eq_zeroExtension`,
  `intervalIntegral_intervalZeroExtension_eq`,
  `intervalIntegral_reflectedDerivativeExtension_left`, `_right`: the interval integrals of
  the extensions, reduced to integrals of `f` or `g` by the substitutions `r ↦ 2a - r`,
  `r ↦ 2b - r`.
* `reflectedTimeDomain`: the enlarged interval `(2a - b, 2b - a)` on which the reflected
  extensions carry information about `f`.

## Implementation notes

The base extension is by zero on `Ioc a b` rather than `Ioo a b`; the two differ by a null
set and `Ioc` matches the measure used for the Bochner spaces in the Galerkin
development. Far outside `[a, b]` the reflected argument leaves `(a, b)`, so the reflected
extensions vanish there and are integrable on all of `ℝ`, not just locally.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1 and the higher-order reflection (3) in its
  proof. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

section ReflectedExtension

/-- Zero extension of a time-dependent function from `(a,b)` to the whole
real line.  The half-open set `Ioc` is measure-equivalent to the open interval
and matches the Bochner spaces used in the Galerkin development. -/
noncomputable def intervalZeroExtension {X : Type*} [Zero X]
    (a b : ℝ) (f : ℝ → X) : ℝ → X :=
  (Set.Ioc a b).indicator f

/-- Integrability for the restricted measure is exactly what is needed for
integrability of the zero extension under Lebesgue measure. -/
theorem integrable_intervalZeroExtension
    {X : Type*} [NormedAddCommGroup X]
    {a b : ℝ} {f : ℝ → X}
    (hf : Integrable f (volume.restrict (Set.Ioc a b))) :
    Integrable (intervalZeroExtension a b f) volume := by
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2 hf

/-- Zero extension preserves every Bochner `Lᵖ` class. -/
theorem memLp_intervalZeroExtension
    {X : Type*} [NormedAddCommGroup X]
    {a b : ℝ} {f : ℝ → X} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Set.Ioc a b))) :
    MemLp (intervalZeroExtension a b f) p volume := by
  exact (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 hf

/-- Even reflection of a zero-extended interval trajectory across both
endpoints.  Far outside the interval the reflected argument lands where the
zero extension vanishes, so this remains globally integrable. -/
noncomputable def reflectedIntervalExtension {X : Type*} [Zero X]
    (a b : ℝ) (f : ℝ → X) : ℝ → X :=
  fun t ↦
    if t < a then intervalZeroExtension a b f (reflectTime a t)
    else if b < t then intervalZeroExtension a b f (reflectTime b t)
    else intervalZeroExtension a b f t

/-- Odd reflection of a derivative across both endpoints.  The minus signs
are the chain-rule factors from reflection of the time coordinate. -/
noncomputable def reflectedDerivativeExtension
    {X : Type*} [AddGroup X]
    (a b : ℝ) (g : ℝ → X) : ℝ → X :=
  fun t ↦
    if t < a then -intervalZeroExtension a b g (reflectTime a t)
    else if b < t then -intervalZeroExtension a b g (reflectTime b t)
    else intervalZeroExtension a b g t

/-- Integrability is preserved by the two even endpoint reflections. -/
theorem integrable_reflectedIntervalExtension
    {X : Type*} [NormedAddCommGroup X]
    {a b : ℝ} {f : ℝ → X}
    (hf : Integrable f (volume.restrict (Set.Ioc a b))) :
    Integrable (reflectedIntervalExtension a b f) volume := by
  let f₀ := intervalZeroExtension a b f
  have hf₀ : Integrable f₀ volume := integrable_intervalZeroExtension hf
  have hleft : Integrable (fun t ↦ f₀ (reflectTime a t)) volume := by
    change Integrable (f₀ ∘ reflectTime a) volume
    exact ((measurePreserving_reflectTime a).integrable_comp
      hf₀.aestronglyMeasurable).2 hf₀
  have hright : Integrable (fun t ↦ f₀ (reflectTime b t)) volume := by
    change Integrable (f₀ ∘ reflectTime b) volume
    exact ((measurePreserving_reflectTime b).integrable_comp
      hf₀.aestronglyMeasurable).2 hf₀
  have hinner : Integrable
      ((Set.Ioi b).piecewise
        (fun t ↦ f₀ (reflectTime b t)) f₀) volume :=
    Integrable.piecewise measurableSet_Ioi.nullMeasurableSet hright.integrableOn hf₀.integrableOn
  have hall : Integrable
      ((Set.Iio a).piecewise
        (fun t ↦ f₀ (reflectTime a t))
        ((Set.Ioi b).piecewise
          (fun t ↦ f₀ (reflectTime b t)) f₀)) volume :=
    Integrable.piecewise measurableSet_Iio.nullMeasurableSet hleft.integrableOn hinner.integrableOn
  apply hall.congr
  filter_upwards with t
  simp only [reflectedIntervalExtension, f₀, Set.piecewise,
    Set.mem_Iio, Set.mem_Ioi]

/-- Even reflection across both endpoints preserves every Bochner `Lᵖ`
class.  Measure preservation of the affine reflections is the only analytic
input. -/
theorem memLp_reflectedIntervalExtension
    {X : Type*} [NormedAddCommGroup X]
    {a b : ℝ} {f : ℝ → X} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Set.Ioc a b))) :
    MemLp (reflectedIntervalExtension a b f) p volume := by
  let f₀ := intervalZeroExtension a b f
  have hf₀ : MemLp f₀ p volume := memLp_intervalZeroExtension hf
  have hleft : MemLp
      (fun t ↦ f₀ (reflectTime a t)) p volume := by
    change MemLp (f₀ ∘ reflectTime a) p volume
    exact hf₀.comp_measurePreserving
      (measurePreserving_reflectTime a)
  have hright : MemLp
      (fun t ↦ f₀ (reflectTime b t)) p volume := by
    change MemLp (f₀ ∘ reflectTime b) p volume
    exact hf₀.comp_measurePreserving
      (measurePreserving_reflectTime b)
  have hinner : MemLp
      ((Set.Ioi b).piecewise
        (fun t ↦ f₀ (reflectTime b t)) f₀) p volume :=
    MemLp.piecewise measurableSet_Ioi.nullMeasurableSet
      (hright.mono_measure Measure.restrict_le_self)
      (hf₀.mono_measure Measure.restrict_le_self)
  have hall : MemLp
      ((Set.Iio a).piecewise
        (fun t ↦ f₀ (reflectTime a t))
        ((Set.Ioi b).piecewise
          (fun t ↦ f₀ (reflectTime b t)) f₀)) p volume :=
    MemLp.piecewise measurableSet_Iio.nullMeasurableSet
      (hleft.mono_measure Measure.restrict_le_self)
      (hinner.mono_measure Measure.restrict_le_self)
  apply MemLp.ae_eq _ hall
  filter_upwards with t
  simp only [reflectedIntervalExtension, f₀, Set.piecewise,
    Set.mem_Iio, Set.mem_Ioi]

/-- Integrability is preserved by the sign-correct reflected derivative. -/
theorem integrable_reflectedDerivativeExtension
    {X : Type*} [NormedAddCommGroup X]
    {a b : ℝ} {g : ℝ → X}
    (hg : Integrable g (volume.restrict (Set.Ioc a b))) :
    Integrable (reflectedDerivativeExtension a b g) volume := by
  let g₀ := intervalZeroExtension a b g
  have hg₀ : Integrable g₀ volume := integrable_intervalZeroExtension hg
  have hleft : Integrable
      (fun t ↦ -g₀ (reflectTime a t)) volume := by
    have hcomp : Integrable (g₀ ∘ reflectTime a) volume :=
      ((measurePreserving_reflectTime a).integrable_comp
        hg₀.aestronglyMeasurable).2 hg₀
    apply hcomp.neg.congr
    filter_upwards with t
    rfl
  have hright : Integrable
      (fun t ↦ -g₀ (reflectTime b t)) volume := by
    have hcomp : Integrable (g₀ ∘ reflectTime b) volume :=
      ((measurePreserving_reflectTime b).integrable_comp
        hg₀.aestronglyMeasurable).2 hg₀
    apply hcomp.neg.congr
    filter_upwards with t
    rfl
  have hinner : Integrable
      ((Set.Ioi b).piecewise
        (fun t ↦ -g₀ (reflectTime b t)) g₀) volume :=
    Integrable.piecewise measurableSet_Ioi.nullMeasurableSet hright.integrableOn hg₀.integrableOn
  have hall : Integrable
      ((Set.Iio a).piecewise
        (fun t ↦ -g₀ (reflectTime a t))
        ((Set.Ioi b).piecewise
          (fun t ↦ -g₀ (reflectTime b t)) g₀)) volume :=
    Integrable.piecewise measurableSet_Iio.nullMeasurableSet hleft.integrableOn hinner.integrableOn
  apply hall.congr
  filter_upwards with t
  simp only [reflectedDerivativeExtension, g₀, Set.piecewise,
    Set.mem_Iio, Set.mem_Ioi]

/-- Odd reflection of a derivative preserves every Bochner `Lᵖ` class. -/
theorem memLp_reflectedDerivativeExtension
    {X : Type*} [NormedAddCommGroup X]
    {a b : ℝ} {g : ℝ → X} {p : ℝ≥0∞}
    (hg : MemLp g p (volume.restrict (Set.Ioc a b))) :
    MemLp (reflectedDerivativeExtension a b g) p volume := by
  let g₀ := intervalZeroExtension a b g
  have hg₀ : MemLp g₀ p volume := memLp_intervalZeroExtension hg
  have hleft : MemLp
      (fun t ↦ -g₀ (reflectTime a t)) p volume := by
    have hcomp : MemLp (g₀ ∘ reflectTime a) p volume :=
      hg₀.comp_measurePreserving
        (measurePreserving_reflectTime a)
    apply MemLp.ae_eq _ hcomp.neg
    filter_upwards with t
    rfl
  have hright : MemLp
      (fun t ↦ -g₀ (reflectTime b t)) p volume := by
    have hcomp : MemLp (g₀ ∘ reflectTime b) p volume :=
      hg₀.comp_measurePreserving
        (measurePreserving_reflectTime b)
    apply MemLp.ae_eq _ hcomp.neg
    filter_upwards with t
    rfl
  have hinner : MemLp
      ((Set.Ioi b).piecewise
        (fun t ↦ -g₀ (reflectTime b t)) g₀) p volume :=
    MemLp.piecewise measurableSet_Ioi.nullMeasurableSet
      (hright.mono_measure Measure.restrict_le_self)
      (hg₀.mono_measure Measure.restrict_le_self)
  have hall : MemLp
      ((Set.Iio a).piecewise
        (fun t ↦ -g₀ (reflectTime a t))
        ((Set.Ioi b).piecewise
          (fun t ↦ -g₀ (reflectTime b t)) g₀)) p volume :=
    MemLp.piecewise measurableSet_Iio.nullMeasurableSet
      (hleft.mono_measure Measure.restrict_le_self)
      (hinner.mono_measure Measure.restrict_le_self)
  apply MemLp.ae_eq _ hall
  filter_upwards with t
  simp only [reflectedDerivativeExtension, g₀, Set.piecewise,
    Set.mem_Iio, Set.mem_Ioi]

/-- Between an interior anchor and any point of the closed interval, the
reflected derivative is just the original zero extension. -/
theorem intervalIntegral_reflectedDerivativeExtension_eq_zeroExtension
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b s t : ℝ} {g : ℝ → X}
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Icc a b) :
    (∫ r in s..t, reflectedDerivativeExtension a b g r) =
      ∫ r in s..t, intervalZeroExtension a b g r := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with r
  intro hr
  have hrab : r ∈ Set.Icc a b := by
    rcases le_total s t with hst | hts
    · rw [Set.uIoc_of_le hst] at hr
      exact ⟨(hs.1.trans hr.1).le, hr.2.trans ht.2⟩
    · rw [Set.uIoc_of_ge hts] at hr
      exact ⟨ht.1.trans hr.1.le, hr.2.trans hs.2.le⟩
  simp only [reflectedDerivativeExtension,
    ite_eq_right (not_lt_of_ge hrab.1), ite_eq_right (not_lt_of_ge hrab.2)]

/-- Zero extension is invisible to interval integrals whose two endpoints
lie strictly inside the original interval.  This elementary localization
theorem is used for both the `V*` primitive and the scalar energy primitive. -/
theorem intervalIntegral_intervalZeroExtension_eq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b s t : ℝ} {f : ℝ → X}
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    (∫ r in s..t, intervalZeroExtension a b f r) = ∫ r in s..t, f r := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with r
  intro hr
  have hrab : r ∈ Set.Ioo a b := by
    rcases le_total s t with hst | hts
    · rw [Set.uIoc_of_le hst] at hr
      exact ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩
    · rw [Set.uIoc_of_ge hts] at hr
      exact ⟨ht.1.trans hr.1, hr.2.trans_lt hs.2⟩
  simp only [intervalZeroExtension, Set.indicator_of_mem
    (Set.Ioo_subset_Ioc_self hrab)]

/-- On the left reflected wing, the odd derivative integral becomes the
ordinary zero-extension integral after the substitution `r ↦ 2a-r`. -/
theorem intervalIntegral_reflectedDerivativeExtension_left
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b t : ℝ} {g : ℝ → X} (hab : a < b) (ht : t < a) :
    (∫ r in a..t, reflectedDerivativeExtension a b g r) =
      ∫ r in a..reflectTime a t,
        intervalZeroExtension a b g r := by
  let g₀ := intervalZeroExtension a b g
  have hpoint :
      (∫ r in a..t, reflectedDerivativeExtension a b g r) =
        ∫ r in a..t, -g₀ (reflectTime a r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r
    intro hr
    rw [Set.uIoc_of_ge ht.le] at hr
    by_cases hra : r < a
    · simp [reflectedDerivativeExtension, g₀, hra]
    · have hraeq : r = a := le_antisymm hr.2 (not_lt.mp hra)
      subst r
      simp [reflectedDerivativeExtension, g₀, intervalZeroExtension,
        not_lt_of_ge hab.le]
  rw [hpoint]
  calc
    (∫ r in a..t, -g₀ (reflectTime a r)) =
        -(∫ r in a..t, g₀ (reflectTime a r)) := by
          rw [← intervalIntegral.integral_neg]
    _ = -(∫ r in reflectTime a t..a, g₀ r) := by
          simp [reflectTime, two_mul,
            intervalIntegral.integral_comp_sub_left]
    _ = ∫ r in a..reflectTime a t, g₀ r := by
          exact (intervalIntegral.integral_symm
            (f := g₀) (reflectTime a t) a).symm

/-- The analogous substitution formula on the right reflected wing. -/
theorem intervalIntegral_reflectedDerivativeExtension_right
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b t : ℝ} {g : ℝ → X} (hab : a < b) (ht : b < t) :
    (∫ r in b..t, reflectedDerivativeExtension a b g r) =
      ∫ r in b..reflectTime b t,
        intervalZeroExtension a b g r := by
  let g₀ := intervalZeroExtension a b g
  have hpoint :
      (∫ r in b..t, reflectedDerivativeExtension a b g r) =
        ∫ r in b..t, -g₀ (reflectTime b r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r
    intro hr
    rw [Set.uIoc_of_le ht.le] at hr
    have hra : ¬r < a := not_lt_of_ge (hab.le.trans hr.1.le)
    simp [reflectedDerivativeExtension, g₀, hra, hr.1]
  rw [hpoint]
  calc
    (∫ r in b..t, -g₀ (reflectTime b r)) =
        -(∫ r in b..t, g₀ (reflectTime b r)) := by
          rw [← intervalIntegral.integral_neg]
    _ = -(∫ r in reflectTime b t..b, g₀ r) := by
          simp [reflectTime, two_mul,
            intervalIntegral.integral_comp_sub_left]
    _ = ∫ r in b..reflectTime b t, g₀ r := by
          exact (intervalIntegral.integral_symm
            (f := g₀) (reflectTime b t) b).symm

/-- The open interval obtained by reflecting `(a,b)` once across each
endpoint. -/
def reflectedTimeDomain (a b : ℝ) : Set ℝ :=
  Set.Ioo (2 * a - b) (2 * b - a)

end ReflectedExtension

end PDE.Analysis.Evolution
