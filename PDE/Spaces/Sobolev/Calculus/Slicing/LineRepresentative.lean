/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Canonical representatives on one-dimensional slices

Given a slice value `u` and an integrable candidate derivative `g`, we
normalize the primitive of `g` to have the same average as `u` on `[0,1]`.
The resulting curve is absolutely continuous on compact intervals and has
derivative `g` almost everywhere. If `u` already satisfies the fundamental
theorem with derivative `g`, the normalized primitive recovers `u` exactly.

This normalization is the canonical one-dimensional object used by the
arbitrary-dimensional ACL construction (`Slicing.ACL`). The
representative is a fixed formula in the data `(u, g)`, so no choice is made
on each line, and it depends on `(u, g)` in a Lipschitz way with respect
to whole-line `L¹` norms, which lets `L¹` approximation results pass to the
representatives pointwise.

## Main results

* `lineRepresentative u g`: `∫₀¹ u + ∫₀ᵗ g - ∫₀¹ (∫₀ʳ g) dr`, the primitive of
  `g` normalized to have the same mean as `u` on `[0, 1]`.
* `absolutelyContinuousOnInterval_lineRepresentative`,
  `ae_hasDerivAt_lineRepresentative`: for integrable `g`, the representative
  is absolutely continuous on compact intervals with derivative `g` almost
  everywhere (the Lebesgue differentiation theorem, Mathlib's
  `LocallyIntegrable.ae_hasDerivAt_integral`).
* `lineRepresentative_eq`: if `u` satisfies `∫_a^b g = u b - u a` for all
  `a, b`, then `lineRepresentative u g = u`.
* `abs_lineRepresentative_sub_le`: the pointwise estimate
  `|L(u,g)(t) - L(v,h)(t)| ≤ ‖u - v‖₁ + 2 ‖g - h‖₁`.
* `tendsto_lineRepresentative_of_integral_abs_tendsto_zero`,
  `ae_eq_lineRepresentative_of_integral_abs_tendsto_zero`: `L¹` convergence
  of `(u_m, g_m)` gives pointwise convergence of the representatives, and if
  each approximant is its own representative then the limit representative
  equals the limit almost everywhere.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for the Lebesgue differentiation theorem.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Slices

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The primitive of `g`, normalized to have the same average on `[0,1]`
as `u`. -/
def lineRepresentative (u g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, u r) +
    (∫ s in (0 : ℝ)..t, g s) -
      ∫ r in (0 : ℝ)..1, (∫ s in (0 : ℝ)..r, g s)

/-- The normalized primitive is absolutely continuous on every compact
interval. -/
theorem absolutelyContinuousOnInterval_lineRepresentative
    {u g : ℝ → ℝ} (hg : Integrable g volume)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval (lineRepresentative u g) a b := by
  have hconst (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hprim : AbsolutelyContinuousOnInterval (fun t ↦ ∫ s in (0 : ℝ)..t, g s) a b :=
    ((hconst _).add (hg.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      Set.left_mem_uIcc)).congr fun t _ ↦
        intervalIntegral.integral_add_adjacent_intervals hg.intervalIntegrable hg.intervalIntegrable
  change AbsolutelyContinuousOnInterval ((fun _ : ℝ ↦ ∫ r in (0 : ℝ)..1, u r) +
    (fun t ↦ ∫ s in (0 : ℝ)..t, g s) - fun _ : ℝ ↦ ∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..r, g s) a b
  exact ((hconst _).add hprim).sub (hconst _)

/-- The derivative of the normalized primitive is `g` almost everywhere. -/
theorem ae_hasDerivAt_lineRepresentative
    {u g : ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ t ∂volume, HasDerivAt (lineRepresentative u g) (g t) t := by
  filter_upwards
    [LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable]
      with t ht
  have hleft :
      HasDerivAt
        (fun _ : ℝ ↦ ∫ r in (0 : ℝ)..1, u r) 0 t :=
    hasDerivAt_const t _
  have hright :
      HasDerivAt
        (fun _ : ℝ ↦
          ∫ r in (0 : ℝ)..1, (∫ s in (0 : ℝ)..r, g s)) 0 t :=
    hasDerivAt_const t _
  change HasDerivAt
    ((fun _ : ℝ ↦ ∫ r in (0 : ℝ)..1, u r) +
      (fun x ↦ ∫ s in (0 : ℝ)..x, g s) -
      (fun _ : ℝ ↦
        ∫ r in (0 : ℝ)..1, (∫ s in (0 : ℝ)..r, g s)))
    (g t) t
  simpa only [zero_add, sub_zero] using (hleft.add (ht 0)).sub hright

/-- A function satisfying the fundamental theorem with derivative `g` is
exactly its normalized primitive. -/
theorem lineRepresentative_eq
    {u g : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1)
    (hFTC : ∀ a b : ℝ, (∫ s in a..b, g s) = u b - u a) :
    lineRepresentative u g = u := by
  funext t
  have hinner :
      (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, g s) =
        fun r ↦ u r - u 0 := by
    funext r
    exact hFTC 0 r
  rw [lineRepresentative, hFTC 0 t, hinner]
  have hsub :
      (∫ r in (0 : ℝ)..1, (u r - u 0)) =
        (∫ r in (0 : ℝ)..1, u r) - u 0 := by
    rw [intervalIntegral.integral_sub hu
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ ↦ u 0) volume 0 1)]
    simp
  rw [hsub]
  ring

/-- An interval integral is bounded by the whole-line integral of the
absolute value. -/
theorem abs_intervalIntegral_le_integral_abs
    {f : ℝ → ℝ} (hf : Integrable f volume) (a b : ℝ) :
    |∫ x in a..b, f x| ≤ ∫ x, |f x| := by
  calc
    |∫ x in a..b, f x| = ‖∫ x in a..b, f x‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ x in Set.uIoc a b, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ x, ‖f x‖ :=
      setIntegral_le_integral hf.norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
    _ = ∫ x, |f x| := by simp only [Real.norm_eq_abs]

/-- The normalized representative is Lipschitz with respect to the
whole-line `L¹` errors of its value and derivative data. -/
theorem abs_lineRepresentative_sub_le
    {u v g h : ℝ → ℝ}
    (hu : Integrable u volume) (hv : Integrable v volume)
    (hg : Integrable g volume) (hh : Integrable h volume)
    (t : ℝ) :
    |lineRepresentative u g t - lineRepresentative v h t| ≤
      (∫ x, |u x - v x|) + 2 * ∫ x, |g x - h x| := by
  have hdiff (a b : ℝ) {f₁ f₂ : ℝ → ℝ} (h₁ : Integrable f₁ volume) (h₂ : Integrable f₂ volume) :
      |(∫ r in a..b, f₁ r) - ∫ r in a..b, f₂ r| ≤ ∫ x, |f₁ x - f₂ x| := by
    rw [← intervalIntegral.integral_sub h₁.intervalIntegrable h₂.intervalIntegrable]
    exact abs_intervalIntegral_le_integral_abs (h₁.sub h₂) a b
  have hprim {f : ℝ → ℝ} (hf : Integrable f volume) :
      IntervalIntegrable (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, f s) volume 0 1 :=
    (hf.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      Set.left_mem_uIcc).continuousOn.intervalIntegrable
  have hdouble : |(∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..r, g s) -
      ∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..r, h s| ≤ ∫ x, |g x - h x| := by
    rw [← intervalIntegral.integral_sub (hprim hg) (hprim hh)]
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0)
      (b := 1) (C := ∫ x, |g x - h x|) fun r _ ↦ (Real.norm_eq_abs _).trans_le (hdiff 0 r hg hh)
  obtain ⟨h₁, h₂⟩ := abs_le.1 (hdiff 0 1 hu hv)
  obtain ⟨h₃, h₄⟩ := abs_le.1 (hdiff 0 t hg hh)
  obtain ⟨h₅, h₆⟩ := abs_le.1 hdouble
  simp only [lineRepresentative, abs_le]
  constructor <;> linarith

/-- Whole-line `L¹` convergence of values and derivatives gives pointwise
convergence of their normalized representatives. -/
theorem tendsto_lineRepresentative_of_integral_abs_tendsto_zero
    {u g : ℝ → ℝ} {u_m g_m : ℕ → ℝ → ℝ}
    (hu : Integrable u volume) (hg : Integrable g volume)
    (hu_m : ∀ m, Integrable (u_m m) volume)
    (hg_m : ∀ m, Integrable (g_m m) volume)
    (huconv : Tendsto (fun m ↦ ∫ x, |u_m m x - u x|)
      atTop (𝓝 0))
    (hgconv : Tendsto (fun m ↦ ∫ x, |g_m m x - g x|)
      atTop (𝓝 0)) :
    ∀ t, Tendsto (fun m ↦ lineRepresentative (u_m m) (g_m m) t)
      atTop (𝓝 (lineRepresentative u g t)) := by
  intro t
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
    (by simpa using huconv.add (hgconv.const_mul 2))
  simpa [Real.norm_eq_abs] using abs_lineRepresentative_sub_le (hu_m m) hu (hg_m m) hg t

/-- If `L¹`-convergent value/derivative approximants equal their normalized
representatives, then the limiting normalized representative equals the
limiting value almost everywhere. -/
theorem ae_eq_lineRepresentative_of_integral_abs_tendsto_zero
    {u g : ℝ → ℝ} {u_m g_m : ℕ → ℝ → ℝ}
    (hu : Integrable u volume) (hg : Integrable g volume)
    (hu_m : ∀ m, Integrable (u_m m) volume)
    (hg_m : ∀ m, Integrable (g_m m) volume)
    (huconv : Tendsto (fun m ↦ ∫ x, |u_m m x - u x|)
      atTop (𝓝 0))
    (hgconv : Tendsto (fun m ↦ ∫ x, |g_m m x - g x|)
      atTop (𝓝 0))
    (hrep : ∀ m, lineRepresentative (u_m m) (g_m m) = u_m m) :
    lineRepresentative u g =ᵐ[volume] u := by
  have hLp : Tendsto (fun m ↦ eLpNorm (u_m m - u) 1 volume) atTop (𝓝 0) := by
    convert (ENNReal.continuous_ofReal.tendsto 0).comp huconv using 1
    · funext m
      rw [Function.comp_apply,
        eLpNorm_one_eq_lintegral_enorm ((hu_m m).sub hu).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hu_m m).sub hu)]
      simp [Real.norm_eq_abs]
    · simp
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp).exists_seq_tendsto_ae
  filter_upwards [hae] with t ht
  have hrep' (m : ℕ) : lineRepresentative (u_m m) (g_m m) t = u_m m t := congrFun (hrep m) t
  refine tendsto_nhds_unique ?_ ht
  simpa only [Function.comp_def, hrep'] using
    (tendsto_lineRepresentative_of_integral_abs_tendsto_zero hu hg hu_m hg_m huconv hgconv
      t).comp hns.tendsto_atTop

end SobolevSpace.Slices
