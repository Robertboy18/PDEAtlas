/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.IntervalCauchy
public import PDE.Parabolic.MaximumPrinciple.FactoredOperator
import CAS.ExactTactic

/-!
# Supremum bounds for the interval heat series

The compact-cylinder maximum principle controls a classical heat solution by its
initial and lateral boundary values. Applied to the convergent sine series and its
negative, this gives the supremum estimate used to approximate continuous data.
-/

@[expose] public section

namespace HeatEquation

open Set ParabolicMaximum PDE.Analysis.Fourier.SineSeries
open scoped ContDiff

/-- A positive-time spatial slice of the heat series is `C²`. -/
theorem contDiff_intervalHeatSeries_space {a : ℕ → ℝ} {C t : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C) (ht : 0 < t) :
    ContDiff ℝ 2 (intervalHeatSeries a t) := by
  have hd : deriv (intervalHeatSeries a t) = intervalHeatSeriesDx a t :=
    funext fun x ↦ (hasDerivAt_intervalHeatSeries_space ha ht x).deriv
  have hdd : deriv (intervalHeatSeriesDx a t) = intervalHeatSeriesDt a t :=
    funext fun x ↦ (hasDerivAt_intervalHeatSeriesDx_space ha ht x).deriv
  have hc := (continuousOn_intervalHeatSeriesDt ha).comp_continuous
    (f := fun x : ℝ ↦ (t, x)) (continuous_const.prodMk continuous_id) (fun _ ↦ ht)
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_intervalHeatSeries_space ha ht x).differentiableAt,
    by simp, ?_⟩
  rw [hd, contDiff_one_iff_deriv, hdd]
  refine ⟨fun x ↦ (hasDerivAt_intervalHeatSeriesDx_space ha ht x).differentiableAt, ?_⟩
  exact hc

/-- The scalar heat equation obeys the maximum principle on the unit interval.
Only the initial and lateral faces contribute to the bound. -/
theorem interval_heat_le {u : ℝ → ℝ → ℝ} {M T : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2) {p | 0 ≤ p.1})
    (hs : ∀ t, 0 < t → ContDiff ℝ 2 (u t))
    (htime : ∀ t, 0 < t → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hheat : ∀ t, 0 < t → ∀ x, deriv (fun s ↦ u s x) t = deriv (deriv (u t)) x)
    (hi : ∀ x ∈ Icc 0 1, u 0 x ≤ M)
    (hb : ∀ t, 0 ≤ t → u t 0 ≤ M ∧ u t 1 ≤ M)
    (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 1) :
    u T x ≤ M := by
  let P : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
    fun v y t ↦ deriv (v y) t - deriv (deriv (fun z ↦ v z t)) y
  have hstrict (v : ℝ → ℝ → ℝ)
      (hvc : ContinuousOn (fun p : ℝ × ℝ ↦ v p.1 p.2) (closedCylinder (Ioo 0 1) T))
      (hvs : ∀ y ∈ Ioo 0 1, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun z ↦ v z t) y)
      (hvt : ∀ y ∈ Ioo 0 1, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (v y) t)
      (hvp : ∀ y ∈ Ioo 0 1, ∀ t ∈ Ioc 0 T, P v y t < 0)
      (hvb : ∀ p ∈ parabolicBoundary (Ioo 0 1) T, v p.1 p.2 ≤ M) :
      ∀ p ∈ closedCylinder (Ioo 0 1) T, v p.1 p.2 ≤ M := by
    apply strict_maximum_core isOpen_Ioo (nonempty_Ioo.mpr zero_lt_one)
      (by simpa only [closure_Ioo zero_ne_one] using
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))) hT P v hvc ?_ hvp hvb
    intro y hy t ht hmax hmaxt _
    exact sub_nonneg.mpr ((hmax.deriv_deriv_nonpos (hvs y hy t ht).continuousAt).trans
      (hmaxt.deriv_nonneg_of_left_lt ht.1 ht.2 (hvt y hy t ht)))
  have hglobal := subsolution_le_of_strict_perturbation hT P hstrict
    (fun y t ↦ u t y) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hglobal (x, T) ⟨by simpa only [closure_Ioo zero_ne_one] using hx,
      hT.le, le_rfl⟩
  · exact hc.comp (continuous_snd.prodMk continuous_fst).continuousOn fun p hp ↦ hp.2.1
  · intro y _ t ht
    exact (hs t ht.1).contDiffAt
  · intro y _ t ht
    exact htime t ht.1 y
  · intro ε _ y _ t ht
    have he : HasDerivAt (fun s : ℝ ↦ ε * s) ε t := by cas
    dsimp only [P]
    rw [((htime t ht.1 y).hasDerivAt.fun_sub he).deriv, deriv_sub_const_fun]
    exact le_of_eq (by ring)
  · intro y _ t ht
    exact sub_nonpos.mpr (hheat t ht.1 y).le
  · intro p hp
    rcases hp with hp | hp
    · have hpx : p.1 = 0 ∨ p.1 = 1 := by
        simpa only [frontier_Ioo zero_lt_one, mem_insert_iff, mem_singleton_iff] using hp.1
      rcases hpx with hpx | hpx
      · simpa only [hpx] using (hb p.2 hp.2.1).1
      · simpa only [hpx] using (hb p.2 hp.2.1).2
    · have hpt : p.2 = 0 := hp.2
      rw [hpt]
      exact hi p.1 (by simpa only [closure_Ioo zero_ne_one] using hp.1)

/-- The supremum of a classical interval heat solution is bounded by the initial
supremum when both boundary values vanish. -/
theorem norm_interval_heat_le {u : ℝ → ℝ → ℝ} {M T : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2) {p | 0 ≤ p.1})
    (hs : ∀ t, 0 < t → ContDiff ℝ 2 (u t))
    (htime : ∀ t, 0 < t → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hheat : ∀ t, 0 < t → ∀ x, deriv (fun s ↦ u s x) t = deriv (deriv (u t)) x)
    (hM : 0 ≤ M) (hi : ∀ x ∈ Icc 0 1, ‖u 0 x‖ ≤ M)
    (hb : ∀ t, 0 ≤ t → u t 0 = 0 ∧ u t 1 = 0)
    (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 1) :
    ‖u T x‖ ≤ M := by
  rw [Real.norm_eq_abs, abs_le]
  have hu := interval_heat_le hc hs htime hheat
    (fun y hy ↦ (le_abs_self _).trans (hi y hy))
    (fun t ht ↦ by simpa only [(hb t ht).1, (hb t ht).2] using And.intro hM hM) hT hx
  have hn := interval_heat_le (u := fun t y ↦ -u t y) hc.neg
    (fun t ht ↦ (hs t ht).neg) (fun t ht y ↦ (htime t ht y).neg)
    (fun t ht y ↦ by
      simpa only [deriv.fun_neg', deriv.fun_neg] using congrArg Neg.neg (hheat t ht y))
    (fun y hy ↦ (neg_le_abs _).trans (hi y hy))
    (fun t ht ↦ by simpa only [(hb t ht).1, (hb t ht).2, neg_zero] using And.intro hM hM)
    hT hx
  exact ⟨by linarith, hu⟩

/-- The heat series for interval `C²` Dirichlet data is bounded by any nonnegative
uniform bound for the initial data. -/
theorem norm_intervalHeatSeries_le_of_contDiffOn {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0)
    {M t x : ℝ} (hM : 0 ≤ M) (hbound : ∀ y ∈ Icc 0 1, ‖g y‖ ≤ M)
    (ht : 0 < t) (hx : x ∈ Icc 0 1) :
    ‖intervalHeatSeries (intervalCoefficient g) t x‖ ≤ M := by
  have ha := summable_norm_intervalCoefficient hg hzero hone
  have hb : ∀ n, ‖intervalCoefficient g n‖ ≤ ∑' i, ‖intervalCoefficient g i‖ :=
    fun n ↦ ha.le_tsum n (fun _ _ ↦ norm_nonneg _)
  apply norm_interval_heat_le (continuousOn_intervalHeatSeries_of_summable ha)
    (fun _ ht ↦ contDiff_intervalHeatSeries_space hb ht)
    (fun _ ht x ↦ (hasDerivAt_intervalHeatSeries_time hb ht x).differentiableAt)
    (fun _ ht x ↦ intervalHeatSeries_heat_equation hb ht x) hM ?_
    (fun t _ ↦ ⟨intervalHeatSeries_left_boundary _ t, intervalHeatSeries_right_boundary _ t⟩)
    ht hx
  intro y hy
  have he : intervalHeatSeries (intervalCoefficient g) 0 y = g y := by
    simpa only [intervalHeatSeries, intervalHeatMode_initial_trace] using
      (hasSum_intervalCoefficient_sineMode hg hzero hone hy).tsum_eq
  rw [he]
  exact hbound y hy

end HeatEquation
