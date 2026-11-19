/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.Norm.Trajectory
public import Mathlib.Analysis.Calculus.Deriv.Basic
import CAS.ExactTactic

/-!
# Finite-time obstruction from quadratic differential growth

The scalar comparison mechanism behind many PDE blow-up arguments: if a
positive classical observable satisfies

`a * y(t)^2 ≤ y'(t)` with `a > 0`,

then its reciprocal decreases at least linearly. Consequently the trajectory cannot remain finite
through the Riccati horizon `t₀ + (a * y(t₀))⁻¹`.

This is the scalar step in Kaplan-type eigenfunction arguments and related moment methods
(Kaplan; Quittner and Souplet).

In the proof of Evans, §9.4.1, Theorem 1, the first-eigenfunction moment `η = ∫ u w₁` of a
solution of `u_t - Δu = u²` satisfies `η' ≥ -λ₁ η + η²`, (5), and the change of variables
`ξ = e^{λ₁ t} η` removes the linear term, leaving `ξ' ≥ e^{-λ₁ t} ξ²`. The inequality here is
the autonomous case. The function `y` is an arbitrary real function; a model-specific theorem
derives the differential inequality from the equation, the boundary conditions, and an
observable.

## References

* S. Kaplan, "On the growth of solutions of quasi-linear parabolic equations",
  *Comm. Pure Appl. Math.* 16 (1963), 305-330.
  <https://doi.org/10.1002/cpa.3160160307>
* P. Quittner and P. Souplet, *Superlinear Parabolic Problems*, 2nd ed., Birkhäuser Advanced
  Texts, Birkhäuser, 2019, chapter "Model Parabolic Problems", pp. 85-325.
  <https://doi.org/10.1007/978-3-030-18222-9_2>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, proof of Theorem 1, (4)-(5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set

namespace PDE.Solution.Singularity.FiniteTime.QuadraticGrowth

/-- A trajectory with nonnegative quadratic differential growth is monotone on its interval.

Indeed, `0 ≤ a` makes the lower bound `a * y²` nonnegative, so the derivative criterion for
monotonicity applies directly. -/
theorem monotoneOn_of_mul_sq_le_deriv {y : ℝ → ℝ} {a t₀ T : ℝ}
    (ha : 0 ≤ a) (hy_cont : ContinuousOn y (Icc t₀ T))
    (hy_diff : DifferentiableOn ℝ y (Ioo t₀ T))
    (hy_deriv : ∀ t ∈ Ioo t₀ T, a * y t ^ 2 ≤ deriv y t) :
    MonotoneOn y (Icc t₀ T) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ T) hy_cont
  · simpa only [interior_Icc] using hy_diff
  · intro t ht
    rw [interior_Icc] at ht
    exact (mul_nonneg ha (sq_nonneg (y t))).trans (hy_deriv t ht)

/-- A positive initial value stays positive at every later point of the interval.

Membership of the evaluation point in `[t₀, T]` already implies that the interval is nonempty,
so no separate hypothesis `t₀ ≤ T` is needed. -/
theorem pos_of_mem_Icc_of_mul_sq_le_deriv {y : ℝ → ℝ} {a t₀ T : ℝ}
    (ha : 0 ≤ a) (hy₀ : 0 < y t₀)
    (hy_cont : ContinuousOn y (Icc t₀ T))
    (hy_diff : DifferentiableOn ℝ y (Ioo t₀ T))
    (hy_deriv : ∀ t ∈ Ioo t₀ T, a * y t ^ 2 ≤ deriv y t)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    0 < y t := by
  have ht₀T : t₀ ≤ T := ht.1.trans ht.2
  have hy_mono := monotoneOn_of_mul_sq_le_deriv ha hy_cont hy_diff hy_deriv
  exact hy₀.trans_le (hy_mono (left_mem_Icc.mpr ht₀T) ht ht.1)

/-- A positive trajectory satisfying `a * y² ≤ y'` obeys the sharp reciprocal estimate

`y(t)⁻¹ ≤ y(t₀)⁻¹ - a * (t - t₀)`.

The estimate remains valid for `a = 0`. Positivity is derived from monotonicity, rather than
carried as a separate hypothesis. -/
theorem inv_le_initial_inv_sub {y : ℝ → ℝ} {a t₀ T : ℝ}
    (ha : 0 ≤ a) (hy₀ : 0 < y t₀)
    (hy_cont : ContinuousOn y (Icc t₀ T))
    (hy_diff : DifferentiableOn ℝ y (Ioo t₀ T))
    (hy_deriv : ∀ t ∈ Ioo t₀ T, a * y t ^ 2 ≤ deriv y t)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    (y t)⁻¹ ≤ (y t₀)⁻¹ - a * (t - t₀) := by
  have hy_pos : ∀ s ∈ Icc t₀ T, 0 < y s := by
    intro s hs
    exact pos_of_mem_Icc_of_mul_sq_le_deriv ha hy₀ hy_cont hy_diff hy_deriv hs
  have hinv_cont : ContinuousOn (fun t ↦ (y t)⁻¹) (Icc t₀ T) :=
    hy_cont.inv₀ fun t ht ↦ (hy_pos t ht).ne'
  have hinv_diff : DifferentiableOn ℝ (fun t ↦ (y t)⁻¹) (interior (Icc t₀ T)) := by
    rw [interior_Icc]
    exact hy_diff.inv fun t ht ↦ (hy_pos t (Ioo_subset_Icc_self ht)).ne'
  have hinv_deriv : ∀ t ∈ interior (Icc t₀ T),
      deriv (fun s ↦ (y s)⁻¹) t ≤ -a := by
    intro t ht
    rw [interior_Icc] at ht
    have hyt_diff : DifferentiableAt ℝ y t :=
      (hy_diff t ht).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    rw [deriv_fun_inv'' hyt_diff (hy_pos t (Ioo_subset_Icc_self ht)).ne']
    apply (div_le_iff₀ (sq_pos_of_pos (hy_pos t (Ioo_subset_Icc_self ht)))).2
    simpa only [neg_mul] using neg_le_neg (hy_deriv t ht)
  have ht₀T : t₀ ≤ T := ht.1.trans ht.2
  have hbound :=
    (convex_Icc t₀ T).image_sub_le_mul_sub_of_deriv_le
      hinv_cont hinv_diff hinv_deriv t₀ (left_mem_Icc.mpr ht₀T) t ht ht.1
  linarith

/-- A positive trajectory satisfying `a * y² ≤ y'` tends to `+∞` from below at the Riccati
horizon `τ = t₀ + (a * y(t₀))⁻¹`.

Lean functions `y : ℝ → ℝ` are total, so `y` is still defined at and after `τ`. The hypotheses
impose continuity only on `[t₀, τ)` and differentiability and quadratic growth only on
`(t₀, τ)`, so the values of `y` from `τ` on play no role. The proof applies
`inv_le_initial_inv_sub` on each compact interval `[t₀, t]` and compares `y(t)` with
`(a * (τ - t))⁻¹`. -/
theorem tendsto_atTop_riccati_horizon {y : ℝ → ℝ} {a t₀ : ℝ}
    (ha : 0 < a) (hy₀ : 0 < y t₀)
    (hy_cont : ContinuousOn y (Ico t₀ (t₀ + (a * y t₀)⁻¹)))
    (hy_diff : DifferentiableOn ℝ y (Ioo t₀ (t₀ + (a * y t₀)⁻¹)))
    (hy_deriv : ∀ t ∈ Ioo t₀ (t₀ + (a * y t₀)⁻¹),
      a * y t ^ 2 ≤ deriv y t) :
    Filter.Tendsto y
      (nhdsWithin (t₀ + (a * y t₀)⁻¹) (Iio (t₀ + (a * y t₀)⁻¹)))
      Filter.atTop := by
  let τ := t₀ + (a * y t₀)⁻¹
  change ContinuousOn y (Ico t₀ τ) at hy_cont
  change DifferentiableOn ℝ y (Ioo t₀ τ) at hy_diff
  change (∀ t ∈ Ioo t₀ τ, a * y t ^ 2 ≤ deriv y t) at hy_deriv
  change Filter.Tendsto y (nhdsWithin τ (Iio τ)) Filter.atTop
  have ha_y₀ : 0 < a * y t₀ := mul_pos ha hy₀
  have ht₀τ : t₀ < τ := by
    dsimp [τ]
    exact lt_add_of_pos_right t₀ (inv_pos.mpr ha_y₀)
  have hcomparison : ∀ t ∈ Ico t₀ τ, (a * (τ - t))⁻¹ ≤ y t := by
    intro t ht
    have hIcc_sub : Icc t₀ t ⊆ Ico t₀ τ := by
      intro s hs
      exact ⟨hs.1, hs.2.trans_lt ht.2⟩
    have hIoo_sub : Ioo t₀ t ⊆ Ioo t₀ τ := by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hy_cont_t : ContinuousOn y (Icc t₀ t) := hy_cont.mono hIcc_sub
    have hy_diff_t : DifferentiableOn ℝ y (Ioo t₀ t) := hy_diff.mono hIoo_sub
    have hy_deriv_t : ∀ s ∈ Ioo t₀ t, a * y s ^ 2 ≤ deriv y s := by
      intro s hs
      exact hy_deriv s (hIoo_sub hs)
    have ht_mem : t ∈ Icc t₀ t := right_mem_Icc.mpr ht.1
    have hbound :=
      inv_le_initial_inv_sub ha.le hy₀ hy_cont_t hy_diff_t hy_deriv_t ht_mem
    have hyt_pos :=
      pos_of_mem_Icc_of_mul_sq_le_deriv
        ha.le hy₀ hy_cont_t hy_diff_t hy_deriv_t ht_mem
    have hright : (y t₀)⁻¹ - a * (t - t₀) = a * (τ - t) := by
      dsimp [τ]
      cas
    rw [hright] at hbound
    exact (inv_le_comm₀ (mul_pos ha (sub_pos.mpr ht.2)) hyt_pos).2 hbound
  have hden_tendsto :
      Filter.Tendsto (fun t ↦ a * (τ - t))
        (nhdsWithin τ (Iio τ)) (nhdsWithin 0 (Ioi 0)) := by
    have hnhds :
        Filter.Tendsto (fun t ↦ a * (τ - t))
          (nhdsWithin τ (Iio τ)) (nhds 0) := by
      have hcont : ContinuousAt (fun t : ℝ ↦ a * (τ - t)) τ :=
        continuousAt_const.mul (continuousAt_const.sub continuousAt_id)
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hpos :
        ∀ᶠ t in nhdsWithin τ (Iio τ), a * (τ - t) ∈ Ioi (0 : ℝ) := by
      exact eventually_nhdsWithin_of_forall fun t ht ↦
        mul_pos ha (sub_pos.mpr ht)
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hnhds hpos
  have hlower :
      Filter.Tendsto (fun t ↦ (a * (τ - t))⁻¹)
        (nhdsWithin τ (Iio τ)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp hden_tendsto
  have hIco : ∀ᶠ t in nhdsWithin τ (Iio τ), t ∈ Ico t₀ τ :=
    Ico_mem_nhdsLT ht₀τ
  exact Filter.tendsto_atTop_mono'
    (nhdsWithin τ (Iio τ)) (hIco.mono hcomparison) hlower

/-- Quadratic differential growth forces norm blow-up at the sharp Riccati horizon.

This is the form PDE moment arguments use: once the PDE gives the scalar differential
inequality, no separate step from order divergence to norm divergence is needed. -/
theorem norm_blows_up_at_riccati_horizon {y : ℝ → ℝ} {a t₀ : ℝ}
    (ha : 0 < a) (hy₀ : 0 < y t₀)
    (hy_cont : ContinuousOn y (Ico t₀ (t₀ + (a * y t₀)⁻¹)))
    (hy_diff : DifferentiableOn ℝ y (Ioo t₀ (t₀ + (a * y t₀)⁻¹)))
    (hy_deriv : ∀ t ∈ Ioo t₀ (t₀ + (a * y t₀)⁻¹),
      a * y t ^ 2 ≤ deriv y t) :
    NormBlowsUpAt y (t₀ + (a * y t₀)⁻¹) :=
  NormBlowsUpAt.of_tendsto_atTop <|
    tendsto_atTop_riccati_horizon ha hy₀ hy_cont hy_diff hy_deriv

/-- The right endpoint of an interval carrying positive quadratic growth lies before the
Riccati horizon:

`T < t₀ + (a * y(t₀))⁻¹`.

At the proposed horizon the reciprocal estimate has a nonpositive right-hand side, contradicting
the positivity of `y`. Here `T` is only the right endpoint of the supplied interval; no maximal
existence or terminal-time interpretation is assumed. If `T < t₀`, the conclusion follows
directly. -/
theorem right_endpoint_lt_riccati_horizon {y : ℝ → ℝ} {a t₀ T : ℝ}
    (ha : 0 < a) (hy₀ : 0 < y t₀)
    (hy_cont : ContinuousOn y (Icc t₀ T))
    (hy_diff : DifferentiableOn ℝ y (Ioo t₀ T))
    (hy_deriv : ∀ t ∈ Ioo t₀ T, a * y t ^ 2 ≤ deriv y t) :
    T < t₀ + (a * y t₀)⁻¹ := by
  by_cases ht₀T : t₀ ≤ T
  · by_contra hT
    let τ := t₀ + (a * y t₀)⁻¹
    have ha_y₀ : 0 < a * y t₀ := mul_pos ha hy₀
    have hτ_mem : τ ∈ Icc t₀ T := by
      constructor
      · exact le_add_of_nonneg_right (inv_nonneg.mpr ha_y₀.le)
      · exact le_of_not_gt hT
    have hbound :=
      inv_le_initial_inv_sub ha.le hy₀ hy_cont hy_diff hy_deriv hτ_mem
    have hy_pos :=
      pos_of_mem_Icc_of_mul_sq_le_deriv ha.le hy₀ hy_cont hy_diff hy_deriv hτ_mem
    have hzero : (y t₀)⁻¹ - a * (τ - t₀) = 0 := by
      dsimp [τ]
      cas
    rw [hzero] at hbound
    exact (not_lt_of_ge hbound) (inv_pos.mpr hy_pos)
  · exact (lt_of_not_ge ht₀T).trans
      (lt_add_of_pos_right t₀ (inv_pos.mpr (mul_pos ha hy₀)))

end PDE.Solution.Singularity.FiniteTime.QuadraticGrowth
