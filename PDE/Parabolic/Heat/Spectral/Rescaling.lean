/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.Regularity
import CAS.ExactTactic

/-!
# Heat-series rescaling to a finite interval

For `a < b`, the changes of variables `y = (x - a) / (b - a)` and
`s = t / (b - a)²` transport the unit-interval series and its derivatives.
The resulting frequencies are `(n + 1)π / (b - a)`. Bounded coefficients suffice
for convergence and classical positive-time regularity; initial data are treated
in `Spectral.FiniteInterval`.
-/

@[expose] public section

namespace HeatEquation

open PDE.Representations Set

/-- The positive Dirichlet frequencies of an interval of length `b - a`. -/
noncomputable def finiteIntervalFrequency (a b : ℝ) (n : ℕ) : ℝ :=
  (n.succ : ℝ) * Real.pi / (b - a)

/-- A separated heat mode on the interval with endpoints `a` and `b`. -/
noncomputable def finiteIntervalHeatMode (a b : ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  Real.sin (finiteIntervalFrequency a b n * (x - a)) *
    Real.exp (-(finiteIntervalFrequency a b n) ^ 2 * t)

/-- The unit-interval heat series transported by parabolic scaling. -/
noncomputable def finiteIntervalHeatSeries (a b : ℝ) (c : ℕ → ℝ) (t x : ℝ) : ℝ :=
  intervalHeatSeries c (t / (b - a) ^ 2) ((x - a) / (b - a))

/-- The transported first spatial derivative series. -/
noncomputable def finiteIntervalHeatSeriesDx (a b : ℝ) (c : ℕ → ℝ) (t x : ℝ) : ℝ :=
  intervalHeatSeriesDx c (t / (b - a) ^ 2) ((x - a) / (b - a)) / (b - a)

/-- The transported time and second spatial derivative series. -/
noncomputable def finiteIntervalHeatSeriesDt (a b : ℝ) (c : ℕ → ℝ) (t x : ℝ) : ℝ :=
  intervalHeatSeriesDt c (t / (b - a) ^ 2) ((x - a) / (b - a)) / (b - a) ^ 2

/-- The explicit interval mode is exactly the parabolically rescaled unit mode. -/
theorem finiteIntervalHeatMode_eq (a b : ℝ) (n : ℕ) (t x : ℝ) :
    finiteIntervalHeatMode a b n t x =
      intervalHeatMode n (t / (b - a) ^ 2) ((x - a) / (b - a)) := by
  unfold finiteIntervalHeatMode finiteIntervalFrequency intervalHeatMode
    intervalHeatTimeMode intervalDirichletSineMode intervalDirichletEigenvalue
  cas

variable {a b : ℝ} {c : ℕ → ℝ} {C : ℝ}

/-- The scaled solution is the convergent series with the interval's own eigenfrequencies. -/
theorem hasSum_finiteIntervalHeatSeries (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n ↦ c n * finiteIntervalHeatMode a b n t x)
      (finiteIntervalHeatSeries a b c t x) := by
  simp_rw [finiteIntervalHeatMode_eq]
  exact (summable_intervalHeatSeries hc (div_pos ht (sq_pos_of_pos (sub_pos.mpr hab)))
    ((x - a) / (b - a))).hasSum

/-- The first spatial derivative series has the differentiated interval frequencies. -/
theorem hasSum_finiteIntervalHeatSeriesDx (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n ↦ c n * (finiteIntervalFrequency a b n *
      Real.cos (finiteIntervalFrequency a b n * (x - a)) *
        Real.exp (-(finiteIntervalFrequency a b n) ^ 2 * t)))
      (finiteIntervalHeatSeriesDx a b c t x) := by
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have h := (summable_intervalHeatSeriesDx hc
    (div_pos ht (sq_pos_of_pos (sub_pos.mpr hab))) ((x - a) / (b - a))).hasSum.div_const (b - a)
  apply h.congr_fun
  intro n
  rw [intervalDirichletSineMode_deriv]
  unfold finiteIntervalFrequency intervalHeatTimeMode intervalDirichletEigenvalue
  cas using hL

/-- The time derivative and second spatial derivative have multiplier minus the
square of the interval frequency in their convergent series. -/
theorem hasSum_finiteIntervalHeatSeriesDt (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n ↦ c n * (-(finiteIntervalFrequency a b n) ^ 2 *
      finiteIntervalHeatMode a b n t x)) (finiteIntervalHeatSeriesDt a b c t x) := by
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have h := (summable_intervalHeatSeriesDt hc
    (div_pos ht (sq_pos_of_pos (sub_pos.mpr hab))) ((x - a) / (b - a))).hasSum.div_const
      ((b - a) ^ 2)
  apply h.congr_fun
  intro n
  rw [finiteIntervalHeatMode_eq]
  unfold finiteIntervalFrequency intervalDirichletEigenvalue intervalHeatMode
    intervalHeatTimeMode intervalDirichletSineMode
  cas using hL

/-- Finite sums converge uniformly on every positive-time strip after rescaling. -/
theorem tendstoUniformlyOn_finiteIntervalHeatSeries (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) ↦
        ∑ n ∈ Finset.range N, c n * finiteIntervalHeatMode a b n p.1 p.2)
      (fun p ↦ finiteIntervalHeatSeries a b c p.1 p.2) Filter.atTop {p | τ ≤ p.1} := by
  simp_rw [finiteIntervalHeatMode_eq]
  apply ((tendstoUniformlyOn_intervalHeatSeries hc
    (div_pos hτ (sq_pos_of_pos (sub_pos.mpr hab)))).comp
      (fun p : ℝ × ℝ ↦ (p.1 / (b - a) ^ 2, (p.2 - a) / (b - a)))).mono
  intro p hp
  change τ / (b - a) ^ 2 ≤ p.1 / (b - a) ^ 2
  exact div_le_div_of_nonneg_right hp (sq_nonneg (b - a))

/-- The scaled first series is the spatial derivative. -/
theorem hasDerivAt_finiteIntervalHeatSeries_space (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (finiteIntervalHeatSeries a b c t) (finiteIntervalHeatSeriesDx a b c t x) x := by
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hx : HasDerivAt (fun y : ℝ ↦ (y - a) / (b - a)) (1 / (b - a)) x := by
    cas using hL
  unfold finiteIntervalHeatSeries finiteIntervalHeatSeriesDx
  simpa only [Function.comp_def,
    div_eq_mul_inv, one_mul] using
    (hasDerivAt_intervalHeatSeries_space hc
      (div_pos ht (sq_pos_of_pos (sub_pos.mpr hab))) ((x - a) / (b - a))).comp x hx

/-- Differentiating the first scaled spatial series gives the scaled time series. -/
theorem hasDerivAt_finiteIntervalHeatSeriesDx_space (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (finiteIntervalHeatSeriesDx a b c t)
      (finiteIntervalHeatSeriesDt a b c t x) x := by
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hx : HasDerivAt (fun y : ℝ ↦ (y - a) / (b - a)) (1 / (b - a)) x := by
    cas using hL
  unfold finiteIntervalHeatSeriesDx finiteIntervalHeatSeriesDt
  simpa only [Function.comp_def,
    div_eq_mul_inv, one_mul, pow_two, mul_inv, mul_assoc] using
    ((hasDerivAt_intervalHeatSeriesDx_space hc
      (div_pos ht (sq_pos_of_pos (sub_pos.mpr hab))) ((x - a) / (b - a))).comp x hx).div_const
      (b - a)

/-- The scaled time series is the time derivative. -/
theorem hasDerivAt_finiteIntervalHeatSeries_time (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s ↦ finiteIntervalHeatSeries a b c s x)
      (finiteIntervalHeatSeriesDt a b c t x) t := by
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hs : HasDerivAt (fun s : ℝ ↦ s / (b - a) ^ 2) (1 / (b - a) ^ 2) t := by
    cas using hL
  simpa only [finiteIntervalHeatSeries, finiteIntervalHeatSeriesDt, Function.comp_def,
    div_eq_mul_inv, one_mul] using
    (hasDerivAt_intervalHeatSeries_time hc
      (div_pos ht (sq_pos_of_pos (sub_pos.mpr hab))) ((x - a) / (b - a))).comp t hs

/-- The transported series satisfies the heat equation, with diffusivity one. -/
theorem finiteIntervalHeatSeries_heat_equation (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s ↦ finiteIntervalHeatSeries a b c s x) t =
      deriv (deriv (finiteIntervalHeatSeries a b c t)) x := by
  have hspace : deriv (finiteIntervalHeatSeries a b c t) = finiteIntervalHeatSeriesDx a b c t :=
    funext fun y ↦ (hasDerivAt_finiteIntervalHeatSeries_space hab hc ht y).deriv
  rw [hspace, (hasDerivAt_finiteIntervalHeatSeries_time hab hc ht x).deriv,
    (hasDerivAt_finiteIntervalHeatSeriesDx_space hab hc ht x).deriv]

/-- The left boundary value vanishes at every time. -/
theorem finiteIntervalHeatSeries_left_boundary (a b : ℝ) (c : ℕ → ℝ) (t : ℝ) :
    finiteIntervalHeatSeries a b c t a = 0 := by
  simp only [finiteIntervalHeatSeries, sub_self, zero_div, intervalHeatSeries_left_boundary]

/-- The right boundary value vanishes at every time for a nondegenerate interval. -/
theorem finiteIntervalHeatSeries_right_boundary (hab : a < b) (c : ℕ → ℝ) (t : ℝ) :
    finiteIntervalHeatSeries a b c t b = 0 := by
  simp only [finiteIntervalHeatSeries, div_self (ne_of_gt (sub_pos.mpr hab)),
    intervalHeatSeries_right_boundary]

/-- Joint continuity of the rescaled solution at positive time. -/
theorem continuousOn_finiteIntervalHeatSeries (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C) :
    ContinuousOn (fun p : ℝ × ℝ ↦ finiteIntervalHeatSeries a b c p.1 p.2)
      {p | 0 < p.1} := by
  apply (continuousOn_intervalHeatSeries hc).comp
    (f := fun p : ℝ × ℝ ↦ (p.1 / (b - a) ^ 2, (p.2 - a) / (b - a)))
  · fun_prop
  · intro p hp
    exact div_pos hp (sq_pos_of_pos (sub_pos.mpr hab))

/-- Joint continuity of the rescaled first spatial derivative series. -/
theorem continuousOn_finiteIntervalHeatSeriesDx (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C) :
    ContinuousOn (fun p : ℝ × ℝ ↦ finiteIntervalHeatSeriesDx a b c p.1 p.2)
      {p | 0 < p.1} := by
  apply ContinuousOn.div_const
  apply (continuousOn_intervalHeatSeriesDx hc).comp
    (f := fun p : ℝ × ℝ ↦ (p.1 / (b - a) ^ 2, (p.2 - a) / (b - a)))
  · fun_prop
  · intro p hp
    exact div_pos hp (sq_pos_of_pos (sub_pos.mpr hab))

/-- Joint continuity of the rescaled time and second spatial derivative series. -/
theorem continuousOn_finiteIntervalHeatSeriesDt (hab : a < b) (hc : ∀ n, ‖c n‖ ≤ C) :
    ContinuousOn (fun p : ℝ × ℝ ↦ finiteIntervalHeatSeriesDt a b c p.1 p.2)
      {p | 0 < p.1} := by
  apply ContinuousOn.div_const
  apply (continuousOn_intervalHeatSeriesDt hc).comp
    (f := fun p : ℝ × ℝ ↦ (p.1 / (b - a) ^ 2, (p.2 - a) / (b - a)))
  · fun_prop
  · intro p hp
    exact div_pos hp (sq_pos_of_pos (sub_pos.mpr hab))

end HeatEquation
