/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import PDE.Analysis.Integration.Primitive.Basic

/-!
# Bounded primitives of periodic oscillations

Subtracting the cell mean from a continuous one-periodic function gives a periodic
primitive. Rescaling this primitive gives an error bounded by a constant times the
microscopic length, uniformly in the integration endpoint.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.PeriodicAveraging

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- The average over the unit cell. -/
def mean (q : ℝ → ℝ) : ℝ := ∫ y in (0 : ℝ)..1, q y

/-- The primitive after removing the mean linear part. -/
def fluctuation (q : ℝ → ℝ) (x : ℝ) : ℝ := primitive q x - mean q * x

/-- Integrating a bounded function over an initial subinterval of `[0,1]` preserves its bound. -/
theorem abs_primitive_le_on_unit {g : ℝ → ℝ} {M x : ℝ} (hM : 0 ≤ M)
    (hg : ∀ y ∈ Icc (0 : ℝ) 1, |g y| ≤ M) (hx : x ∈ Icc (0 : ℝ) 1) :
    |primitive g x| ≤ M := by
  have hb : ∀ y ∈ Ι (0 : ℝ) x, ‖g y‖ ≤ M := by
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) x := by
      simpa only [uIcc_of_le hx.1] using uIoc_subset_uIcc hy
    exact (Real.norm_eq_abs _).trans_le (hg y ⟨hy'.1, hy'.2.trans hx.2⟩)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] at hi
  exact hi.trans (mul_le_of_le_one_right hM hx.2)

/-- The fluctuation vanishes at zero. -/
@[simp] theorem fluctuation_zero (q : ℝ → ℝ) : fluctuation q 0 = 0 := by
  simp [fluctuation]

/-- Removing the mean makes the primitive periodic. -/
theorem periodic_fluctuation {q : ℝ → ℝ} (hq : Continuous q)
    (hp : Function.Periodic q 1) : Function.Periodic (fluctuation q) 1 := by
  intro x
  simp only [fluctuation, primitive,
    hp.intervalIntegral_add_eq_add 0 x (fun a b ↦ hq.intervalIntegrable a b), zero_add,
    mean]
  ring

/-- The fluctuation has derivative equal to the mean-zero oscillation. -/
theorem hasDerivAt_fluctuation {q : ℝ → ℝ} (hq : Continuous q) (x : ℝ) :
    HasDerivAt (fluctuation q) (q x - mean q) x := by
  change HasDerivAt (fun y ↦ primitive q y - mean q * y) _ x
  convert (hasDerivAt_primitive hq x).fun_sub
    ((hasDerivAt_id x).const_mul (mean q)) using 1 <;> simp

/-- A continuous periodic oscillation has a globally bounded primitive. -/
theorem exists_fluctuation_bound {q : ℝ → ℝ} (hq : Continuous q)
    (hp : Function.Periodic q 1) : ∃ K > 0, ∀ x, |fluctuation q x| ≤ K := by
  have hc : Continuous (fluctuation q) :=
    (continuous_primitive hq).sub (continuous_const.mul continuous_id)
  obtain ⟨K, hK, hb⟩ :=
    ((periodic_fluctuation hq hp).isBounded_of_continuous one_ne_zero hc).exists_pos_norm_le
  exact ⟨K, hK, fun x ↦ by simpa only [Real.norm_eq_abs] using hb _ (mem_range_self x)⟩

/-- Change of variables separates the cell average and the oscillatory remainder. -/
theorem primitive_rescale {q : ℝ → ℝ} {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    primitive (fun y ↦ q (y / ε)) x = mean q * x + ε * fluctuation q (x / ε) := by
  rw [primitive, integral_comp_div q hε]
  simp only [zero_div, smul_eq_mul, fluctuation, primitive]
  field_simp
  ring

/-- The primitive error is uniform on the whole line. -/
theorem abs_primitive_rescale_sub_le {q : ℝ → ℝ} {K ε : ℝ}
    (hb : ∀ x, |fluctuation q x| ≤ K) (hε : ε ≠ 0) (x : ℝ) :
    |primitive (fun y ↦ q (y / ε)) x - mean q * x| ≤ |ε| * K := by
  rw [primitive_rescale hε, add_sub_cancel_left, abs_mul]
  exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg ε)

end PDE.Analysis.PeriodicAveraging
