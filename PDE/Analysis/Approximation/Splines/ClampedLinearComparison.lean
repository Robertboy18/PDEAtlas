/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import CAS.ExactTactic

/-!
# Clamped linear interpolation and its right derivative

A finite sum of ramps defines the continuous interpolant, with constant
extensions beyond the first and last knots. Half-open panels select the
right affine germ at every knot. No differentiability of the nodal data is
required.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace CAS.Splines

/-- A continuous ramp, equal to `x-a` on `[a,b]` and constant on either side. -/
def linearRamp (a b x : ℝ) : ℝ :=
  max 0 (x - a) - max 0 (x - b)

/-- The ramp is continuous even when an endpoint is included. -/
theorem continuous_linearRamp (a b : ℝ) : Continuous (linearRamp a b) :=
  (continuous_const.max (continuous_id.sub continuous_const)).sub
    (continuous_const.max (continuous_id.sub continuous_const))

/-- The left constant germ of a ramp. -/
theorem linearRamp_of_le {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    linearRamp a b x = 0 := by
  simp [linearRamp, max_eq_left (sub_nonpos.mpr hx),
    max_eq_left (sub_nonpos.mpr (hx.trans hab))]

/-- The affine germ, with both endpoint values included. -/
theorem linearRamp_of_mem_Icc {a b x : ℝ} (hx : x ∈ Icc a b) :
    linearRamp a b x = x - a := by
  simp [linearRamp, max_eq_right (sub_nonneg.mpr hx.1),
    max_eq_left (sub_nonpos.mpr hx.2)]

/-- The right constant germ of a ramp. -/
theorem linearRamp_of_ge {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) :
    linearRamp a b x = b - a := by
  rw [linearRamp, max_eq_right (sub_nonneg.mpr (hab.trans hx)),
    max_eq_right (sub_nonneg.mpr hx)]
  cas

/-- The ramp has the indicated right derivative, including at both endpoints. -/
theorem hasDerivWithinAt_linearRamp_right {a b : ℝ} (hab : a < b) (x : ℝ) :
    HasDerivWithinAt (linearRamp a b) (if x ∈ Ico a b then 1 else 0) (Ioi x) x := by
  by_cases hleft : x < a
  · rw [ite_eq_right (fun h ↦ (not_le_of_gt hleft) h.1)]
    apply (hasDerivWithinAt_const x (Ioi x) (0 : ℝ)).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hleft)] with y hy
      exact linearRamp_of_le hab.le hy.le
    · exact linearRamp_of_le hab.le hleft.le
  by_cases hright : x < b
  · have hx : x ∈ Ico a b := ⟨le_of_not_gt hleft, hright⟩
    rw [ite_eq_left hx]
    have hd : HasDerivAt (fun y : ℝ ↦ y - a) 1 x := by cas
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hright)] with y hy hyb
      exact linearRamp_of_mem_Icc ⟨hx.1.trans hy.le, hyb.le⟩
    · exact linearRamp_of_mem_Icc ⟨hx.1, hx.2.le⟩
  · have hx : b ≤ x := le_of_not_gt hright
    rw [ite_eq_right (fun h ↦ hright h.2)]
    apply (hasDerivWithinAt_const x (Ioi x) (b - a)).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact linearRamp_of_ge hab.le (hx.trans hy.le)
    · exact linearRamp_of_ge hab.le hx

/-- The slope of an interpolating panel. -/
def interpolationSlope (a v : ℕ → ℝ) (i : ℕ) : ℝ :=
  (v (i + 1) - v i) / (a (i + 1) - a i)

/-- The continuous interpolant of `v 0, ..., v n`, clamped outside the knots. -/
def clampedLinear (a v : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  v 0 + ∑ i ∈ Finset.range n, interpolationSlope a v i * linearRamp (a i) (a (i + 1)) x

/-- The canonical right derivative, rather than a separately supplied coefficient. -/
def clampedLinearRightDeriv (a v : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  derivWithin (clampedLinear a v n) (Ioi x) x

/-- The clamped interpolant is globally continuous. -/
theorem continuous_clampedLinear (a v : ℕ → ℝ) (n : ℕ) :
    Continuous (clampedLinear a v n) := by
  exact continuous_const.add
    (continuous_finsetSum _ fun i _ ↦
      continuous_const.mul (continuous_linearRamp (a i) (a (i + 1))))

/-- The right derivative exists at every real point, including all knots. -/
theorem hasDerivWithinAt_clampedLinear_right
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivWithinAt (clampedLinear a v n)
      (clampedLinearRightDeriv a v n x) (Ioi x) x := by
  have hd := (hasDerivWithinAt_const x (Ioi x) (v 0)).add
    (HasDerivWithinAt.fun_sum fun i (_ : i ∈ Finset.range n) ↦
      (hasDerivWithinAt_linearRamp_right (ha (Nat.lt_succ_self i)) x).const_mul
        (interpolationSlope a v i))
  exact hd.differentiableWithinAt.hasDerivWithinAt

/-- An exact finite formula for the right derivative. -/
theorem clampedLinearRightDeriv_eq_sum
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    clampedLinearRightDeriv a v n x =
      ∑ i ∈ Finset.range n,
        if x ∈ Ico (a i) (a (i + 1)) then interpolationSlope a v i else 0 := by
  have hd := (hasDerivWithinAt_const x (Ioi x) (v 0)).add
    (HasDerivWithinAt.fun_sum fun i (_ : i ∈ Finset.range n) ↦
      (hasDerivWithinAt_linearRamp_right (ha (Nat.lt_succ_self i)) x).const_mul
        (interpolationSlope a v i))
  have hd' : HasDerivWithinAt (clampedLinear a v n)
      (0 + ∑ i ∈ Finset.range n, interpolationSlope a v i *
        (if x ∈ Ico (a i) (a (i + 1)) then 1 else 0)) (Ioi x) x := hd
  simpa only [clampedLinearRightDeriv, zero_add, mul_ite, mul_one, mul_zero] using
    hd'.derivWithin (uniqueDiffWithinAt_Ioi x)

/-- Measurability also holds at the knots and outside the interpolation interval. -/
theorem measurable_clampedLinearRightDeriv (a v : ℕ → ℝ) (n : ℕ) :
    Measurable (clampedLinearRightDeriv a v n) :=
  measurable_derivWithin_Ioi _

/-- Distinct half-open panels of a strictly increasing mesh are disjoint. -/
theorem eq_of_mem_interpolation_panels {a : ℕ → ℝ} (ha : StrictMono a)
    {i j : ℕ} {x : ℝ} (hi : x ∈ Ico (a i) (a (i + 1)))
    (hj : x ∈ Ico (a j) (a (j + 1))) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (not_lt_of_ge (ha.monotone hij) (hj.1.trans_lt hi.2))
  · exact hij
  · exact False.elim (not_lt_of_ge (ha.monotone hij) (hi.1.trans_lt hj.2))

/-- At a knot the outgoing slope is used. -/
theorem clampedLinearRightDeriv_eq_slope
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) {n i : ℕ} (hi : i < n)
    {x : ℝ} (hx : x ∈ Ico (a i) (a (i + 1))) :
    clampedLinearRightDeriv a v n x = interpolationSlope a v i := by
  rw [clampedLinearRightDeriv_eq_sum ha]
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hx
  · intro j _ hji
    exact ite_eq_right (fun hj ↦ hji (eq_of_mem_interpolation_panels ha hj hx))
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

/-- All right slopes vanish on the left open tail and the right closed tail. -/
theorem clampedLinearRightDeriv_eq_zero
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ)
    {x : ℝ} (hx : x < a 0 ∨ a n ≤ x) :
    clampedLinearRightDeriv a v n x = 0 := by
  rw [clampedLinearRightDeriv_eq_sum ha]
  apply Finset.sum_eq_zero
  intro i hi
  apply ite_eq_right
  intro h
  rcases hx with hx | hx
  · exact (not_le_of_gt hx) ((ha.monotone (Nat.zero_le i)).trans h.1)
  · exact (not_lt_of_ge hx)
      (h.2.trans_le (ha.monotone (Finset.mem_range.mp hi)))

/-- Nonnegative successive nodal differences imply nonnegative right derivatives. -/
theorem clampedLinearRightDeriv_nonneg
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ)
    (hv : ∀ i < n, v i ≤ v (i + 1)) (x : ℝ) :
    0 ≤ clampedLinearRightDeriv a v n x := by
  rw [clampedLinearRightDeriv_eq_sum ha]
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr (hv i (Finset.mem_range.mp hi)))
      (sub_nonneg.mpr (ha (Nat.lt_succ_self i)).le)
  · exact le_rfl

/-- A finite, unconditional global bound for the derivative.
Sharper certificate bounds may replace this finite sum. -/
theorem abs_clampedLinearRightDeriv_le
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    |clampedLinearRightDeriv a v n x| ≤
      ∑ i ∈ Finset.range n, |interpolationSlope a v i| := by
  rw [clampedLinearRightDeriv_eq_sum ha]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (interpolationSlope a v i)

/-- Every point between the first and last knot belongs to a half-open panel. -/
theorem exists_mem_interpolation_panel {a : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hx : x ∈ Ico (a 0) (a n)) :
    ∃ i < n, x ∈ Ico (a i) (a (i + 1)) := by
  induction n with
  | zero => exact False.elim (not_lt_of_ge hx.1 hx.2)
  | succ n ih =>
    by_cases hn : a n ≤ x
    · exact ⟨n, Nat.lt_succ_self n, hn, hx.2⟩
    · obtain ⟨i, hi, hpanel⟩ := ih ⟨hx.1, lt_of_not_ge hn⟩
      exact ⟨i, hi.trans (Nat.lt_succ_self n), hpanel⟩

/-- A ramp traversed in full contributes exactly one nodal difference. -/
theorem interpolationSlope_mul_width
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (i : ℕ) :
    interpolationSlope a v i * (a (i + 1) - a i) = v (i + 1) - v i := by
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr (ha (Nat.lt_succ_self i)).ne')

/-- On each closed panel the finite ramp formula is the affine interpolant. -/
theorem clampedLinear_eq_panel
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) {n i : ℕ} (hi : i < n)
    {x : ℝ} (hx : x ∈ Icc (a i) (a (i + 1))) :
    clampedLinear a v n x = v i + interpolationSlope a v i * (x - a i) := by
  have htruncate :
      ∑ j ∈ Finset.range n, interpolationSlope a v j * linearRamp (a j) (a (j + 1)) x =
        ∑ j ∈ Finset.range (i + 1),
          interpolationSlope a v j * linearRamp (a j) (a (j + 1)) x := by
    symm
    apply Finset.sum_subset (Finset.range_mono hi)
    intro j _ hj
    have hij : i + 1 ≤ j := Nat.le_of_not_lt (fun h ↦ hj (Finset.mem_range.mpr h))
    rw [linearRamp_of_le (ha (Nat.lt_succ_self j)).le
      (hx.2.trans (ha.monotone hij)), mul_zero]
  have hearly :
      ∑ j ∈ Finset.range i, interpolationSlope a v j * linearRamp (a j) (a (j + 1)) x =
        v i - v 0 := by
    rw [← Finset.sum_range_sub v i]
    apply Finset.sum_congr rfl
    intro j hj
    rw [linearRamp_of_ge (ha (Nat.lt_succ_self j)).le
      ((ha.monotone (Finset.mem_range.mp hj)).trans hx.1)]
    exact interpolationSlope_mul_width ha v j
  rw [clampedLinear, htruncate, Finset.sum_range_succ, hearly,
    linearRamp_of_mem_Icc hx]
  abel

/-- The interpolant is constant to the left, including the first knot. -/
theorem clampedLinear_eq_left
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ)
    {x : ℝ} (hx : x ≤ a 0) :
    clampedLinear a v n x = v 0 := by
  rw [clampedLinear]
  have hsum :
      ∑ i ∈ Finset.range n, interpolationSlope a v i * linearRamp (a i) (a (i + 1)) x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [linearRamp_of_le (ha (Nat.lt_succ_self i)).le
      (hx.trans (ha.monotone (Nat.zero_le i))), mul_zero]
  rw [hsum, add_zero]

/-- The interpolant is constant to the right, including the last knot. -/
theorem clampedLinear_eq_right
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ)
    {x : ℝ} (hx : a n ≤ x) :
    clampedLinear a v n x = v n := by
  rw [clampedLinear]
  have hsum :
      ∑ i ∈ Finset.range n, interpolationSlope a v i * linearRamp (a i) (a (i + 1)) x =
        v n - v 0 := by
    rw [← Finset.sum_range_sub v n]
    apply Finset.sum_congr rfl
    intro i hi
    rw [linearRamp_of_ge (ha (Nat.lt_succ_self i)).le
      ((ha.monotone (Finset.mem_range.mp hi)).trans hx)]
    exact interpolationSlope_mul_width ha v i
  rw [hsum, add_sub_cancel]

/-- The outgoing affine panel is a right germ, including at its left knot. -/
theorem clampedLinear_eventuallyEq_panel
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) {n i : ℕ} (hi : i < n)
    {x : ℝ} (hx : x ∈ Ico (a i) (a (i + 1))) :
    clampedLinear a v n =ᶠ[𝓝[Ioi x] x]
      (fun y ↦ v i + interpolationSlope a v i * (y - a i)) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hx.2)] with y hy hyb
  exact clampedLinear_eq_panel ha v hi ⟨hx.1.trans hy.le, hyb.le⟩

/-- A bound on each of finitely many slopes bounds the derivative everywhere. -/
theorem abs_clampedLinearRightDeriv_le_of_slopes
    {a : ℕ → ℝ} (ha : StrictMono a) (v : ℕ → ℝ) (n : ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i < n, |interpolationSlope a v i| ≤ C) (x : ℝ) :
    |clampedLinearRightDeriv a v n x| ≤ C := by
  by_cases hleft : x < a 0
  · rw [clampedLinearRightDeriv_eq_zero ha v n (Or.inl hleft), abs_zero]
    exact hC
  by_cases hright : a n ≤ x
  · rw [clampedLinearRightDeriv_eq_zero ha v n (Or.inr hright), abs_zero]
    exact hC
  obtain ⟨i, hi, hpanel⟩ :=
    exists_mem_interpolation_panel ⟨le_of_not_gt hleft, lt_of_not_ge hright⟩
  rw [clampedLinearRightDeriv_eq_slope ha v hi hpanel]
  exact hv i hi

end CAS.Splines
