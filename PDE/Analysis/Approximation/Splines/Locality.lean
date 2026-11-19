/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.CoxDeBoor
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Locality of finite spline sums

Only basis functions whose supports meet a point contribute to a finite spline
sum. Strict separation from the closed support gives equality on a neighborhood,
so derivatives of a full spline can be proved using a finite local coefficient
window. A basis ending exactly at the point must be handled separately in the
derivative argument: its zero value alone does not imply a zero derivative.
-/

@[expose] public section

namespace CAS.Splines

open Set
open scoped Topology BigOperators

/-- Drop a finite prefix of a knot sequence. -/
def KnotSequence.shift (knots : KnotSequence) (offset : ℕ) : KnotSequence :=
  OrderHom.mk (fun i ↦ knots (offset + i))
    (fun _ _ h ↦ knots.monotone (Nat.add_le_add_left h offset))

/-- Evaluation of a shifted knot sequence. -/
@[simp]
theorem KnotSequence.shift_knot (knots : KnotSequence) (offset i : ℕ) :
    (knots.shift offset) i = knots (offset + i) := rfl

/-- Dropping a knot prefix simply shifts the basis indices. -/
theorem coxDeBoorBasis_shift (knots : KnotSequence) (offset degree index : ℕ) (x : ℝ) :
    coxDeBoorBasis (knots.shift offset) degree index x =
      coxDeBoorBasis knots degree (offset + index) x := by
  induction degree generalizing index with
  | zero =>
      simp only [coxDeBoorBasis_zero, KnotSequence.shift_knot, Nat.add_assoc]
      rfl
  | succ degree ih =>
      simp only [coxDeBoorBasis_succ, leftBlendWeight, rightBlendWeight,
        KnotSequence.shift_knot, ih, Nat.add_assoc]

/-- A local knot window identifies the corresponding global basis function. -/
theorem coxDeBoorBasis_congr_shift
    (globalKnots localKnots : KnotSequence) (offset degree index : ℕ) (x : ℝ)
    (hknots : ∀ j ≤ degree + 1,
      globalKnots (offset + (index + j)) = localKnots (index + j)) :
    coxDeBoorBasis globalKnots degree (offset + index) x =
      coxDeBoorBasis localKnots degree index x := by
  rw [← coxDeBoorBasis_shift]
  exact coxDeBoorBasis_congr_knots
    (globalKnots.shift offset) localKnots degree index x hknots

/-- Strict separation from a closed support makes the basis locally zero. -/
theorem coxDeBoorBasis_eventually_zero (knots : KnotSequence) (degree index : ℕ)
    {x : ℝ} (houtside : x < knots index ∨ knots (index + degree + 1) < x) :
    coxDeBoorBasis knots degree index =ᶠ[𝓝 x] (fun _ ↦ 0) := by
  rcases houtside with hleft | hright
  · filter_upwards [Iio_mem_nhds hleft] with y hy
    exact coxDeBoorBasis_eq_zero_of_lt_left knots degree index hy
  · filter_upwards [Ioi_mem_nhds hright] with y hy
    exact coxDeBoorBasis_eq_zero_of_right_le knots degree index hy.le

/-- Values of a finite spline sum only use the bases with nonzero support at the point. -/
theorem sum_coxDeBoorBasis_eq_sum_local
    (knots : KnotSequence) (degree : ℕ) (indices active : Finset ℕ)
    (coefficients : ℕ → ℝ) {x : ℝ} (hsubset : active ⊆ indices)
    (houtside : ∀ i ∈ indices, i ∉ active →
      x < knots i ∨ knots (i + degree + 1) ≤ x) :
    (∑ i ∈ indices, coxDeBoorBasis knots degree i x * coefficients i) =
      ∑ i ∈ active, coxDeBoorBasis knots degree i x * coefficients i := by
  symm
  apply Finset.sum_subset hsubset
  intro i hi hnot
  rcases houtside i hi hnot with hleft | hright
  · rw [coxDeBoorBasis_eq_zero_of_lt_left knots degree i hleft, zero_mul]
  · rw [coxDeBoorBasis_eq_zero_of_right_le knots degree i hright, zero_mul]

/-- Strictly separated omitted supports give a local equality of the full and windowed sums. -/
theorem sum_coxDeBoorBasis_eventually_eq_sum_local
    (knots : KnotSequence) (degree : ℕ) (indices active : Finset ℕ)
    (coefficients : ℕ → ℝ) {x : ℝ} (hsubset : active ⊆ indices)
    (houtside : ∀ i ∈ indices, i ∉ active →
      x < knots i ∨ knots (i + degree + 1) < x) :
    (fun y ↦ ∑ i ∈ indices, coxDeBoorBasis knots degree i y * coefficients i) =ᶠ[𝓝 x]
      (fun y ↦ ∑ i ∈ active, coxDeBoorBasis knots degree i y * coefficients i) := by
  have hzero : ∀ᶠ y in 𝓝 x, ∀ i ∈ indices, i ∉ active →
      coxDeBoorBasis knots degree i y = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    by_cases ha : i ∈ active
    · exact Filter.Eventually.of_forall fun _ hnot ↦ False.elim (hnot ha)
    · filter_upwards [coxDeBoorBasis_eventually_zero knots degree i (houtside i hi ha)]
        with y hy
      exact fun _ ↦ hy
  filter_upwards [hzero] with y hy
  symm
  apply Finset.sum_subset hsubset
  intro i hi hnot
  rw [hy i hi hnot, zero_mul]

/-- A finite tensor value only uses bases whose supports meet its coordinates. -/
theorem tensor_coxDeBoorBasis_eq_local
    (radial axial : KnotSequence) (radialDegree axialDegree : ℕ)
    (rows columns activeRows activeColumns : Finset ℕ) (coefficients : ℕ → ℕ → ℝ)
    {x z : ℝ} (hrows : activeRows ⊆ rows) (hcolumns : activeColumns ⊆ columns)
    (hradial : ∀ i ∈ rows, i ∉ activeRows →
      x < radial i ∨ radial (i + radialDegree + 1) ≤ x)
    (haxial : ∀ j ∈ columns, j ∉ activeColumns →
      z < axial j ∨ axial (j + axialDegree + 1) ≤ z) :
    (∑ i ∈ rows, coxDeBoorBasis radial radialDegree i x *
      ∑ j ∈ columns, coxDeBoorBasis axial axialDegree j z * coefficients i j) =
    (∑ i ∈ activeRows, coxDeBoorBasis radial radialDegree i x *
      ∑ j ∈ activeColumns, coxDeBoorBasis axial axialDegree j z * coefficients i j) := by
  rw [sum_coxDeBoorBasis_eq_sum_local radial radialDegree rows activeRows
    (fun i ↦ ∑ j ∈ columns, coxDeBoorBasis axial axialDegree j z * coefficients i j)
    hrows hradial]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_coxDeBoorBasis_eq_sum_local axial axialDegree columns activeColumns
    (coefficients i) hcolumns haxial]

/-- A tensor-product radial slice agrees locally with its active rectangular window.
The axial coordinate is fixed, so half-open support separation suffices there. -/
theorem tensor_coxDeBoorBasis_eventually_eq_local
    (radial axial : KnotSequence) (radialDegree axialDegree : ℕ)
    (rows columns activeRows activeColumns : Finset ℕ) (coefficients : ℕ → ℕ → ℝ)
    {x z : ℝ} (hrows : activeRows ⊆ rows) (hcolumns : activeColumns ⊆ columns)
    (hradial : ∀ i ∈ rows, i ∉ activeRows →
      x < radial i ∨ radial (i + radialDegree + 1) < x)
    (haxial : ∀ j ∈ columns, j ∉ activeColumns →
      z < axial j ∨ axial (j + axialDegree + 1) ≤ z) :
    (fun y ↦ ∑ i ∈ rows, coxDeBoorBasis radial radialDegree i y *
      ∑ j ∈ columns, coxDeBoorBasis axial axialDegree j z * coefficients i j) =ᶠ[𝓝 x]
    (fun y ↦ ∑ i ∈ activeRows, coxDeBoorBasis radial radialDegree i y *
      ∑ j ∈ activeColumns, coxDeBoorBasis axial axialDegree j z * coefficients i j) := by
  have hrow := sum_coxDeBoorBasis_eventually_eq_sum_local radial radialDegree rows activeRows
    (fun i ↦ ∑ j ∈ columns, coxDeBoorBasis axial axialDegree j z * coefficients i j)
    hrows hradial
  filter_upwards [hrow] with y hy
  rw [hy]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_coxDeBoorBasis_eq_sum_local axial axialDegree columns activeColumns
    (coefficients i) hcolumns haxial]

end CAS.Splines
