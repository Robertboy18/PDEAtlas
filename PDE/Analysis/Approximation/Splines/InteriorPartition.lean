/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.NormalizedBasis

/-!
# Interior partitions for finite Cox–de Boor windows

A finite window of simple knots already gives a partition of unity on its
interior span. This justifies subtracting a constant coefficient anchor when
bounding a local spline, without requiring endpoint clamping of the window.
-/

@[expose] public section

namespace CAS.Splines

open Set

/-- A simple-knot window reproduces constants between its interior endpoints. -/
theorem sum_finiteCoxDeBoorBasis_eq_one_of_interior (knots : KnotSequence)
    (degree count : ℕ)
    (hstrict : ∀ i < count + degree, knots i < knots (i + 1))
    {x : ℝ} (hx : x ∈ Ico (knots degree) (knots count)) :
    (∑ i : Fin count, finiteCoxDeBoorBasis knots degree count i x) = 1 := by
  induction degree generalizing count with
  | zero => exact sum_finiteCoxDeBoorBasis_zero_eq_one knots count hx
  | succ degree ih =>
      cases count with
      | zero =>
          exact (not_lt_of_ge ((knots.monotone (Nat.zero_le _)).trans hx.1)) hx.2 |>.elim
      | succ count =>
          have hleft : coxDeBoorBasis knots degree 0 x = 0 :=
            coxDeBoorBasis_eq_zero_of_right_le knots degree 0 (by simpa using hx.1)
          have hright : coxDeBoorBasis knots degree (count + 1) x = 0 :=
            coxDeBoorBasis_eq_zero_of_lt_left knots degree (count + 1) hx.2
          rw [sum_finiteCoxDeBoorBasis_succ_eq_sum knots degree count x
            (by simp [hleft]) _ (by simp [hright])]
          · apply ih
            · intro i hi
              exact hstrict i (by omega)
            · exact ⟨(knots.monotone (by omega)).trans hx.1,
                hx.2.trans_le (knots.monotone (by omega))⟩
          · intro i
            apply coxDeBoorBasis_mul_add_adjacent_weights
            exact ne_of_gt ((hstrict (i.val + 1) (by omega)).trans_le
              (knots.monotone (by omega)))

/-- A normalized local basis on the interior of an unclamped simple-knot window. -/
def interiorCoxDeBoorPartition (knots : KnotSequence) (degree count : ℕ)
    (hstrict : ∀ i < count + degree, knots i < knots (i + 1)) :
    FiniteCoxDeBoorPartition knots degree count where
  carrier := Ico (knots degree) (knots count)
  sum_eq_one_on := fun _ hx ↦
    sum_finiteCoxDeBoorBasis_eq_one_of_interior knots degree count hstrict hx

end CAS.Splines
