/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.RationalReplay
public import PDE.Analysis.Approximation.Splines.SecondDerivatives
public import Mathlib.Data.List.GetD

/-!
# Rational spline replay agrees with real spline semantics

The four cast lemmas identify exact rational value, branch-value, first-derivative,
and second-derivative tables with their real Cox–de Boor quantities at the origin.
The hypotheses are a rational knot list and a real knot sequence agreeing at every
index of that list. Each lookup also requires its stated degree-dependent index bound.

Every proof is an induction on the degree. The recurrence step applies the induction
hypothesis at adjacent indices and uses the knot agreement to move between rational
and real arithmetic. The branch lemmas concern polynomial extensions; they do not by
themselves prove smoothness of the piecewise spline at a knot.
-/

@[expose] public section

namespace CAS.Splines.ReplaySemantics

open CAS.Splines CAS.Splines.RationalReplay

variable (knots : List ℚ) (realKnots : KnotSequence)
    (hknots : ∀ i < knots.length, realKnots i = (knots.getD i 0 : ℝ))

-- `hknots` is used only inside the proofs below, never in their statements, so Lean would
-- drop it from the signatures. Including it explicitly keeps every lemma stated for an
-- arbitrary matching pair and lets each caller supply its own window's agreement lemma.
include hknots

/-- Rational local tables evaluate the real Cox–de Boor basis for matching knots. -/
theorem basisTable_cast (degree i : ℕ) (hi : i + degree + 1 < knots.length) :
    ((basisTable knots degree).getD i 0 : ℝ) = coxDeBoorBasis realKnots degree i 0 := by
  induction degree generalizing i with
  | zero =>
    have hr : i < knots.length - 1 := by omega
    rw [basisTable, initialTable, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hr, Option.map_some, Option.getD_some, coxDeBoorBasis_zero]
    rw [hknots i (by omega), hknots (i + 1) (by omega)]
    simp only [Set.mem_Ico, Rat.cast_nonpos, Rat.cast_pos]
    split <;> simp_all
  | succ degree ih =>
    have hr : i < knots.length - (degree + 1) - 1 := by omega
    rw [basisTable, nextTable, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hr, Option.map_some, Option.getD_some, coxDeBoorBasis_succ]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_sub]
    rw [ih i (by omega), ih (i + 1) (by omega)]
    unfold leftBlendWeight rightBlendWeight
    rw [hknots i (by omega), hknots (i + 1) (by omega),
      hknots (i + degree + 1) (by omega), hknots (i + degree + 2) (by omega)]
    simp only [zero_sub]
    simp only [Nat.add_assoc, sub_zero]

/-- A rational branch table casts to the real polynomial branch at the origin. -/
theorem branchValues_cast (cell degree i : ℕ) (hi : i + degree + 1 < knots.length) :
    ((branchValues knots cell degree).getD i 0 : ℝ) =
      coxDeBoorBranch realKnots cell degree i 0 := by
  induction degree generalizing i with
  | zero =>
    have hr : i < knots.length - 1 := by omega
    rw [branchValues, initialBranchValues, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hr, Option.map_some, Option.getD_some, coxDeBoorBranch]
    split <;> simp_all
  | succ degree ih =>
    have hr : i < knots.length - (degree + 1) - 1 := by omega
    rw [branchValues, nextTable, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hr, Option.map_some, Option.getD_some, coxDeBoorBranch]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_sub]
    rw [ih i (by omega), ih (i + 1) (by omega)]
    unfold leftBlendWeight rightBlendWeight
    rw [hknots i (by omega), hknots (i + 1) (by omega),
      hknots (i + degree + 1) (by omega), hknots (i + degree + 2) (by omega)]
    simp only [zero_sub, Nat.add_assoc, sub_zero]

/-- The checked rational product-rule table is the branch derivative. -/
theorem branchDerivatives_cast (cell degree i : ℕ) (hi : i + degree + 1 < knots.length) :
    ((branchDerivatives knots cell degree).getD i 0 : ℝ) =
      coxDeBoorBranchDerivative realKnots cell degree i 0 := by
  induction degree generalizing i with
  | zero => simp [branchDerivatives, coxDeBoorBranchDerivative]
  | succ degree ih =>
    have hr : i < knots.length - (degree + 1) - 1 := by omega
    rw [branchDerivatives, nextBranchDerivatives, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hr, Option.map_some, Option.getD_some,
      coxDeBoorBranchDerivative]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_sub,
      Rat.cast_one]
    rw [ih i (by omega), ih (i + 1) (by omega),
      branchValues_cast knots realKnots hknots cell degree i (by omega),
      branchValues_cast knots realKnots hknots cell degree (i + 1) (by omega)]
    unfold leftBlendWeight rightBlendWeight leftBlendWeightDerivative rightBlendWeightDerivative
    rw [hknots i (by omega), hknots (i + 1) (by omega),
      hknots (i + degree + 1) (by omega), hknots (i + degree + 2) (by omega)]
    simp only [zero_sub, Nat.add_assoc, sub_zero]

/-- The checked rational second-jet table is the branch second derivative. -/
theorem branchSecondDerivatives_cast (cell degree i : ℕ)
    (hi : i + degree + 1 < knots.length) :
    ((branchSecondDerivatives knots cell degree).getD i 0 : ℝ) =
      coxDeBoorBranchSecondDerivative realKnots cell degree i 0 := by
  induction degree generalizing i with
  | zero => simp [branchSecondDerivatives, coxDeBoorBranchSecondDerivative]
  | succ degree ih =>
    have hr : i < knots.length - (degree + 1) - 1 := by omega
    rw [branchSecondDerivatives, nextSecondDerivatives, List.getD_eq_getElem?_getD,
      List.getElem?_map,
      List.getElem?_range hr, Option.map_some, Option.getD_some,
      coxDeBoorBranchSecondDerivative]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_sub,
      Rat.cast_one, Rat.cast_ofNat]
    rw [ih i (by omega), ih (i + 1) (by omega),
      branchDerivatives_cast knots realKnots hknots cell degree i (by omega),
      branchDerivatives_cast knots realKnots hknots cell degree (i + 1) (by omega)]
    unfold leftBlendWeight rightBlendWeight leftBlendWeightDerivative rightBlendWeightDerivative
    rw [hknots i (by omega), hknots (i + 1) (by omega),
      hknots (i + degree + 1) (by omega), hknots (i + degree + 2) (by omega)]
    simp only [zero_sub, Nat.add_assoc, sub_zero]

end CAS.Splines.ReplaySemantics
