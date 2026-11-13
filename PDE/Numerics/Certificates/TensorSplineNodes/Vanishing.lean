/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Field

/-!
# Vanishing of node-engine fields beyond their knots

A term `c B_r(x)` of a mode vanishes for `x ≥ Y` when every knot of the raw spline `r` is at most
`Y`, since then every truncated power vanishes; a reflected term `c B_r(-x)` vanishes for `x ≥ Y`
when every knot is at least `-Y`, since then `-x` lies below all knots, where the spline vanishes by
the cancellation of its divided differences (this needs distinct knots). `Term.vanishesFrom` checks
this, and `Level.xVanishesFrom`, `Level.yVanishesFrom` check it for every term of every mode of one
variable of a level. Under these checks the node-engine field vanishes for `x ≥ Y`
(`field_eq_zero_of_le_fst`), respectively `y ≥ Y` (`field_eq_zero_of_le_snd`), whatever the other
variable.

## Main definitions

* `Term.vanishesFrom`: the check that a term vanishes from `Y` on.
* `Level.xVanishesFrom`, `Level.yVanishesFrom`: the check for every mode of one variable of a
  level.

## Main results

* `field_eq_zero_of_le_fst`: for strictly increasing knots and levels passing `xVanishesFrom` at
  `Y`, `field n L lv wt x y = 0` for `x ≥ Y`.
* `field_eq_zero_of_le_snd`: the same in the second variable, for `y ≥ Y`.
* `mode_eq_zero_of_vanishesFrom`: a mode all of whose terms pass `vanishesFrom` at `Y` vanishes
  at every `x ≥ Y`.
* `Term.eval_eq_zero_of_vanishesFrom`: the same for one term.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset CAS.Splines

/-- The term vanishes from `Y` on: its knots are at most `Y`, or at least `-Y` when it is
reflected. -/
def Term.vanishesFrom (n : ℕ) (K : ℕ → ℚ) (Y : ℚ) (τ : Term) : Bool :=
  (List.finRange (n + 3)).all fun t ↦
    if τ.reflect then decide (-Y ≤ K (τ.index + t)) else decide (K (τ.index + t) ≤ Y)

/-- For strictly increasing knots, a term that passes `vanishesFrom` at `Y` vanishes at every
`x ≥ Y`. -/
theorem Term.eval_eq_zero_of_vanishesFrom {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {Y : ℚ}
    {τ : Term} (h : τ.vanishesFrom n K Y = true) {x : ℝ} (hx : (Y : ℝ) ≤ x) :
    τ.eval n K x = 0 := by
  unfold Term.vanishesFrom at h
  rw [List.all_eq_true] at h
  have ht := fun t ↦ h t (List.mem_finRange t)
  unfold Term.eval raw
  cases hr : τ.reflect
  · simp only [hr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at ht ⊢
    rw [truncatedPowerBSpline_eq_zero_of_knots_le n _ (fun t ↦ ?_), mul_zero]
    exact (show ((K (τ.index + t) : ℚ) : ℝ) ≤ Y by exact_mod_cast ht t).trans hx
  · simp only [hr, ↓reduceIte, decide_eq_true_eq] at ht ⊢
    rw [truncatedPowerBSpline_eq_zero_of_le_knots n _ (injective_knots hK _) (fun t ↦ ?_),
      mul_zero]
    have h1 : (-(Y : ℝ)) ≤ (K (τ.index + t) : ℝ) := by exact_mod_cast ht t
    simp only [knots]
    linarith

/-- For strictly increasing knots, a mode all of whose terms pass `vanishesFrom` at `Y` vanishes at
every `x ≥ Y`. -/
theorem mode_eq_zero_of_vanishesFrom {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {Y : ℚ}
    {terms : List Term} (h : terms.all (Term.vanishesFrom n K Y) = true) {x : ℝ}
    (hx : (Y : ℝ) ≤ x) : mode n K terms x = 0 := by
  rw [List.all_eq_true] at h
  unfold mode
  induction terms with
  | nil => simp
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Term.eval_eq_zero_of_vanishesFrom hK (h τ (by simp)) hx,
      ih (fun σ hσ ↦ h σ (by simp [hσ])), add_zero]

/-- Every first-variable mode of the level vanishes from `Y` on. -/
def Level.xVanishesFrom (n : ℕ) (Y : ℚ) (lv : Level) : Bool :=
  (List.range lv.rows).all fun i ↦ (lv.xModes i).all (Term.vanishesFrom n lv.xKnots Y)

/-- Every second-variable mode of the level vanishes from `Y` on. -/
def Level.yVanishesFrom (n : ℕ) (Y : ℚ) (lv : Level) : Bool :=
  (List.range lv.cols).all fun j ↦ (lv.yModes j).all (Term.vanishesFrom n lv.yKnots Y)

/-- **The field vanishes beyond the knots of its first-variable modes.** -/
theorem field_eq_zero_of_le_fst {n L : ℕ} {lv : ℕ → Level} {wt : ℝ → ℝ} {Y : ℚ}
    (hK : ∀ m < L, StrictMono (lv m).xKnots) (h : ∀ m < L, (lv m).xVanishesFrom n Y = true)
    {x : ℝ} (hx : (Y : ℝ) ≤ x) (y : ℝ) : field n L lv wt x y = 0 := by
  unfold field
  refine sum_eq_zero fun m hm ↦ sum_eq_zero fun i hi ↦ sum_eq_zero fun j _ ↦ ?_
  have hm' := mem_range.mp hm
  have hmode := h m hm'
  unfold Level.xVanishesFrom at hmode
  rw [List.all_eq_true] at hmode
  rw [mode_eq_zero_of_vanishesFrom (hK m hm') (hmode i (List.mem_range.mpr (mem_range.mp hi))) hx]
  ring

/-- **The field vanishes beyond the knots of its second-variable modes.** -/
theorem field_eq_zero_of_le_snd {n L : ℕ} {lv : ℕ → Level} {wt : ℝ → ℝ} {Y : ℚ}
    (hK : ∀ m < L, StrictMono (lv m).yKnots) (h : ∀ m < L, (lv m).yVanishesFrom n Y = true)
    (x : ℝ) {y : ℝ} (hy : (Y : ℝ) ≤ y) : field n L lv wt x y = 0 := by
  unfold field
  refine sum_eq_zero fun m hm ↦ sum_eq_zero fun i _ ↦ sum_eq_zero fun j hj ↦ ?_
  have hm' := mem_range.mp hm
  have hmode := h m hm'
  unfold Level.yVanishesFrom at hmode
  rw [List.all_eq_true] at hmode
  rw [mode_eq_zero_of_vanishesFrom (hK m hm') (hmode j (List.mem_range.mpr (mem_range.mp hj))) hy]
  ring

end CAS.Numerics.TensorSpline
