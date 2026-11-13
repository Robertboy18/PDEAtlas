/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Coordinatewise bounds for finite ℓᵖ norms

A bound on each coordinate gives the same bound on the finite ℓᵖ norm. The
coordinate spaces can differ, so this applies both to restriction of functions
and to maps of their codomains. The endpoint `p = ∞` uses the maximum norm.
-/

@[expose] public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F G : ι → Type*}
  [∀ i, SeminormedAddCommGroup (F i)] [∀ i, SeminormedAddCommGroup (G i)]

/-- Coordinatewise norm domination implies domination of every finite ℓᵖ norm. -/
theorem norm_mono (x : PiLp p F) (y : PiLp p G)
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Subsingleton.elim x 0, norm_zero]
    exact norm_nonneg y
  · rcases p.dichotomy with rfl | hp
    · rw [norm_eq_ciSup, norm_eq_ciSup]
      exact ciSup_mono (Finite.bddAbove_range _) h
    · rw [norm_eq_sum (zero_lt_one.trans_le hp), norm_eq_sum (zero_lt_one.trans_le hp)]
      gcongr
      · exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _
      · exact h _

/-- A uniform bound on the coordinates has the same constant in the ℓᵖ norm. -/
theorem norm_le_mul_of_norm_apply_le [∀ i, NormedSpace ℝ (G i)]
    (x : PiLp p F) (y : PiLp p G) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ‖x i‖ ≤ c * ‖y i‖) : ‖x‖ ≤ c * ‖y‖ := by
  calc
    ‖x‖ ≤ ‖c • y‖ := norm_mono x (c • y) fun i ↦ by
      simpa only [PiLp.smul_apply, norm_smul, Real.norm_of_nonneg hc] using h i
    _ = c * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hc]

/-- Forgetting coordinates cannot increase an ℓᵖ norm.
Injectivity ensures that no coordinate is counted twice. -/
theorem norm_mono_of_injective
    {κ : Type*} [Fintype κ] {H : κ → Type*} [∀ j, SeminormedAddCommGroup (H j)]
    (e : ι → κ) (he : Function.Injective e) (x : PiLp p F) (y : PiLp p H)
    (h : ∀ i, ‖x i‖ ≤ ‖y (e i)‖) : ‖x‖ ≤ ‖y‖ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Subsingleton.elim x 0, norm_zero]
    exact norm_nonneg y
  · have : Nonempty κ := Nonempty.map e hι
    rcases p.dichotomy with rfl | hp
    · rw [norm_eq_ciSup, norm_eq_ciSup]
      exact ciSup_le fun i ↦ (h i).trans
        (le_ciSup (Finite.bddAbove_range fun j ↦ ‖y j‖) (e i))
    · rw [norm_eq_sum (zero_lt_one.trans_le hp), norm_eq_sum (zero_lt_one.trans_le hp)]
      apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦
        Real.rpow_nonneg (norm_nonneg (x i)) _)
      · calc
          ∑ i, ‖x i‖ ^ p.toReal ≤ ∑ i, ‖y (e i)‖ ^ p.toReal :=
            Finset.sum_le_sum fun i _ ↦
              Real.rpow_le_rpow (norm_nonneg _) (h i) ENNReal.toReal_nonneg
          _ = ∑ j ∈ Finset.univ.image e, ‖y j‖ ^ p.toReal := by
            rw [Finset.sum_image]
            exact fun _ _ _ _ hij ↦ he hij
          _ ≤ ∑ j, ‖y j‖ ^ p.toReal :=
            Finset.sum_le_univ_sum_of_nonneg fun j ↦ Real.rpow_nonneg (norm_nonneg _) _
      · positivity

end PiLp
