/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction
public import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Differences of nonnegative tests

A compact C¹ test is a difference of nonnegative compact C¹ tests in the same open
set. A smooth cutoff equal to one on its support supplies a positive majorant.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace TestFunction

/-- Every compact C¹ real test is a difference of two nonnegative tests in its domain. -/
theorem exists_sub_nonneg {n : ℕ} {U : Opens (ℝ^n)} (φ : 𝓓^{1}(U, ℝ)) :
    ∃ a b : 𝓓^{1}(U, ℝ),
      (∀ x, 0 ≤ a x) ∧ (∀ x, 0 ≤ b x) ∧ φ = a - b := by
  obtain ⟨χ, hχU, hχone, _, hχrange⟩ :=
    exists_eq_one_on_compact U.isOpen φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨C, hC⟩ :=
    φ.hasCompactSupport.isCompact.bddAbove_image φ.contDiff.continuous.norm.continuousOn
  let ψ : 𝓓^{1}(U, ℝ) :=
    .mk χ (χ.contDiff.of_le (by simp)) χ.hasCompactSupport hχU
  let b : 𝓓^{1}(U, ℝ) := max C 0 • ψ
  have hb (x : ℝ^n) : 0 ≤ b x :=
    mul_nonneg (le_max_right _ _) (hχrange x).1
  refine ⟨φ + b, b, ?_, hb, by simp⟩
  intro x
  change 0 ≤ φ x + max C 0 * χ x
  by_cases hx : x ∈ tsupport (φ : ℝ^n → ℝ)
  · have hone : χ x = 1 := hχone x hx
    rw [hone, mul_one]
    have hnorm := (hC (mem_image_of_mem _ hx)).trans (le_max_left C 0)
    have hlo := (abs_le.mp hnorm).1
    linarith
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_add]
    exact hb x

end TestFunction
