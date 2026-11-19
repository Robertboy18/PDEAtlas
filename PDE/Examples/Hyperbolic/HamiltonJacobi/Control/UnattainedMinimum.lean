/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import PDE.Hyperbolic.HamiltonJacobi.Control.Hamiltonian

/-!
# A compact control set without a minimizing control

The cost on `[0, 1]` equals the control away from zero and jumps to one at zero.
It is measurable, bounded, and independent of the state. Its infimum is zero,
but every control has a strictly positive cost. Thus compact controls and
Lipschitz dependence on the state do not by themselves give the pointwise
minimum used in the terminal Hamiltonian. Continuity in the control is needed
for that application of the extreme value theorem.
-/

@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace PDE.Examples.HamiltonJacobi.Control

/-- A bounded state-independent cost with an upward jump at the zero control. -/
def endpointJumpCost : ℝ → Icc (0 : ℝ) 1 → ℝ :=
  fun _ a ↦ if (a : ℝ) = 0 then 1 else a

/-- The jump cost takes every value in `(0, 1]`, so its lower endpoint is absent. -/
theorem range_endpointJumpCost (x : ℝ) :
    range (endpointJumpCost x) = Ioc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    unfold endpointJumpCost
    split_ifs with ha
    · exact ⟨zero_lt_one, le_rfl⟩
    · exact ⟨lt_of_le_of_ne a.property.1 (Ne.symm ha), a.property.2⟩
  · intro hz
    refine ⟨⟨z, hz.1.le, hz.2⟩, ?_⟩
    simp only [endpointJumpCost, ne_of_gt hz.1, ↓reduceIte]

/-- The cost is jointly measurable. -/
theorem measurable_endpointJumpCost :
    Measurable (fun q : ℝ × Icc (0 : ℝ) 1 ↦ endpointJumpCost q.1 q.2) := by
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_subtype_coe.comp measurable_snd) measurable_const)
    measurable_const (measurable_subtype_coe.comp measurable_snd)

/-- The cost is uniformly Lipschitz in the state with constant zero. -/
theorem endpointJumpCost_lipschitz (a : Icc (0 : ℝ) 1) :
    LipschitzWith 0 (fun x ↦ endpointJumpCost x a) := LipschitzWith.const _

/-- Every control has positive cost, and all costs are bounded by one. -/
theorem endpointJumpCost_mem (x : ℝ) (a : Icc (0 : ℝ) 1) :
    endpointJumpCost x a ∈ Ioc (0 : ℝ) 1 := by
  rw [← range_endpointJumpCost x]
  exact mem_range_self a

/-- The jump cost is bounded by one. -/
theorem abs_jumpCost_le (x : ℝ) (a : Icc (0 : ℝ) 1) : |endpointJumpCost x a| ≤ (1 : NNReal) := by
  rw [abs_of_pos (endpointJumpCost_mem x a).1]
  exact (endpointJumpCost_mem x a).2

/-- With zero dynamics the control Hamiltonian is `0`. -/
theorem controlHamiltonian_endpointJumpCost (p x : ℝ) :
    _root_.HamiltonJacobi.controlHamiltonian (fun _ _ ↦ 0) endpointJumpCost p x = 0 := by
  simp only [_root_.HamiltonJacobi.controlHamiltonian, inner_zero_right, zero_add,
    range_endpointJumpCost, csInf_Ioc zero_lt_one, neg_zero]

/-- There is always a cheaper control: the infimum on this compact set is not attained. -/
theorem endpointJumpCost_has_no_minimum (x : ℝ) :
    ¬ ∃ a : Icc (0 : ℝ) 1, ∀ b, endpointJumpCost x a ≤ endpointJumpCost x b := by
  rintro ⟨a, ha⟩
  have hc := endpointJumpCost_mem x a
  let b : Icc (0 : ℝ) 1 := ⟨endpointJumpCost x a / 2, by
    constructor <;> linarith [hc.1, hc.2]⟩
  have hb : endpointJumpCost x b = endpointJumpCost x a / 2 := by
    change (if endpointJumpCost x a / 2 = 0 then 1 else endpointJumpCost x a / 2) = _
    rw [ite_eq_right (ne_of_gt (half_pos hc.1))]
  have h := ha b
  rw [hb] at h
  linarith [hc.1]

end PDE.Examples.HamiltonJacobi.Control
