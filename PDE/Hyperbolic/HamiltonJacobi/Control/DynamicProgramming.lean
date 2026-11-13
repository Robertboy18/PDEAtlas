/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Value

/-!
# Dynamic programming for measurable controls

Splitting a control gives one inequality; concatenating any prefix and tail
controls gives the other. The order properties of the real infimum suffice:
there is no choice of an optimal control, and no measurable selection of tails
as a function of the intermediate state.

The response is the Carathéodory trajectory for bounded, state-Lipschitz
continuous dynamics on a separable real Banach space. A bounded jointly measurable
running cost and a terminal cost bounded below suffice for the identity.
Both cuts at an endpoint are included.

The identity is Theorem 1 (Optimality conditions) of Evans, §10.3.2, equation (7). Evans gets
the upper bound by concatenating a prefix control with a nearly optimal tail, (8)-(14), and the
lower bound by splitting a nearly optimal control at the cut, (15)-(16). We concatenate and
split arbitrary controls and pass to the infimum.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.2, Theorem 1 and its proof, equations (7)-(16).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Topology

namespace HamiltonJacobi

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
  [Nonempty A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

local notation "X" => controlResponse f hf K M hK hM
local notation "R" => controlRunningCost f hf K M hK hM
local notation "J" => controlCost f hf K M hK hM
local notation "V" => controlValue f hf K M hK hM

/-- The value equals the infimum of the cost up to the cut plus the value from the
state reached there. Controls are a.e. strongly measurable on their own intervals.
The inequalities `a ≤ c ≤ b` allow either segment to have zero length. -/
theorem control_value_dynamic_programming (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (g : E → ℝ) (hg : BddBelow (range g)) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (x : E) :
    V h g (hac.trans hcb) x =
      sInf (range (fun α : ControlOn A a c ↦ R h hac α x + V h g hcb (X hac α x c))) := by
  let S : Set ℝ := range (fun α : ControlOn A a c ↦ R h hac α x + V h g hcb (X hac α x c))
  have hne : S.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty A›
    exact ⟨_, mem_range_self (ControlOn.const a c v)⟩
  have hbdd : BddBelow S := by
    obtain ⟨m, hm⟩ := hg
    refine ⟨m - (C : ℝ) * (b - a), ?_⟩
    rintro _ ⟨α, rfl⟩
    have hp := (abs_le.mp (abs_control_runningCost_le f hf K M hK hM h C hC hac α x)).1
    have ht := control_value_lower_bound f hf K M hK hM h C hC g m
      (fun y ↦ hm (mem_range_self y)) hcb (X hac α x c)
    nlinarith
  change V h g (hac.trans hcb) x = sInf S
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨α, rfl⟩
    -- Concatenation works for every tail, so it supplies a lower bound of its cost set.
    have htail : V h g (hac.trans hcb) x - R h hac α x ≤
        V h g hcb (X hac α x c) := by
      apply le_csInf (control_costs_nonempty f hf K M hK hM h g hcb (X hac α x c))
      rintro _ ⟨β, rfl⟩
      have hwhole := control_value_le_cost f hf K M hK hM h C hC g hg (hac.trans hcb) (α.concat β) x
      rw [control_cost_concat f hf K M hK hM h hh C hC g hac hcb α β x] at hwhole
      linarith
    linarith
  · apply le_csInf (control_costs_nonempty f hf K M hK hM h g (hac.trans hcb) x)
    rintro _ ⟨γ, rfl⟩
    let α : ControlOn A a c := γ.restrict le_rfl hcb
    let β : ControlOn A c b := γ.restrict hac le_rfl
    have hprefix : sInf S ≤ R h hac α x + V h g hcb (X hac α x c) :=
      csInf_le hbdd (mem_range_self α)
    have htail := control_value_le_cost f hf K M hK hM h C hC g hg hcb β (X hac α x c)
    have hsplit := control_cost_split f hf K M hK hM h hh C hC g hac hcb γ α β x
      (Filter.Eventually.of_forall fun _ ↦ rfl) (Filter.Eventually.of_forall fun _ ↦ rfl)
    linarith

end HamiltonJacobi
