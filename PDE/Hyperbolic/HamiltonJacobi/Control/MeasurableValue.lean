/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Value

/-!
# Measurable representatives of control costs

Changing a control on a null set preserves its trajectory on the closed interval,
and hence its running and terminal costs. Choosing Mathlib's measurable
representative identifies the set of costs, and so the value, with those over
Borel measurable controls `ℝ → A`. No optimal control is selected.

These congruences need no regularity of the cost functions. Integrability of the
running cost along a trajectory, `intervalIntegrable_control_runningCost`, uses
joint measurability and a uniform bound.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace

namespace HamiltonJacobi

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

local notation "X" => controlResponse f hf K M hK hM
local notation "J" => controlCost f hf K M hK hM

/-- Controls that agree almost everywhere on the time interval have the same total
cost. The interval may have length zero. -/
theorem control_cost_congr_ae (h : E → A → ℝ) (g : E → ℝ) {a b : ℝ} (hab : a ≤ b)
    (α β : ControlOn A a b) (x : E) (hαβ : α.1 =ᵐ[volume.restrict (Ioc a b)] β.1) :
    J h g hab α x = J h g hab β x := by
  have hX : EqOn (X hab α x) (X hab β x) (Icc a b) := by
    simpa only [control_response_initial] using
      control_response_eqOn_segment f hf K M hK hM hab hab le_rfl le_rfl α β x hαβ
  have hR : controlRunningCost f hf K M hK hM h hab α x =
      controlRunningCost f hf K M hK hM h hab β x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hab]
    filter_upwards [hαβ, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    exact congrArg₂ h (hX ⟨hmem.1.le, hmem.2⟩) ht
  simp only [controlCost, hR, hX ⟨hab, le_rfl⟩]

variable [SecondCountableTopology A]

/-- For a second-countable control space, a.e. strongly measurable controls on `[a, b]`
and Borel measurable controls `ℝ → A` give the same set of costs. -/
theorem range_control_cost_eq_range_measurable (h : E → A → ℝ) (g : E → ℝ)
    {a b : ℝ} (hab : a ≤ b) (x : E) :
    range (fun α : ControlOn A a b ↦ J h g hab α x) = range (fun α : {α : ℝ → A // Measurable α} ↦
      J h g hab ⟨α.1, α.2.stronglyMeasurable.aestronglyMeasurable⟩ x) := by
  apply Set.Subset.antisymm
  · rintro z ⟨α, rfl⟩
    let β : {β : ℝ → A // Measurable β} := ⟨α.2.mk α.1, α.2.measurable_mk⟩
    refine ⟨β, ?_⟩
    exact (control_cost_congr_ae f hf K M hK hM h g hab α
      ⟨β.1, β.2.stronglyMeasurable.aestronglyMeasurable⟩ x
      (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self α.2.ae_eq_mk)).symm
  · rintro z ⟨α, rfl⟩
    exact ⟨⟨α.1, α.2.stronglyMeasurable.aestronglyMeasurable⟩, rfl⟩

/-- For a second-countable control space, the control value is the infimum of the costs
of Borel measurable controls `ℝ → A`. -/
theorem control_value_eq_sInf_measurable (h : E → A → ℝ) (g : E → ℝ)
    {a b : ℝ} (hab : a ≤ b) (x : E) :
    controlValue f hf K M hK hM h g hab x = sInf (range (fun α : {α : ℝ → A // Measurable α} ↦
      J h g hab ⟨α.1, α.2.stronglyMeasurable.aestronglyMeasurable⟩ x)) :=
  congrArg sInf (range_control_cost_eq_range_measurable f hf K M hK hM h g hab x)

end HamiltonJacobi
