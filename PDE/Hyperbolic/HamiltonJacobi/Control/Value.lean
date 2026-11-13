/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Restart

/-!
# Costs of measurable controls

Running costs are integrated along the constructed response. Joint measurability,
a uniform bound, and local measurability of the control give interval
integrability. A lower bound for the terminal cost then bounds all total costs
from below. A constant control supplies a competitor when the control space is
nonempty, so the real infimum defines a finite value.

No regularity of the terminal cost is needed for these facts or for splitting a
cost at an intermediate time. In particular, it is only evaluated at the terminal
state, not integrated against a measure on state space.

`controlCost` is the cost functional (4) of Evans, §10.3.1, and `controlValue` is the value
function (6) of §10.3.2, on an interval `[a, b]` in place of `[t, T]`. Evans assumes the bounds
and Lipschitz bounds (5) on the running and terminal costs throughout.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.1, equations (4)-(5); §10.3.2, equation (6).
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

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

local notation "X" => controlResponse f hf K M hK hM

/-- The accumulated running cost along the constructed trajectory. -/
def controlRunningCost (h : E → A → ℝ) {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x : E) : ℝ :=
  ∫ t in a..b, h (X hab α x t) (α.1 t)

/-- Running cost plus terminal cost evaluated at the controlled trajectory's endpoint. -/
def controlCost (h : E → A → ℝ) (g : E → ℝ) {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x : E) : ℝ :=
  controlRunningCost f hf K M hK hM h hab α x + g (X hab α x b)

/-- The infimum of the total cost over all controls that are a.e. strongly measurable
on `[a, b]`. It is a finite real number when the control space is nonempty, the running
cost is bounded and the terminal cost is bounded below. -/
def controlValue (h : E → A → ℝ) (g : E → ℝ) {a b : ℝ} (hab : a ≤ b) (x : E) : ℝ :=
  sInf (range (fun α : ControlOn A a b ↦ controlCost f hf K M hK hM h g hab α x))

local notation "R" => controlRunningCost f hf K M hK hM
local notation "J" => controlCost f hf K M hK hM
local notation "V" => controlValue f hf K M hK hM

/-- A bounded jointly measurable running cost is integrable along every admissible response. -/
theorem intervalIntegrable_control_runningCost (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) :
    IntervalIntegrable (fun t ↦ h (X hab α x t) (α.1 t)) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  have hX : AEMeasurable (X hab α x) (volume.restrict (Icc a b)) :=
    (control_response_lipschitz f hf K M hK hM hab α x).continuous.measurable.aemeasurable
  apply IntegrableOn.of_bound measure_Icc_lt_top
    (hh.comp_aemeasurable (hX.prodMk α.2.aemeasurable)).aestronglyMeasurable (C : ℝ)
  exact Filter.Eventually.of_forall fun t ↦ by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hC (X hab α x t) (α.1 t)

/-- The absolute running cost is bounded by the elapsed time times its uniform bound. -/
theorem abs_control_runningCost_le (h : E → A → ℝ) (C : NNReal)
    (hC : ∀ x v, |h x v| ≤ (C : ℝ)) {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x : E) : |R h hab α x| ≤ (C : ℝ) * (b - a) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun t ↦ h (X hab α x t) (α.1 t))
    (fun t _ht ↦ by simpa only [Real.norm_eq_abs] using hC (X hab α x t) (α.1 t))
  simpa only [controlRunningCost, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hbound

/-- A lower bound for the terminal cost gives a uniform lower bound for every total cost. -/
theorem control_cost_lower_bound (h : E → A → ℝ) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (g : E → ℝ) (m : ℝ) (hm : ∀ y, m ≤ g y) {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) :
    m - (C : ℝ) * (b - a) ≤ J h g hab α x := by
  have hr := (abs_le.mp (abs_control_runningCost_le f hf K M hK hM h C hC hab α x)).1
  have hg := hm (X hab α x b)
  dsimp only [controlCost]
  linarith

/-- The set of total costs is bounded below before its real infimum is used. -/
theorem bddBelow_control_costs (h : E → A → ℝ) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (g : E → ℝ) (hg : BddBelow (range g)) {a b : ℝ} (hab : a ≤ b) (x : E) :
    BddBelow (range (fun α : ControlOn A a b ↦ J h g hab α x)) := by
  obtain ⟨m, hm⟩ := hg
  refine ⟨m - (C : ℝ) * (b - a), ?_⟩
  rintro _ ⟨α, rfl⟩
  exact control_cost_lower_bound f hf K M hK hM h C hC g m (fun y ↦ hm (mem_range_self y)) hab α x

/-- Any particular admissible control bounds the value from above. -/
theorem control_value_le_cost (h : E → A → ℝ) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (g : E → ℝ) (hg : BddBelow (range g)) {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) :
    V h g hab x ≤ J h g hab α x :=
  csInf_le (bddBelow_control_costs f hf K M hK hM h C hC g hg hab x) (mem_range_self α)

/-- A nonempty control space supplies a finite competitor, even on a zero-length interval. -/
theorem control_costs_nonempty [Nonempty A] (h : E → A → ℝ) (g : E → ℝ)
    {a b : ℝ} (hab : a ≤ b) (x : E) :
    (range (fun α : ControlOn A a b ↦ J h g hab α x)).Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty A›
  exact ⟨J h g hab (ControlOn.const a b v) x, mem_range_self _⟩

/-- The same explicit lower bound holds for the value. -/
theorem control_value_lower_bound [Nonempty A] (h : E → A → ℝ) (C : NNReal)
    (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (g : E → ℝ) (m : ℝ)
    (hm : ∀ y, m ≤ g y) {a b : ℝ} (hab : a ≤ b) (x : E) :
    m - (C : ℝ) * (b - a) ≤ V h g hab x := by
  apply le_csInf (control_costs_nonempty f hf K M hK hM h g hab x)
  rintro _ ⟨α, rfl⟩
  exact control_cost_lower_bound f hf K M hK hM h C hC g m hm hab α x

/-- At zero horizon, every control has the prescribed terminal cost. -/
@[simp]
theorem control_cost_zero (h : E → A → ℝ) (g : E → ℝ) (a : ℝ)
    (α : ControlOn A a a) (x : E) : J h g le_rfl α x = g x := by
  simp only [controlCost, controlRunningCost, intervalIntegral.integral_same,
    control_response_initial, zero_add]

/-- The value at zero horizon equals the terminal cost, without a limiting argument. -/
@[simp]
theorem control_value_zero [Nonempty A] (h : E → A → ℝ) (g : E → ℝ) (a : ℝ) (x : E) :
    V h g (a := a) le_rfl x = g x := by
  have hcost : ∀ α : ControlOn A a a, J h g le_rfl α x = g x :=
    fun α ↦ control_cost_zero f hf K M hK hM h g a α x
  have hne := control_costs_nonempty f hf K M hK hM h g (a := a) le_rfl x
  apply le_antisymm
  · obtain ⟨z, hz⟩ := hne
    have hz' : z = g x := by obtain ⟨α, rfl⟩ := hz; exact hcost α
    subst z
    exact csInf_le ⟨g x, by rintro _ ⟨α, rfl⟩; exact (hcost α).ge⟩ hz
  · apply le_csInf hne
    rintro _ ⟨α, rfl⟩
    exact (hcost α).ge

/-- A whole cost splits into prefix and tail costs whenever the segment controls agree
with the whole control a.e. The intermediate state is supplied by the prefix response. -/
theorem control_cost_split (h : E → A → ℝ) (hh : Measurable (fun p : E × A ↦ h p.1 p.2))
    (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (g : E → ℝ) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (γ : ControlOn A a b) (α : ControlOn A a c) (β : ControlOn A c b) (x : E)
    (hγα : γ.1 =ᵐ[volume.restrict (Ioc a c)] α.1) (hγβ : γ.1 =ᵐ[volume.restrict (Ioc c b)] β.1) :
    J h g (hac.trans hcb) γ x = R h hac α x + J h g hcb β (X hac α x c) := by
  have hleft : EqOn (X (hac.trans hcb) γ x) (X hac α x) (Icc a c) := by
    simpa only [control_response_initial] using control_response_eqOn_segment f hf K M hK hM
        (hac.trans hcb) hac le_rfl hcb γ α x hγα
  have hright : EqOn (X (hac.trans hcb) γ x)
      (X hcb β (X hac α x c)) (Icc c b) := by
    have heq := control_response_eqOn_segment f hf K M hK hM
      (hac.trans hcb) hcb hac le_rfl γ β x hγβ
    rwa [hleft ⟨hac, le_rfl⟩] at heq
  let H : ℝ → ℝ := fun t ↦ h (X (hac.trans hcb) γ x t) (γ.1 t)
  have hwhole : IntegrableOn H (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hac.trans hcb)).1
      (intervalIntegrable_control_runningCost f hf K M hK hM h hh C hC (hac.trans hcb) γ x)
  have hl : IntervalIntegrable H volume a c := (intervalIntegrable_iff_integrableOn_Icc_of_le hac).2
      (hwhole.mono_set (fun _ ht ↦ ⟨ht.1, ht.2.trans hcb⟩))
  have hr : IntervalIntegrable H volume c b := (intervalIntegrable_iff_integrableOn_Icc_of_le hcb).2
      (hwhole.mono_set (fun _ ht ↦ ⟨hac.trans ht.1, ht.2⟩))
  have hIl : (∫ t in a..c, H t) = R h hac α x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hac]
    filter_upwards [hγα, ae_restrict_mem measurableSet_Ioc] with t heq ht
    exact congrArg₂ h (hleft ⟨ht.1.le, ht.2⟩) heq
  have hIr : (∫ t in c..b, H t) = R h hcb β (X hac α x c) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hcb]
    filter_upwards [hγβ, ae_restrict_mem measurableSet_Ioc] with t heq ht
    exact congrArg₂ h (hright ⟨ht.1.le, ht.2⟩) heq
  have hsum := intervalIntegral.integral_add_adjacent_intervals hl hr
  rw [hIl, hIr] at hsum
  change (∫ t in a..b, H t) + g (X (hac.trans hcb) γ x b) = _
  rw [← hsum, hright ⟨hcb, le_rfl⟩]
  exact add_assoc _ _ _

/-- Concatenation adds the first running cost to the restarted second total cost. -/
theorem control_cost_concat (h : E → A → ℝ) (hh : Measurable (fun p : E × A ↦ h p.1 p.2))
    (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (g : E → ℝ) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (α : ControlOn A a c) (β : ControlOn A c b) (x : E) :
    J h g (hac.trans hcb) (α.concat β) x = R h hac α x + J h g hcb β (X hac α x c) := by
  apply control_cost_split f hf K M hK hM h hh C hC g hac hcb (α.concat β) α β x
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Set.piecewise_eq_of_mem (Iic c) α.1 β.1 ht.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Set.piecewise_eq_of_notMem (Iic c) α.1 β.1 (not_le.mpr ht.1)

end HamiltonJacobi
