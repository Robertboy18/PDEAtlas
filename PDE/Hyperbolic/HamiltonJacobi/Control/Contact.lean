/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.TestDynamics
public import PDE.Hyperbolic.HamiltonJacobi.Control.DynamicProgramming

/-!
# The control value satisfies local C¹ contact inequalities

Reverse time by setting `W(x,t) = V[-t,0](x)` for `t ≥ 0`. At an upper contact,
a constant control and dynamic programming force every test rate to be
nonnegative. At a lower contact, a positive lower bound for all rates would
give a positive cost increment for every short control, contradicting the
same infimum identity.

The lower-contact argument uses a uniform estimate over controls, not an
optimal control. The terminal cost need only be bounded below for these
inequalities; boundedness and Lipschitz continuity enter the initial-value
regularity theorem separately.

The two contact arguments are steps 2 and 3 of Evans's proof of Theorem 2 in §10.3.3,
equations (26)-(33) and (34)-(40). The time reversal is his Remark (iii) after that theorem:
the forward Hamiltonian is the negative of the terminal Hamiltonian (23).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Theorem 2, Remarks (i) and (iii), and steps 2-3
  of the proof, equations (23) and (26)-(40).
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
local notation "V" => controlValue f hf K M hK hM

/-- The finite-horizon value in forward time, with fixed terminal time zero.
For negative forward times the horizon is zero. This extension makes a total
function without changing the initial datum or the positive-time equation. -/
def controlInitialValue (h : E → A → ℝ) (g : E → ℝ) (z : E × ℝ) : ℝ :=
  V h g (a := -max z.2 0) (b := 0) (neg_nonpos.mpr (le_max_right _ _)) z.1

local notation "W" => controlInitialValue f hf K M hK hM

/-- At forward time zero the horizon vanishes and the value is the terminal cost. -/
@[simp]
theorem control_initialValue_initial (h : E → A → ℝ) (g : E → ℝ) (x : E) :
    W h g (x, 0) = g x := by
  simp only [controlInitialValue, max_self, neg_zero, control_value_zero]

/-- Dynamic programming for the time-reversed value, with the response still
parametrized by physical time. Both endpoints of a cut are allowed. -/
theorem control_initialValue_dynamic_programming (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (g : E → ℝ) (hg : BddBelow (range g)) {a c : ℝ} (hac : a ≤ c) (hc : c ≤ 0) (x : E) :
    W h g (x, -a) = sInf (range (fun α : ControlOn A a c ↦
      R h hac α x + W h g (X hac α x c, -c))) := by
  simp only [controlInitialValue, max_eq_left (neg_nonneg.mpr (hac.trans hc)),
    max_eq_left (neg_nonneg.mpr hc), neg_neg]
  exact control_value_dynamic_programming f hf K M hK hM h hh C hC g hg hac hc x

/-- Prefix costs are bounded below before their real infimum is used.
The running costs on the two segments have a common bound. -/
private theorem bddBelow_reversed_prefix_costs (h : E → A → ℝ) (C : NNReal)
    (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (g : E → ℝ) (hg : BddBelow (range g)) {a c : ℝ} (hac : a ≤ c)
    (hc : c ≤ 0) (x : E) :
    BddBelow (range (fun α : ControlOn A a c ↦ R h hac α x + W h g (X hac α x c, -c))) := by
  obtain ⟨m, hm⟩ := hg
  refine ⟨m - (C : ℝ) * (0 - a), ?_⟩
  rintro _ ⟨α, rfl⟩
  have hr := (abs_le.mp (abs_control_runningCost_le f hf K M hK hM h C hC hac α x)).1
  have ht := control_value_lower_bound f hf K M hK hM h C hC g m
    (fun y ↦ hm (mem_range_self y)) hc (X hac α x c)
  simp only [controlInitialValue, max_eq_left (neg_nonneg.mpr hc), neg_neg]
  nlinarith only [hr, ht]

/-- An upper contact forces the reversed test rate to be nonnegative for
every constant control. Continuity in the state for each fixed control suffices;
the cost may be discontinuous in the control variable. -/
theorem control_initialValue_upper_contact (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hstate : ∀ v, Continuous (fun x ↦ h x v)) (g : E → ℝ) (hg : BddBelow (range g)) {z : E × ℝ}
    (hz : 0 < z.2) {φ : E × ℝ → ℝ} (hφ : ContDiffAt ℝ 1 φ z)
    (hmax : IsLocalMax (fun w ↦ W h g w - φ w) z) (v : A) :
    0 ≤ fderiv ℝ φ z (f z.1 v, -1) + h z.1 v := by
  by_contra! hneg
  let r := fderiv ℝ φ z (f z.1 v, -1) + h z.1 v
  obtain ⟨U, hUz, hφU⟩ := hφ.contDiffOn le_rfl (by simp)
  obtain ⟨B, hBU, hB, hzB⟩ := mem_nhds_iff.mp hUz
  have hD : ContinuousAt (fderiv ℝ φ) z :=
    ((hφU.mono hBU).continuousOn_fderiv_of_isOpen hB le_rfl).continuousAt (hB.mem_nhds hzB)
  have hf' : Continuous (fun w : E × ℝ ↦ f w.1 v) :=
    hf.comp (continuous_fst.prodMk continuous_const)
  have hh' : Continuous (fun w : E × ℝ ↦ h w.1 v) := (hstate v).comp continuous_fst
  have hr : ContinuousAt (fun w ↦ fderiv ℝ φ w (f w.1 v, -1) + h w.1 v) z :=
    (((ContinuousLinearMap.id ℝ ((E × ℝ) →L[ℝ] ℝ)).continuous₂.continuousAt).comp
      (hD.prodMk (hf'.continuousAt.prodMk continuousAt_const))).add hh'.continuousAt
  have he : ∀ᶠ w in 𝓝 z, fderiv ℝ φ w (f w.1 v, -1) + h w.1 v < r / 2 :=
    hr.eventually (gt_mem_nhds (by dsimp only [r]; linarith only [hneg]))
  have hc : ∀ᶠ w in 𝓝 z, W h g w - φ w ≤ W h g z - φ z := hmax
  let N := {w | w ∈ B ∧ W h g w - φ w ≤ W h g z - φ z ∧
    fderiv ℝ φ w (f w.1 v, -1) + h w.1 v < r / 2}
  have hN : N ∈ 𝓝 z := Filter.inter_mem (hB.mem_nhds hzB) (hc.and he)
  obtain ⟨c, hac, hc0, hstay⟩ :=
    exists_short_control_response_reverse_mem f hf K M hK hM (neg_lt_zero.mpr hz) z.1
      (by simpa only [neg_neg, Prod.mk.eta] using hN)
  let α := ControlOn.const (-z.2) c v
  have himage (s : ℝ) (hs : s ∈ Icc (-z.2) c) : (X hac.le α z.1 s, -s) ∈ B := (hstay α s hs).1
  have hi := intervalIntegrable_control_test_rate f hf K M hK hM
    h hh C hC hac.le α z.1 hB (hφU.mono hBU) himage
  have hint := intervalIntegral.integral_mono_on hac.le hi
    (intervalIntegrable_const (c := r / 2)) (fun s hs ↦ (hstay α s hs).2.2.le)
  have heq := control_response_test_increment f hf K M hK hM
    h hh C hC hac.le α z.1 hB (hφU.mono hBU) himage
  have hend := (hstay α c ⟨hac.le, le_rfl⟩).2.1
  have hp : W h g z ≤ R h hac.le α z.1 + W h g (X hac.le α z.1 c, -c) := by
    have hdpp := control_initialValue_dynamic_programming f hf K M hK hM
      h hh C hC g hg hac.le hc0.le z.1
    simp only [neg_neg, Prod.mk.eta] at hdpp
    rw [hdpp]
    exact csInf_le (bddBelow_reversed_prefix_costs f hf K M hK hM h C hC g hg hac.le hc0.le z.1)
      (mem_range_self α)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hint
  simp only [neg_neg, Prod.mk.eta] at heq
  have hstrict : (c - -z.2) * (r / 2) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hac) (div_neg_of_neg_of_pos hneg zero_lt_two)
  linarith only [hint, heq, hend, hp, hstrict]

/-- At a lower contact the infimum of the reversed test rates is nonpositive.
A putative positive infimum supplies a common positive margin on a short
interval. Integrating that margin for every control contradicts dynamic
programming, so no minimizing control or compact control set is required. -/
theorem control_initialValue_lower_contact (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (hg : BddBelow (range g)) {z : E × ℝ}
    (hz : 0 < z.2) {φ : E × ℝ → ℝ} (hφ : ContDiffAt ℝ 1 φ z)
    (hmin : IsLocalMin (fun w ↦ W h g w - φ w) z) :
    sInf (range (fun v ↦ fderiv ℝ φ z (f z.1 v, -1) + h z.1 v)) ≤ 0 := by
  let r : A → ℝ := fun v ↦ fderiv ℝ φ z (f z.1 v, -1) + h z.1 v
  have hbdd : BddBelow (range r) := by
    refine ⟨-(‖fderiv ℝ φ z‖ * ((M : ℝ) + 1) + (C : ℝ)), ?_⟩
    rintro _ ⟨v, rfl⟩
    apply (abs_le.mp (?_ : |r v| ≤ _)).1
    apply (abs_add_le _ _).trans
    apply add_le_add _ (hC z.1 v)
    apply ((fderiv ℝ φ z).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Prod.norm_mk, norm_neg, norm_one]
    exact max_le ((hM _ _).trans (le_add_of_nonneg_right zero_le_one))
      (le_add_of_nonneg_left M.property)
  by_contra! hpos
  let m := sInf (range r)
  have hm : 0 < m := hpos
  have hr (v : A) : m ≤ r v := csInf_le hbdd (mem_range_self v)
  have he := eventually_control_test_rate f h K M L hK hM hL hφ (half_pos hm)
  have hc : ∀ᶠ w in 𝓝 z, W h g z - φ z ≤ W h g w - φ w := hmin
  obtain ⟨U, hUz, hφU⟩ := hφ.contDiffOn le_rfl (by simp)
  obtain ⟨B, hBU, hB, hzB⟩ := mem_nhds_iff.mp hUz
  let N := {w | w ∈ B ∧ W h g z - φ z ≤ W h g w - φ w ∧
    ∀ v, |(fderiv ℝ φ w (f w.1 v, -1) + h w.1 v) - r v| < m / 2}
  have hN : N ∈ 𝓝 z := Filter.inter_mem (hB.mem_nhds hzB) (hc.and he)
  obtain ⟨c, hac, hc0, hstay⟩ :=
    exists_short_control_response_reverse_mem f hf K M hK hM (neg_lt_zero.mpr hz) z.1
      (by simpa only [neg_neg, Prod.mk.eta] using hN)
  have hbound (α : ControlOn A (-z.2) c) : W h g z + (c - -z.2) * (m / 2) ≤
        R h hac.le α z.1 + W h g (X hac.le α z.1 c, -c) := by
    have himage (s : ℝ) (hs : s ∈ Icc (-z.2) c) : (X hac.le α z.1 s, -s) ∈ B := (hstay α s hs).1
    have hi := intervalIntegrable_control_test_rate f hf K M hK hM
      h hh C hC hac.le α z.1 hB (hφU.mono hBU) himage
    have hint := intervalIntegral.integral_mono_on hac.le
      (intervalIntegrable_const (c := m / 2)) hi (fun s hs ↦ by
        have hd := (abs_lt.mp ((hstay α s hs).2.2 (α.1 s))).1
        have hb := hr (α.1 s)
        linarith only [hd, hb])
    have heq := control_response_test_increment f hf K M hK hM
      h hh C hC hac.le α z.1 hB (hφU.mono hBU) himage
    have hend := (hstay α c ⟨hac.le, le_rfl⟩).2.1
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hint
    simp only [neg_neg, Prod.mk.eta] at heq
    linarith only [hint, heq, hend]
  have hdpp := control_initialValue_dynamic_programming f hf K M hK hM
    h hh C hC g hg hac.le hc0.le z.1
  simp only [neg_neg, Prod.mk.eta] at hdpp
  have hstrict := mul_pos (sub_pos.mpr hac) (half_pos hm)
  have hlt : sInf (range (fun α : ControlOn A (-z.2) c ↦
      R h hac.le α z.1 + W h g (X hac.le α z.1 c, -c))) <
      W h g z + (c - -z.2) * (m / 2) := by
    rw [← hdpp]
    exact lt_add_of_pos_right _ hstrict
  obtain ⟨q, ⟨α, rfl⟩, hα⟩ := exists_lt_of_csInf_lt (by
    obtain ⟨v⟩ := ‹Nonempty A›
    exact ⟨_, mem_range_self (ControlOn.const (-z.2) c v)⟩) hlt
  exact (not_lt_of_ge (hbound α)) hα

end HamiltonJacobi
