/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.ResponseStability
public import PDE.Hyperbolic.HamiltonJacobi.Control.DynamicProgramming

/-!
# Quantitative regularity of the control value

The running cost is bounded and jointly Borel measurable, and has a state Lipschitz
constant uniform in the control. The terminal cost is Lipschitz and bounded
below. Comparing responses under the same control gives a spatial bound for
each cost and then for their infimum.

The dynamic programming identity gives the time bound: during the short prefix
the state moves at most `M * (c-a)`, and the running cost contributes at most
`C * (c-a)`. This uses the constructed response and the infimum identity,
without an optimal control or a measurable selector. The estimates allow zero
Lipschitz constants and degenerate cuts.

The estimates hold on a finite terminal horizon.
The state space remains a separable real Banach space and the control space need
not be compact. The terminal trace estimate only needs a Lipschitz terminal cost:
bounded speed confines its values along every response. Bounded terminal data
also give a uniform bound for the value on each finite slab.

Together these are the Lemma (Estimates for value function) of Evans, §10.3.3, with explicit
constants. The uniform bound is step 1 of his proof and the spatial bound is step 2,
(17)-(20). In step 3 Evans obtains the time bound by translating controls, (21); we derive it
from dynamic programming and the spatial bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Lemma (Estimates for value function) and its
  proof, equations (17)-(21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace

namespace HamiltonJacobi

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

local notation "X" => controlResponse f hf K M hK hM
local notation "R" => controlRunningCost f hf K M hK hM
local notation "J" => controlCost f hf K M hK hM
local notation "V" => controlValue f hf K M hK hM

/-- The same control gives costs whose difference is bounded by the propagated
initial-state error, including the running and terminal contributions. -/
theorem abs_control_cost_sub_le (h : E → A → ℝ) (hh : Measurable (fun p : E × A ↦ h p.1 p.2))
    (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (hL : ∀ v, LipschitzWith L (fun x ↦ h x v))
    (g : E → ℝ) (G : NNReal) (hG : LipschitzWith G g) {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b)
    (x y : E) :
    |J h g hab α x - J h g hab α y| ≤
      ((L : ℝ) * (b - a) + (G : ℝ)) * Real.exp ((K : ℝ) * (b - a)) * dist x y := by
  let D := dist x y * Real.exp ((K : ℝ) * (b - a))
  have hd (t : ℝ) (ht : t ∈ Icc a b) : dist (X hab α x t) (X hab α y t) ≤ D :=
    (dist_control_response_le f hf K M hK hM hab α x y ht).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) K.property))
        (dist_nonneg))
  have hr : |R h hab α x - R h hab α y| ≤ (L : ℝ) * D * (b - a) := by
    have hi (z : E) := intervalIntegrable_control_runningCost f hf K M hK hM h hh C hC hab α z
    change |(∫ t in a..b, h (X hab α x t) (α.1 t)) - (∫ t in a..b, h (X hab α y t) (α.1 t))| ≤ _
    rw [← intervalIntegral.integral_sub (hi x) (hi y)]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := (L : ℝ) * D)
      (f := fun t ↦ h (X hab α x t) (α.1 t) - h (X hab α y t) (α.1 t))
      (fun t ht ↦ by
        rw [uIoc_of_le hab] at ht
        simpa only [Real.norm_eq_abs, ← Real.dist_eq] using
          ((hL (α.1 t)).dist_le_mul (X hab α x t) (X hab α y t)).trans
            (mul_le_mul_of_nonneg_left (hd t (Ioc_subset_Icc_self ht)) L.property))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hn
  have hg : |g (X hab α x b) - g (X hab α y b)| ≤ (G : ℝ) * D := by
    simpa only [← Real.dist_eq] using (hG.dist_le_mul (X hab α x b) (X hab α y b)).trans
        (mul_le_mul_of_nonneg_left (hd b ⟨hab, le_rfl⟩) G.property)
  calc
    |J h g hab α x - J h g hab α y| =
        |(R h hab α x - R h hab α y) + (g (X hab α x b) - g (X hab α y b))| := by
      congr 1
      dsimp only [controlCost]
      ring
    _ ≤ |R h hab α x - R h hab α y| +
        |g (X hab α x b) - g (X hab α y b)| := abs_add_le _ _
    _ ≤ (L : ℝ) * D * (b - a) + (G : ℝ) * D := add_le_add hr hg
    _ = ((L : ℝ) * (b - a) + (G : ℝ)) *
        Real.exp ((K : ℝ) * (b - a)) * dist x y := by dsimp only [D]; ring

variable [Nonempty A]

/-- Taking the infimum preserves the uniform spatial bound on costs.
The terminal lower bound justifies both real infima. -/
theorem abs_control_value_sub_le (h : E → A → ℝ) (hh : Measurable (fun p : E × A ↦ h p.1 p.2))
    (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (hL : ∀ v, LipschitzWith L (fun x ↦ h x v))
    (g : E → ℝ) (hg : BddBelow (range g)) (G : NNReal) (hG : LipschitzWith G g) {a b : ℝ}
    (hab : a ≤ b) (x y : E) :
    |V h g hab x - V h g hab y| ≤
      ((L : ℝ) * (b - a) + (G : ℝ)) * Real.exp ((K : ℝ) * (b - a)) * dist x y := by
  have hone (z w : E) : V h g hab z - ((L : ℝ) * (b - a) + (G : ℝ)) *
        Real.exp ((K : ℝ) * (b - a)) * dist z w ≤ V h g hab w := by
    apply le_csInf (control_costs_nonempty f hf K M hK hM h g hab w)
    rintro _ ⟨α, rfl⟩
    have hz := control_value_le_cost f hf K M hK hM h C hC g hg hab α z
    have hc := (abs_le.mp
      (abs_control_cost_sub_le f hf K M hK hM h hh C L hC hL g G hG hab α z w)).2
    linarith
  have hxy := hone x y
  have hyx := hone y x
  rw [dist_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The value varies Lipschitz continuously with the initial state on a fixed horizon. -/
theorem lipschitzWith_control_value (h : E → A → ℝ) (hh : Measurable (fun p : E × A ↦ h p.1 p.2))
    (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (hL : ∀ v, LipschitzWith L (fun x ↦ h x v))
    (g : E → ℝ) (hg : BddBelow (range g)) (G : NNReal) (hG : LipschitzWith G g) {a b : ℝ}
    (hab : a ≤ b) :
    LipschitzWith ⟨((L : ℝ) * (b - a) + (G : ℝ)) * Real.exp ((K : ℝ) * (b - a)),
      mul_nonneg (add_nonneg (mul_nonneg L.property (sub_nonneg.mpr hab)) G.property)
      (Real.exp_pos _).le⟩ (V h g hab) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  change dist (V h g hab x) (V h g hab y) ≤
    (((L : ℝ) * (b - a) + (G : ℝ)) * Real.exp ((K : ℝ) * (b - a))) * dist x y
  simpa only [Real.dist_eq] using
    abs_control_value_sub_le f hf K M hK hM h hh C L hC hL g hg G hG hab x y

/-- Starting later changes the value by at most the short running cost plus
the tail value's spatial modulus times the distance traveled during that prefix.
This follows from the dynamic programming identity for every closed cut. -/
theorem abs_control_value_time_sub_le (h : E → A → ℝ) (hh : Measurable (fun p : E × A ↦ h p.1 p.2))
    (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (hL : ∀ v, LipschitzWith L (fun x ↦ h x v))
    (g : E → ℝ) (hg : BddBelow (range g)) (G : NNReal) (hG : LipschitzWith G g) {a b c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (x : E) :
    |V h g (hac.trans hcb) x - V h g hcb x| ≤ ((C : ℝ) + ((L : ℝ) * (b - c) + (G : ℝ)) *
      Real.exp ((K : ℝ) * (b - c)) * (M : ℝ)) * (c - a) := by
  let B := ((L : ℝ) * (b - c) + (G : ℝ)) * Real.exp ((K : ℝ) * (b - c))
  let d := ((C : ℝ) + B * (M : ℝ)) * (c - a)
  let S : Set ℝ := range (fun α : ControlOn A a c ↦ R h hac α x + V h g hcb (X hac α x c))
  have hB : 0 ≤ B := mul_nonneg (add_nonneg (mul_nonneg L.property (sub_nonneg.mpr hcb)) G.property)
      (Real.exp_pos _).le
  have hbound (α : ControlOn A a c) :
      |R h hac α x + V h g hcb (X hac α x c) - V h g hcb x| ≤ d := by
    have hx : dist (X hac α x c) x ≤ (M : ℝ) * (c - a) := by
      have hx' := (control_response_lipschitz f hf K M hK hM hac α x).dist_le_mul c a
      simpa only [control_response_initial, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hac)] using hx'
    have hv := (abs_control_value_sub_le f hf K M hK hM
      h hh C L hC hL g hg G hG hcb (X hac α x c) x).trans (mul_le_mul_of_nonneg_left hx hB)
    have hr := abs_control_runningCost_le f hf K M hK hM h C hC hac α x
    calc
      |R h hac α x + V h g hcb (X hac α x c) - V h g hcb x| =
          |R h hac α x + (V h g hcb (X hac α x c) - V h g hcb x)| := by
        rw [add_sub_assoc]
      _ ≤ |R h hac α x| + |V h g hcb (X hac α x c) - V h g hcb x| := abs_add_le _ _
      _ ≤ (C : ℝ) * (c - a) + B * ((M : ℝ) * (c - a)) := add_le_add hr hv
      _ = d := by dsimp only [d]; ring
  have hne : S.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty A›
    exact ⟨_, mem_range_self (ControlOn.const a c v)⟩
  have hlower : ∀ z ∈ S, V h g hcb x - d ≤ z := by
    rintro _ ⟨α, rfl⟩
    have hz := (abs_le.mp (hbound α)).1
    linarith
  have hl : V h g hcb x - d ≤ sInf S := le_csInf hne hlower
  have hu : sInf S ≤ V h g hcb x + d := by
    obtain ⟨v⟩ := ‹Nonempty A›
    have hi : sInf S ≤ R h hac (ControlOn.const a c v) x +
        V h g hcb (X hac (ControlOn.const a c v) x c) :=
      csInf_le ⟨V h g hcb x - d, hlower⟩ (mem_range_self (ControlOn.const a c v))
    have hz := (abs_le.mp (hbound (ControlOn.const a c v))).2
    linarith
  have hdpp := control_value_dynamic_programming f hf K M hK hM h hh C hC g hg hac hcb x
  change V h g (hac.trans hcb) x = sInf S at hdpp
  rw [hdpp]
  change |sInf S - V h g hcb x| ≤ d
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The terminal value is approached uniformly in the state, with an explicit linear
error bound, including zero horizon. The costs lie in this interval before their
infimum is taken; no global lower bound on the terminal cost is needed. -/
theorem abs_control_value_sub_terminal_le (h : E → A → ℝ) (C : NNReal)
    (hC : ∀ x v, |h x v| ≤ (C : ℝ)) (g : E → ℝ) (G : NNReal) (hG : LipschitzWith G g)
    {a b : ℝ} (hab : a ≤ b) (x : E) :
    |V h g hab x - g x| ≤ ((C : ℝ) + (G : ℝ) * (M : ℝ)) * (b - a) := by
  let d := ((C : ℝ) + (G : ℝ) * (M : ℝ)) * (b - a)
  have hbound (α : ControlOn A a b) : |J h g hab α x - g x| ≤ d := by
    have hx : dist (X hab α x b) x ≤ (M : ℝ) * (b - a) := by
      simpa only [control_response_initial, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)] using
        (control_response_lipschitz f hf K M hK hM hab α x).dist_le_mul b a
    have hg : |g (X hab α x b) - g x| ≤ (G : ℝ) * ((M : ℝ) * (b - a)) := by
      simpa only [← Real.dist_eq] using
        (hG.dist_le_mul (X hab α x b) x).trans (mul_le_mul_of_nonneg_left hx G.property)
    have hr := abs_control_runningCost_le f hf K M hK hM h C hC hab α x
    calc
      |J h g hab α x - g x| = |R h hab α x + (g (X hab α x b) - g x)| := by
        rw [controlCost, add_sub_assoc]
      _ ≤ |R h hab α x| + |g (X hab α x b) - g x| := abs_add_le _ _
      _ ≤ (C : ℝ) * (b - a) + (G : ℝ) * ((M : ℝ) * (b - a)) := add_le_add hr hg
      _ = d := by dsimp only [d]; ring
  have hlower : ∀ z ∈ range (fun α : ControlOn A a b ↦ J h g hab α x), g x - d ≤ z := by
    rintro _ ⟨α, rfl⟩
    have hz := (abs_le.mp (hbound α)).1
    linarith
  have hl : g x - d ≤ V h g hab x :=
    le_csInf (control_costs_nonempty f hf K M hK hM h g hab x) hlower
  obtain ⟨v⟩ := ‹Nonempty A›
  have hu : V h g hab x ≤ J h g hab (ControlOn.const a b v) x :=
    csInf_le ⟨g x - d, hlower⟩ (mem_range_self (ControlOn.const a b v))
  have hz := (abs_le.mp (hbound (ControlOn.const a b v))).2
  change |V h g hab x - g x| ≤ d
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Bounded running and terminal costs bound the value uniformly in the state.
Only a nonempty control space is needed to supply a competitor. -/
theorem abs_control_value_le (h : E → A → ℝ) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (g : E → ℝ) (D : NNReal) (hg : ∀ x, |g x| ≤ (D : ℝ)) {a b : ℝ} (hab : a ≤ b) (x : E) :
    |V h g hab x| ≤ (C : ℝ) * (b - a) + (D : ℝ) := by
  have hgb : BddBelow (range g) := by
    refine ⟨-(D : ℝ), ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (abs_le.mp (hg y)).1
  have hl := control_value_lower_bound f hf K M hK hM h C hC g (-(D : ℝ))
    (fun y ↦ (abs_le.mp (hg y)).1) hab x
  obtain ⟨v⟩ := ‹Nonempty A›
  have hu := control_value_le_cost f hf K M hK hM h C hC g hgb hab (ControlOn.const a b v) x
  have hr := (abs_le.mp
    (abs_control_runningCost_le f hf K M hK hM h C hC hab (ControlOn.const a b v) x)).2
  have ht := (abs_le.mp (hg (X hab (ControlOn.const a b v) x b))).2
  dsimp only [controlCost] at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- On each finite closed terminal slab the value is jointly Lipschitz in
state and starting time. The time coordinate is a subtype, so its upper endpoint
supplies the proof needed to evaluate the value on that horizon. -/
theorem lipschitzWith_control_value_slab (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (hg : BddBelow (range g)) (G : NNReal)
    (hG : LipschitzWith G g) {a b : ℝ} (hab : a ≤ b) :
    LipschitzWith (Real.toNNReal ((1 + (M : ℝ)) * ((L : ℝ) * (b - a) + (G : ℝ)) *
      Real.exp ((K : ℝ) * (b - a)) + (C : ℝ))) (fun z : E × Icc a b ↦ V h g z.2.2.2 z.1) := by
  let B := ((L : ℝ) * (b - a) + (G : ℝ)) * Real.exp ((K : ℝ) * (b - a))
  have hB : 0 ≤ B := mul_nonneg (add_nonneg (mul_nonneg L.property (sub_nonneg.mpr hab)) G.property)
      (Real.exp_pos _).le
  have hmono (t : Icc a b) : ((L : ℝ) * (b - t.1) + (G : ℝ)) *
        Real.exp ((K : ℝ) * (b - t.1)) ≤ B := by
    apply mul_le_mul
    · exact add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub_left t.2.1 b) L.property) (le_refl _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_left t.2.1 b) K.property)
    · exact (Real.exp_pos _).le
    · exact add_nonneg (mul_nonneg L.property (sub_nonneg.mpr hab)) G.property
  have hordered (z w : E × Icc a b) (hzw : z.2.1 ≤ w.2.1) :
      dist (V h g z.2.2.2 z.1) (V h g w.2.2.2 w.1) ≤
        (B + ((C : ℝ) + B * (M : ℝ))) * dist z w := by
    have hs : dist (V h g z.2.2.2 z.1) (V h g z.2.2.2 w.1) ≤ B * dist z.1 w.1 := by
      rw [Real.dist_eq]
      exact (abs_control_value_sub_le f hf K M hK hM h hh C L hC hL g hg G hG z.2.2.2 z.1 w.1).trans
          (mul_le_mul_of_nonneg_right (hmono z.2) dist_nonneg)
    have ht : dist (V h g z.2.2.2 w.1) (V h g w.2.2.2 w.1) ≤
        ((C : ℝ) + B * (M : ℝ)) * (w.2.1 - z.2.1) := by
      rw [Real.dist_eq]
      exact (abs_control_value_time_sub_le f hf K M hK hM
        h hh C L hC hL g hg G hG hzw w.2.2.2 w.1).trans (mul_le_mul_of_nonneg_right
            (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (hmono w.2) M.property))
            (sub_nonneg.mpr hzw))
    have hspace : dist z.1 w.1 ≤ dist z w := le_max_left _ _
    have htime : w.2.1 - z.2.1 ≤ dist z w := by
      have heq : w.2.1 - z.2.1 = dist z.2 w.2 := by
        change w.2.1 - z.2.1 = |z.2.1 - w.2.1|
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hzw)]
      rw [heq]
      exact le_max_right _ _
    calc
      dist (V h g z.2.2.2 z.1) (V h g w.2.2.2 w.1) ≤ dist (V h g z.2.2.2 z.1) (V h g z.2.2.2 w.1) +
            dist (V h g z.2.2.2 w.1) (V h g w.2.2.2 w.1) := dist_triangle _ _ _
      _ ≤ B * dist z.1 w.1 + ((C : ℝ) + B * (M : ℝ)) * (w.2.1 - z.2.1) := add_le_add hs ht
      _ ≤ B * dist z w + ((C : ℝ) + B * (M : ℝ)) * dist z w :=
        add_le_add (mul_le_mul_of_nonneg_left hspace hB) (mul_le_mul_of_nonneg_left htime
            (add_nonneg C.property (mul_nonneg hB M.property)))
      _ = (B + ((C : ℝ) + B * (M : ℝ))) * dist z w := by ring
  refine LipschitzWith.of_dist_le' fun z w ↦ ?_
  have hc : B + ((C : ℝ) + B * (M : ℝ)) = (1 + (M : ℝ)) * ((L : ℝ) * (b - a) + (G : ℝ)) *
          Real.exp ((K : ℝ) * (b - a)) + (C : ℝ) := by dsimp only [B]; ring
  rcases le_total z.2.1 w.2.1 with hzw | hwz
  · simpa only [hc] using hordered z w hzw
  · simpa only [dist_comm, hc] using hordered w z hwz

end HamiltonJacobi
