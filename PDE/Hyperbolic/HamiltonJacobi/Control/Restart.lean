/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Response

/-!
# Restarting a response and concatenating controls

A control is required to be a.e. strongly measurable only on its time interval.
The response is chosen from the Carathéodory construction. Uniqueness identifies
its restriction with the response restarted from the intermediate state.

Concatenation assigns the cut to the first control. Its response is constructed on the whole
interval and identified on each segment by uniqueness. All intervals may be degenerate.

These are the concatenated control (11) and the identification (13) of its response that Evans
uses in step 1 of his proof of Theorem 1 in §10.3.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.2, step 1 of the proof of Theorem 1, equations
  (11)-(13).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Topology

namespace HamiltonJacobi

/-- A control with the measurability needed on the prescribed time interval.
Values outside that interval, or on a null set, need not be measurable. -/
abbrev ControlOn (A : Type*) [TopologicalSpace A] (a b : ℝ) :=
  {α : ℝ → A // AEStronglyMeasurable α (volume.restrict (Icc a b))}

namespace ControlOn

variable {A : Type*} [TopologicalSpace A] {a b c d : ℝ}

/-- A fixed control value is admissible on every interval. -/
def const (a b : ℝ) (v : A) : ControlOn A a b :=
  ⟨fun _ ↦ v, aestronglyMeasurable_const⟩

/-- Restriction keeps the same function and requires measurability on a smaller set. -/
def restrict (α : ControlOn A a b) (hac : a ≤ c) (hdb : d ≤ b) : ControlOn A c d :=
  ⟨α.1, AEStronglyMeasurable.mono_set
    (fun (r : ℝ) (ht : r ∈ Icc c d) ↦
      show r ∈ Icc a b from ⟨hac.trans ht.1, ht.2.trans hdb⟩) α.2⟩

/-- Use the first control through the cut and the second strictly afterwards. -/
def concat (α : ControlOn A a c) (β : ControlOn A c b) : ControlOn A a b := by
  classical
  refine ⟨(Iic c).piecewise α.1 β.1, ?_⟩
  apply AEStronglyMeasurable.piecewise measurableSet_Iic.nullMeasurableSet
  · rw [Measure.restrict_restrict measurableSet_Iic]
    apply AEStronglyMeasurable.mono_set _ α.2
    exact fun _ ht ↦ ⟨ht.2.1, ht.1⟩
  · rw [Measure.restrict_restrict measurableSet_Iic.compl]
    apply AEStronglyMeasurable.mono_set _ β.2
    exact fun (r : ℝ) ht ↦ ⟨(lt_of_not_ge (show ¬ r ≤ c from ht.1)).le, ht.2.2⟩

end ControlOn

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

/-- The response furnished by the measurable-control existence theorem.
Its values on the prescribed interval are independent of this choice, by uniqueness. -/
def controlResponse {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) : ℝ → E :=
  Classical.choose (exists_measurable_control_response hab f hf K M hK hM α.1 α.2 x)

local notation "X" => controlResponse f hf K M hK hM

/-- The uniform speed bound controls the distance between any two response values. -/
theorem control_response_lipschitz {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x : E) : LipschitzWith M (X hab α x) :=
  (Classical.choose_spec (exists_measurable_control_response hab f hf K M hK hM α.1 α.2 x)).1

/-- The constructed response attains the prescribed initial state pointwise. -/
@[simp]
theorem control_response_initial {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x : E) : X hab α x a = x :=
  (Classical.choose_spec (exists_measurable_control_response hab f hf K M hK hM α.1 α.2 x)).2.1

/-- The differential equation holds a.e. for the supplied control, without replacing it. -/
theorem control_response_hasDerivAt_ae {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt (X hab α x) (f (X hab α x t) (α.1 t)) t :=
  (Classical.choose_spec (exists_measurable_control_response hab f hf K M hK hM α.1 α.2 x)).2.2.1

/-- An absolutely continuous solution with the same initial data equals the response. -/
theorem eqOn_control_response {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) (v : ℝ → E)
    (hv : AbsolutelyContinuousOnInterval v a b) (hva : v a = x)
    (hdv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt v (f (v t) (α.1 t)) t) :
    EqOn v (X hab α x) (Icc a b) :=
  (Classical.choose_spec (exists_measurable_control_response hab f hf K M hK hM α.1 α.2 x)).2.2.2.2
      v hv hva hdv

/-- On a smaller interval, a response restarts from its intermediate state.
The smaller control may differ from the original on a null set. -/
theorem control_response_eqOn_segment {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) (α : ControlOn A a b) (β : ControlOn A c d)
    (x : E) (hαβ : α.1 =ᵐ[volume.restrict (Ioc c d)] β.1) :
    EqOn (X hab α x) (X hcd β (X hab α x c)) (Icc c d) := by
  have hv : AbsolutelyContinuousOnInterval (X hab α x) c d := (LipschitzWith.lipschitzOnWith
      (control_response_lipschitz f hf K M hK hM hab α x)).absolutelyContinuousOnInterval
  apply eqOn_control_response f hf K M hK hM hcd β (X hab α x c) (X hab α x) hv rfl
  have hd : ∀ᵐ t ∂volume.restrict (Ioc c d), HasDerivAt (X hab α x) (f (X hab α x t) (α.1 t)) t :=
    (control_response_hasDerivAt_ae f hf K M hK hM hab α x).filter_mono
      (MeasureTheory.ae_mono ((volume : Measure ℝ).restrict_mono_set
        (fun (r : ℝ) (ht : r ∈ Ioc c d) ↦
          show r ∈ Ioc a b from ⟨lt_of_le_of_lt hac ht.1, ht.2.trans hdb⟩)))
  filter_upwards [hd, hαβ] with t ht heq
  simpa only [← heq] using ht

/-- Restarting with the restriction of the original control preserves the trajectory. -/
theorem control_response_restart {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) (α : ControlOn A a b) (x : E) :
    EqOn (X hab α x) (X hcd (α.restrict hac hdb) (X hab α x c)) (Icc c d) :=
  control_response_eqOn_segment f hf K M hK hM hab hcd hac hdb α
    (α.restrict hac hdb) x (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- The response to a concatenated control agrees with the first response through the cut. -/
theorem control_response_concat_left {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (α : ControlOn A a c) (β : ControlOn A c b) (x : E) :
    EqOn (X (hac.trans hcb) (α.concat β) x) (X hac α x) (Icc a c) := by
  have heq := control_response_eqOn_segment f hf K M hK hM
    (hac.trans hcb) hac le_rfl hcb (α.concat β) α x (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Set.piecewise_eq_of_mem (Iic c) α.1 β.1 ht.2)
  simpa only [control_response_initial] using heq

/-- After the cut, the second response starts at the state reached by the first. -/
theorem control_response_concat_right {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (α : ControlOn A a c) (β : ControlOn A c b) (x : E) :
    EqOn (X (hac.trans hcb) (α.concat β) x) (X hcb β (X hac α x c)) (Icc c b) := by
  have heq := control_response_eqOn_segment f hf K M hK hM
    (hac.trans hcb) hcb hac le_rfl (α.concat β) β x (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Set.piecewise_eq_of_notMem (Iic c) α.1 β.1 (not_le.mpr ht.1))
  rw [control_response_concat_left f hf K M hK hM hac hcb α β x ⟨hac, le_rfl⟩] at heq
  exact heq

end HamiltonJacobi
