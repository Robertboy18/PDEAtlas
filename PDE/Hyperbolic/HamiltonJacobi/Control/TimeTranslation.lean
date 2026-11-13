/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Value
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Translation of autonomous control problems

Translation gives an equivalence of the admissible controls on two time
intervals. Uniqueness identifies their responses on those intervals, and a change
of variable identifies their costs. Equality of the ranges of all costs then
identifies their infima without requiring an optimal control.

The controls remain a.e. strongly measurable only on their prescribed intervals.

Evans translates controls in this way in step 3 of his proof of the Lemma (Estimates for value
function) in §10.3.3, where the response to `α̂(s) = α(s+t-t̂)` is `x(s+t-t̂)`, before (21).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Lemma (Estimates for value function), step 3
  of the proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace

namespace HamiltonJacobi

namespace ControlOn

variable {A : Type*} [TopologicalSpace A] {a b : ℝ}

/-- Translate an interval control and its time interval by the same amount. -/
def translate (a b c : ℝ) : ControlOn A a b ≃ ControlOn A (a + c) (b + c) where
  toFun α := ⟨fun t ↦ α.1 (t - c), by
    have hs : (fun t : ℝ ↦ t - c) ⁻¹' Icc a b = Icc (a + c) (b + c) := by
      ext t
      simp only [mem_preimage, mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add]
    have hm := (measurePreserving_sub_right (volume : Measure ℝ) c).restrict_preimage
      (measurableSet_Icc : MeasurableSet (Icc a b))
    rw [hs] at hm
    exact α.2.comp_measurePreserving hm⟩
  invFun β := ⟨fun t ↦ β.1 (t + c), by
    have hs : (fun t : ℝ ↦ t + c) ⁻¹' Icc (a + c) (b + c) = Icc a b := by
      ext t
      simp only [mem_preimage, mem_Icc, add_le_add_iff_right]
    have hm := (measurePreserving_add_right (volume : Measure ℝ) c).restrict_preimage
      (measurableSet_Icc : MeasurableSet (Icc (a + c) (b + c)))
    rw [hs] at hm
    exact β.2.comp_measurePreserving hm⟩
  left_inv α := by
    apply Subtype.ext
    funext t
    exact congrArg α.1 (add_sub_cancel_right t c)
  right_inv β := by
    apply Subtype.ext
    funext t
    exact congrArg β.1 (sub_add_cancel t c)

/-- The translated control reads the original control at the original time. -/
@[simp]
theorem translate_apply (c : ℝ) (α : ControlOn A a b) (t : ℝ) :
    (translate a b c α).1 t = α.1 (t - c) :=
  rfl

/-- The inverse translation reads the translated control at the translated time. -/
@[simp]
theorem translate_symm_apply (c : ℝ) (β : ControlOn A (a + c) (b + c)) (t : ℝ) :
    ((translate a b c).symm β).1 t = β.1 (t + c) :=
  rfl

end ControlOn

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

local notation "X" => controlResponse f hf K M hK hM
local notation "J" => controlCost f hf K M hK hM
local notation "V" => controlValue f hf K M hK hM

/-- Autonomous responses commute with translation on their prescribed intervals. -/
theorem control_response_translate {a b : ℝ} (hab : a ≤ b) (c : ℝ)
    (α : ControlOn A a b) (x : E) {t : ℝ} (ht : t ∈ Icc a b) :
    X (add_le_add hab (le_refl c)) (ControlOn.translate a b c α) x (t + c) = X hab α x t := by
  let v : ℝ → E := fun r ↦ X hab α x (r - c)
  have hv : LipschitzWith M v := by
    intro r s
    simpa only [v, edist_dist, Real.dist_eq, sub_sub_sub_cancel_right] using
      (control_response_lipschitz f hf K M hK hM hab α x) (r - c) (s - c)
  have hinit : v (a + c) = x := by
    simp only [v, add_sub_cancel_right, control_response_initial]
  have hs : (fun r : ℝ ↦ r - c) ⁻¹' Ioc a b = Ioc (a + c) (b + c) := by
    ext r
    simp only [mem_preimage, mem_Ioc, lt_sub_iff_add_lt, sub_le_iff_le_add]
  have hm := (measurePreserving_sub_right (volume : Measure ℝ) c).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc a b))
  rw [hs] at hm
  have hd := hm.quasiMeasurePreserving.ae (control_response_hasDerivAt_ae f hf K M hK hM hab α x)
  have heq := eqOn_control_response f hf K M hK hM (add_le_add hab (le_refl c))
    (ControlOn.translate a b c α) x v hv.lipschitzOnWith.absolutelyContinuousOnInterval
    hinit (by
      filter_upwards [hd] with r hr
      exact hr.comp_sub_const r c)
  have ht' : t + c ∈ Icc (a + c) (b + c) :=
    ⟨add_le_add ht.1 (le_refl c), add_le_add ht.2 (le_refl c)⟩
  simpa only [v, add_sub_cancel_right] using (heq ht').symm

/-- Translation preserves each cost, for arbitrary running and terminal costs. -/
theorem control_cost_translate (h : E → A → ℝ) (g : E → ℝ)
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) (α : ControlOn A a b) (x : E) :
    J h g (add_le_add hab (le_refl c)) (ControlOn.translate a b c α) x = J h g hab α x := by
  have hr : controlRunningCost f hf K M hK hM h (add_le_add hab (le_refl c))
        (ControlOn.translate a b c α) x =
      controlRunningCost f hf K M hK hM h hab α x := by
    unfold controlRunningCost
    rw [← intervalIntegral.integral_comp_add_right]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    dsimp only
    rw [control_response_translate f hf K M hK hM hab c α x ht']
    simp only [ControlOn.translate_apply, add_sub_cancel_right]
  unfold controlCost
  rw [hr, control_response_translate f hf K M hK hM hab c α x ⟨hab, le_rfl⟩]

/-- Changing both endpoint times by the same amount preserves the value. -/
theorem control_value_translate (h : E → A → ℝ) (g : E → ℝ)
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) (x : E) :
    V h g (add_le_add hab (le_refl c)) x = V h g hab x := by
  unfold controlValue
  congr 1
  ext y
  constructor
  · rintro ⟨β, rfl⟩
    refine ⟨(ControlOn.translate a b c).symm β, ?_⟩
    simpa only [Equiv.apply_symm_apply] using (control_cost_translate f hf K M hK hM h g hab c
        ((ControlOn.translate a b c).symm β) x).symm
  · rintro ⟨α, rfl⟩
    exact ⟨ControlOn.translate a b c α, control_cost_translate f hf K M hK hM h g hab c α x⟩

end HamiltonJacobi
