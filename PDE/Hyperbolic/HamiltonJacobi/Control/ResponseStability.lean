/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Restart
import PDE.Analysis.Evolution.Core.Gronwall

/-!
# Sensitivity of a controlled response to its initial state

Use the same measurable control for two initial states. The integral equations
give a scalar integral inequality for their distance, so the integral
Grönwall theorem bounds its growth by `exp (K * (t-a))`.

The control is only a.e. strongly measurable on its own interval. Integrability
of the vector field along both responses is proved from the uniform speed bound.

The estimate is the bound `|x(s) - x̂(s)| ≤ C|x - x̂|` that Evans derives from (18), (20) and
Grönwall's inequality in step 2 of his proof of the Lemma (Estimates for value function) in
§10.3.3, with the constant `exp (K * (t-a))` made explicit.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Lemma (Estimates for value function), step 2
  of the proof, equations (18)-(20); §B.2(k), Grönwall's inequality (integral form).
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

/-- Under a common control, initial-state errors grow at most exponentially
with the uniform state Lipschitz constant of the vector field. -/
theorem dist_control_response_le {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x y : E) {t : ℝ} (ht : t ∈ Icc a b) :
    dist (X hab α x t) (X hab α y t) ≤ dist x y * Real.exp ((K : ℝ) * (t - a)) := by
  have hc (z : E) : Continuous (X hab α z) :=
    (control_response_lipschitz f hf K M hK hM hab α z).continuous
  have hi (z : E) :
      IntervalIntegrable (fun s ↦ f (X hab α z s) (α.1 s)) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    apply IntegrableOn.of_bound measure_Icc_lt_top
      (hf.comp_aestronglyMeasurable ((hc z).aestronglyMeasurable.prodMk α.2)) (M : ℝ)
    exact Eventually.of_forall fun s ↦ hM (X hab α z s) (α.1 s)
  have heq (z : E) (s : ℝ) (hs : s ∈ Icc a b) :
      X hab α z s = z + ∫ r in a..s, f (X hab α z r) (α.1 r) := (Classical.choose_spec
      (exists_measurable_control_response hab f hf K M hK hM α.1 α.2 z)).2.2.2.1 s hs
  apply PDE.Analysis.Evolution.le_mul_exp_of_le_const_add_mul_intervalIntegral
    ((hc x).dist (hc y)).continuousOn K.property _ t ht
  intro s hs
  have hsub : uIcc a s ⊆ uIcc a b := by
    rw [uIcc_of_le hs.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right hs.2
  have hid := intervalIntegral.integral_sub ((hi x).mono_set hsub) ((hi y).mono_set hsub)
  have hnorm : ‖∫ r in a..s, f (X hab α x r) (α.1 r) - f (X hab α y r) (α.1 r)‖ ≤
        (K : ℝ) * ∫ r in a..s, dist (X hab α x r) (X hab α y r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hs.1
    · exact Eventually.of_forall fun r _hr ↦ by
        simpa only [← dist_eq_norm] using (hK (α.1 r)).dist_le_mul (X hab α x r) (X hab α y r)
    · exact (continuous_const.mul ((hc x).dist (hc y))).continuousOn.intervalIntegrable_of_Icc hs.1
  calc
    dist (X hab α x s) (X hab α y s) = ‖(x - y) + ∫ r in a..s,
          f (X hab α x r) (α.1 r) - f (X hab α y r) (α.1 r)‖ := by
      rw [dist_eq_norm, heq x s hs, heq y s hs, hid]
      congr 1
      abel
    _ ≤ ‖x - y‖ + ‖∫ r in a..s, f (X hab α x r) (α.1 r) - f (X hab α y r) (α.1 r)‖ :=
      norm_add_le _ _
    _ ≤ dist x y + (K : ℝ) * ∫ r in a..s, dist (X hab α x r) (X hab α y r) := by
      rw [← dist_eq_norm]
      exact add_le_add (le_refl _) hnorm

end HamiltonJacobi
