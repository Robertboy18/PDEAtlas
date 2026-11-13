/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm

/-!
# Oleinik's almost-everywhere one-sided slope condition

The condition is imposed almost everywhere in the three variables
`(t,x,z)`, for positive time and positive increment. It does not select
representatives on exceptional time slices. Fubini and the
measure-preserving swap put the condition in the order needed for spatial
integration.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.3(b), definition of an entropy solution, condition (ii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory

namespace PDE.Hyperbolic.ConservationLaw

/-- Evans's one-sided entropy slope bound with a nonnegative constant, condition (ii) in the
definition of an entropy solution in Evans, §3.4.3(b). Both the time and spatial variables,
including the increment, are quantified almost everywhere. -/
def HasOleinikBound (u : ℝ^2 → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ᵐ p : ℝ × ℝ × ℝ ∂volume, 0 < p.1 → 0 < p.2.2 →
    u !₂[p.1, p.2.1 + p.2.2] - u !₂[p.1, p.2.1] ≤ C * (1 + p.1⁻¹) * p.2.2

/-- Fubini puts the three-variable condition in time–increment–space
order without imposing measurable or pointwise representatives of the field. -/
theorem HasOleinikBound.ae_time_increment_space {u : ℝ^2 → ℝ} {C : ℝ} (h : HasOleinikBound u C) :
    ∀ᵐ t ∂volume, 0 < t → ∀ᵐ z ∂volume, 0 < z →
      ∀ᵐ x ∂volume, u !₂[t, x + z] - u !₂[t, x] ≤ C * (1 + t⁻¹) * z := by
  have ht : ∀ᵐ t ∂volume, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < t → 0 < p.2 →
      u !₂[t, p.1 + p.2] - u !₂[t, p.1] ≤ C * (1 + t⁻¹) * p.2 := by
    have hp := h.2
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)] at hp
    exact Measure.ae_ae_of_ae_prod hp
  filter_upwards [ht] with t htp htpos
  have hp : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      u !₂[t, p.2 + p.1] - u !₂[t, p.2] ≤ C * (1 + t⁻¹) * p.1 := by
    have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact Measure.measurePreserving_swap
    filter_upwards [hs.quasiMeasurePreserving.ae htp] with p hp using hp htpos
  rw [Measure.volume_eq_prod ℝ ℝ] at hp
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with z hz hzpos
  filter_upwards [hz] with x hx using hx hzpos

end PDE.Hyperbolic.ConservationLaw
