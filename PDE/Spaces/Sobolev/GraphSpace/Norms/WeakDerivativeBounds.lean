/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Norms
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Graph norms from distributional derivative bounds

Uniqueness of weak derivatives transfers bounds for any constructed
derivative to the stored Sobolev coordinate. Consequently, estimates do
not depend on which reconstruction theorem supplied the field.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- A derivative coordinate equals any `Lᵖ` weak derivative of
the same order and base representative on an open domain. -/
theorem wkpCoordinateCLM_eq_of_weakDerivative (hΩ : IsOpen Ω)
    (U : W^{k,p}(Ω)) (a : DerivIndex n k) (g : DerivLp n p Ω)
    (hg : HasWeakDerivativeOn Ω a.toList (baseRepresentative U) (g : ℝ^n → ℝ)) :
    wkpCoordinateCLM a U = g :=
  Lp.ext ((U.property a).unique_ae hΩ hg)

/-- Bounds for independently constructed weak first derivatives control
the first-order graph norm. -/
theorem norm_le_base_add_sum_of_weakDerivative_bounds (hΩ : IsOpen Ω)
    (U : W^{1,p}(Ω)) (B : Fin n → ℝ)
    (hB : ∀ i, ∃ g : DerivLp n p Ω, ‖g‖ ≤ B i ∧
      HasWeakDerivativeOn Ω [i] (baseRepresentative U) (g : ℝ^n → ℝ)) :
    ‖U‖ ≤ ‖wkpBaseCoordinateCLM U‖ + ∑ i, B i := by
  apply (ambient_norm_le_base_add_sum_deriv U.val).trans
  rw [wkpBaseCoordinateCLM_apply]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨g, hg, hweak⟩ := hB i
  have heq := wkpCoordinateCLM_eq_of_weakDerivative hΩ U
    (singleDerivIndex n i) g (by simpa only [singleDerivIndex_toList] using hweak)
  change ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ ≤ B i
  rw [heq]
  exact hg

end SobolevSpace.GraphSpace
