/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.LowerBounded
public import PDE.Common.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# A concrete class whose energies are all infinite

On `(0,1)`, each density `1/x + ‖u‖² - 2`, parametrized by `u ∈ ℝ²`, has a
finite negative part and infinite positive part. Its signed energy is `+∞` for
every `u`, so every parameter minimizes it over every class.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped ENNReal

namespace PDE.Examples.VariationalSystems

/-- For every `u`, the signed energy of `1/x + ‖u‖² - 2` on `(0,1)` is `⊤`. -/
theorem singular_energy_eq_top (u : ℝ^2) :
    lowerBoundedIntegral (volume.restrict (Ioo (0 : ℝ) 1))
      (fun x ↦ x⁻¹ + ‖u‖ ^ 2 - 2) = ⊤ := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ x⁻¹ + ‖u‖ ^ 2 - 2) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((measurable_id.inv.add_const _).sub_const _).aestronglyMeasurable
  have hlower : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      -(2 : ℝ) ≤ x⁻¹ + ‖u‖ ^ 2 - 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    linarith [inv_nonneg.mpr hx.1.le, sq_nonneg ‖u‖]
  apply (lowerBoundedIntegral_eq_top_iff hmeas (integrable_const 2) hlower).mpr
  by_contra hfinite
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ x⁻¹ + ‖u‖ ^ 2 - 2 + 2 := hlower.mono fun _ hx ↦ by linarith
  have hi := (lintegral_ofReal_ne_top_iff_integrable
    (hmeas.add aestronglyMeasurable_const) hnonneg).mp hfinite
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioo (0 : ℝ) 1) := by
    have hsub : Integrable (fun x : ℝ ↦ (x⁻¹ + ‖u‖ ^ 2 - 2 + 2) - ‖u‖ ^ 2)
        (volume.restrict (Ioo (0 : ℝ) 1)) := hi.sub (integrable_const (‖u‖ ^ 2))
    simpa only [IntegrableOn, sub_add_cancel, add_sub_cancel_right] using hsub
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) := by
    simpa only [Real.rpow_neg_one] using hinv
  exact (lt_irrefl (-1 : ℝ))
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hpow)

/-- Every parameter `u` minimizes the energy over every class `A`. -/
theorem singular_energy_isMinOn {A : Set (ℝ^2)} (u : ℝ^2) :
    IsMinOn (fun v ↦ lowerBoundedIntegral (volume.restrict (Ioo (0 : ℝ) 1))
      (fun x ↦ x⁻¹ + ‖v‖ ^ 2 - 2)) A u := by
  intro v _
  change lowerBoundedIntegral _ _ ≤ lowerBoundedIntegral _ _
  simp only [singular_energy_eq_top, le_refl]

end PDE.Examples.VariationalSystems
