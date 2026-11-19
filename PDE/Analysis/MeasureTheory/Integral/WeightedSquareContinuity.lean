/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Continuity of weighted square integrals

An integrable bound on squared differences from one fixed slice gives a common
majorant for all weighted squares. Dominated convergence then makes their
integrals continuous in the parameter. The domain and measure are arbitrary.
-/

@[expose] public noncomputable section

open Filter Set

namespace MeasureTheory

/-- Continuous slices with an integrable weighted square-difference bound have
continuous weighted square integrals on any measurable domain. -/
theorem continuous_setIntegral_sq_mul_of_difference_bound
    {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (a : ι) (v : ι → X → ℝ) (W M : X → ℝ)
    (hi : ∀ τ, IntegrableOn (fun x ↦ v τ x ^ 2 * W x) s μ)
    (hc : ∀ x ∈ s, Continuous (fun τ ↦ v τ x))
    (hW : ∀ x ∈ s, 0 ≤ W x)
    (hM : IntegrableOn M s μ)
    (hd : ∀ τ x, x ∈ s → (v τ x - v a x) ^ 2 * W x ≤ M x) :
    Continuous (fun τ ↦ ∫ x in s, v τ x ^ 2 * W x ∂μ) := by
  apply continuous_of_dominated (bound := fun x ↦ 2 * (v a x ^ 2 * W x) + 2 * M x)
    (fun τ ↦ (hi τ).aestronglyMeasurable)
  · intro τ
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hW x hx))]
    have hsq : v τ x ^ 2 ≤ 2 * v a x ^ 2 + 2 * (v τ x - v a x) ^ 2 := by
      nlinarith [sq_nonneg (v τ x - 2 * v a x)]
    have hm := mul_le_mul_of_nonneg_right hsq (hW x hx)
    linarith [hd τ x hx]
  · exact ((hi a).const_mul 2).add (hM.const_mul 2)
  · filter_upwards [ae_restrict_mem hs] with x hx
    exact ((hc x hx).pow 2).mul continuous_const

end MeasureTheory
