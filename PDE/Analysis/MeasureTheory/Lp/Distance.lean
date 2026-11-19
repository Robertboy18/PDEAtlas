/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Difference energy of L² representatives

The square integral of two representatives is the squared distance between
their L² classes. A common support enclosure allows the energy to be computed
on a bounded interval while retaining its L² endpoint continuity.
-/

@[expose] public section

noncomputable section

open Filter Set

namespace MeasureTheory

/-- The square integral of any two real representatives equals their squared
L² distance. The exceptional sets may depend on the two representatives. -/
theorem dist_sq_eq_integral_sq_sub_of_ae_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F G : Lp ℝ 2 μ) {f g : α → ℝ}
    (hf : (F : α → ℝ) =ᵐ[μ] f) (hg : (G : α → ℝ) =ᵐ[μ] g) :
    dist F G ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [dist_eq_norm, Lp.norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub F G, hf, hg] with x hsub hfx hgx
  simp only [hsub, Pi.sub_apply, hfx, hgx]

/-- A common pointwise support enclosure identifies the restricted difference
energy with the full L² distance. -/
theorem dist_sq_eq_setIntegral_sq_sub_of_support
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F G : Lp ℝ 2 μ) {f g : α → ℝ} {K : Set α}
    (hf : (F : α → ℝ) =ᵐ[μ] f) (hg : (G : α → ℝ) =ᵐ[μ] g)
    (hsupp : ∀ x, x ∉ K → f x = 0 ∧ g x = 0) :
    dist F G ^ 2 = ∫ x in K, (f x - g x) ^ 2 ∂μ := by
  rw [dist_sq_eq_integral_sq_sub_of_ae_eq F G hf hg]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp only [(hsupp x hx).1, (hsupp x hx).2, sub_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

end MeasureTheory
