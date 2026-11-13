/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Uniform bounds and parameter dependence in L∞

Essential bounds control the L∞ norm on an arbitrary measure space. Applying
this to differences transfers uniform parameter estimates for representatives
to Lipschitz dependence of their L∞ classes.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open Set
open scoped ENNReal NNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup E]

/-- An essential bound controls the L∞ norm without a finite-measure
assumption. The nonnegative bound also covers the zero measure. -/
theorem norm_top_le_of_ae_bound {u : Lp E ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ᵐ x ∂μ, ‖u x‖ ≤ C) : ‖u‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hu)).trans_eq (ENNReal.toReal_ofReal hC)

/-- Uniform almost-everywhere bounds for differences of representatives
give a Lipschitz L∞-valued parameter map. -/
theorem lipschitzOnWith_top_of_ae_norm_sub_le
    {X : Type*} [PseudoMetricSpace X] {S : Set X} {K : ℝ≥0}
    (U : X → Lp E ∞ μ) (u : X → α → E)
    (hrep : ∀ s ∈ S, (U s : α → E) =ᵐ[μ] u s)
    (hbound : ∀ s ∈ S, ∀ t ∈ S, ∀ᵐ x ∂μ,
      ‖u s x - u t x‖ ≤ K * dist s t) :
    LipschitzOnWith K U S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [_root_.dist_eq_norm]
  apply norm_top_le_of_ae_bound (mul_nonneg K.coe_nonneg dist_nonneg)
  filter_upwards [Lp.coeFn_sub (U s) (U t), hrep s hs, hrep t ht, hbound s hs t ht]
    with x hx hsx htx hxt
  simpa only [hx, Pi.sub_apply, hsx, htx] using hxt

end MeasureTheory.Lp
