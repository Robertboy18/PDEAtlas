/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform time bounds for essentially bounded coefficient fields

A common almost-everywhere set of spatial sections with uniformly bounded
time derivatives gives a Lipschitz curve in `L∞`. Mathlib then gives absolute
continuity on the interval.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

open Set
open scoped ENNReal NNReal Topology

/-- Uniformly bounded time derivatives of representatives make an `L∞` curve
Lipschitz on the closed interval. The derivative and its bound hold for every
time on one common full-measure spatial set. Neither finite spatial measure
nor a Banach-valued derivative is assumed. -/
theorem lipschitzOnWith_lp_top_of_ae_hasDerivWithinAt
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → Lp E ∞ μ) (f fdot : ℝ → α → E) {a b : ℝ} (K : ℝ≥0)
    (hrep : ∀ t ∈ uIcc a b, (F t : α → E) =ᵐ[μ] f t)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ uIcc a b,
      HasDerivWithinAt (fun s ↦ f s x) (fdot t x) (uIcc a b) t)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ uIcc a b, ‖fdot t x‖ ≤ K) :
    LipschitzOnWith K F (uIcc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hdiff :
      ∀ᵐ x ∂μ, ‖((F s - F t : Lp E ∞ μ) : α → E) x‖ ≤
        (K : ℝ) * dist s t := by
    filter_upwards [Lp.coeFn_sub (F s) (F t), hrep s hs, hrep t ht,
      hderiv, hbound] with x hsub hsx htx hdx hbx
    rw [hsub]
    change ‖(F s : α → E) x - (F t : α → E) x‖ ≤ _
    rw [hsx, htx]
    simpa only [dist_eq_norm] using
      (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hdx hbx ht hs
  rw [dist_eq_norm, Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable (F s - F t))]
  exact
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound hdiff)).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg K.coe_nonneg dist_nonneg))

end MeasureTheory
