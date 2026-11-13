/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Primitives of essentially bounded functions

An almost-everywhere bound controls every increment of the actual interval
primitive. The primitive therefore has a global Lipschitz representative
without selecting a pointwise bounded representative of its integrand.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Analysis

/-- An almost-everywhere norm bound gives the same Lipschitz bound for every
normalized interval primitive. -/
theorem lipschitzWith_intervalIntegral_of_ae_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : LocallyIntegrable f volume) {K : ℝ≥0}
    (hK : ∀ᵐ x : ℝ, ‖f x‖ ≤ K) (a : ℝ) :
    LipschitzWith K (fun x ↦ ∫ s in a..x, f s) := by
  have hint (x y : ℝ) : IntervalIntegrable f volume x y :=
    (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left (hint a x) (hint a y)]
  simpa only [Real.dist_eq] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := y) (b := x)
      (hK.mono fun _ hx _ ↦ hx)

/-- The exact essential supremum is a Lipschitz constant for the actual
primitive, even when that essential supremum is zero. -/
theorem lipschitzWith_intervalIntegral_of_memLp_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f ∞ volume) (a : ℝ) :
    LipschitzWith (eLpNorm f ∞ volume).toNNReal (fun x ↦ ∫ s in a..x, f s) := by
  apply lipschitzWith_intervalIntegral_of_ae_bound (hf.locallyIntegrable (by simp)) _ a
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with x hx
  rw [← eLpNorm_exponent_top hf.aestronglyMeasurable] at hx
  simpa only [toReal_enorm, ENNReal.coe_toNNReal_eq_toReal] using
    ENNReal.toReal_mono hf.eLpNorm_lt_top.ne hx

/-- The actual primitive of an arbitrary `L∞` function is globally Lipschitz.
No pointwise bound on the supplied representative is required. -/
theorem exists_lipschitzWith_intervalIntegral_of_memLp_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f ∞ volume) (a : ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x ↦ ∫ s in a..x, f s) :=
  ⟨_, lipschitzWith_intervalIntegral_of_memLp_top hf a⟩

end PDE.Analysis
