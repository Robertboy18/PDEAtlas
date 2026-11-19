/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Spatial sections of bounded measurable coefficients

A bounded measurable function on a product determines bounded spatial L∞ classes.
The classes are chosen to obey the same bound even at exceptional parameters. We
prove measurability of their scalar L² pairings, not measurability in the L∞ norm.
-/

@[expose] public section

noncomputable section

open Filter
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- An essentially bounded jointly measurable coefficient has spatial L∞ sections
with a uniform norm bound. Exceptional sections can be set to zero. -/
theorem exists_bounded_Linfty_sections [SFinite ν]
    {C : α × β → ℝ} (hC : AEStronglyMeasurable C (μ.prod ν))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ z ∂μ.prod ν, ‖C z‖ ≤ M) :
    ∃ c : α → Lp ℝ ∞ ν,
      (∀ t, ‖c t‖ ≤ M) ∧
      ∀ᵐ t ∂μ, (fun x ↦ C (t, x)) =ᵐ[ν] (c t : β → ℝ) := by
  classical
  let good (t : α) :=
    AEStronglyMeasurable (fun x ↦ C (t, x)) ν ∧ ∀ᵐ x ∂ν, ‖C (t, x)‖ ≤ M
  have hmem (t : α) (ht : good t) : MemLp (fun x ↦ C (t, x)) ∞ ν :=
    memLp_top_of_bound ht.1 M ht.2
  let c (t : α) : Lp ℝ ∞ ν :=
    if ht : good t then (hmem t ht).toLp (fun x ↦ C (t, x)) else 0
  refine ⟨c, ?_, ?_⟩
  · intro t
    dsimp only [c]
    split_ifs with ht
    · rw [Lp.norm_toLp, eLpNorm_exponent_top ht.1]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (eLpNormEssSup_le_of_ae_bound ht.2)).trans_eq (ENNReal.toReal_ofReal hM)
    · simpa using hM
  · filter_upwards [hC.prodMk_left, Measure.ae_ae_of_ae_prod hbound] with t ht hbt
    dsimp only [c]
    rw [dite_eq_left (show good t from ⟨ht, hbt⟩)]
    exact (hmem t ⟨ht, hbt⟩).coeFn_toLp.symm

/-- Scalar pairings of bounded spatial coefficient sections are measurable by Fubini.
This conclusion does not require strong measurability of the L∞-valued section map. -/
theorem aestronglyMeasurable_inner_Linfty_sections [SFinite ν]
    {C : α × β → ℝ} {c : α → Lp ℝ ∞ ν}
    (hC : AEStronglyMeasurable C (μ.prod ν))
    (hsection : ∀ᵐ t ∂μ, (fun x ↦ C (t, x)) =ᵐ[ν] (c t : β → ℝ))
    (u v : Lp ℝ 2 ν) :
    AEStronglyMeasurable (fun t ↦ inner ℝ (c t • u : Lp ℝ 2 ν) v) μ := by
  have hu : AEStronglyMeasurable (fun z : α × β ↦ u z.2) (μ.prod ν) :=
    ((Lp.stronglyMeasurable u).comp_measurable measurable_snd).aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun z : α × β ↦ v z.2) (μ.prod ν) :=
    ((Lp.stronglyMeasurable v).comp_measurable measurable_snd).aestronglyMeasurable
  apply ((hC.mul hu).mul hv).integral_prod_right'.congr
  filter_upwards [hsection] with t ht
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ht, Lp.coeFn_lpSMul (r := 2) (c t) u] with x hx hmul
  change C (t, x) * u x * v x = inner ℝ ((c t • u : Lp ℝ 2 ν) x) (v x)
  rw [hx, hmul]
  simp only [Real.inner_apply, smul_eq_mul, Pi.mul_apply]

end MeasureTheory
