/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.OddSupport
import CAS.ExactTactic

/-!
# Global L² bounds from an even square

Reflection transfers a weighted energy on `(0,L)` to the whole line.
Only the square must be even, so the same estimate applies to an odd
function and its even derivative.
-/

@[expose] public section

noncomputable section

open Set

namespace MeasureTheory

/-- A half-interval weighted energy controls a global L² norm when the square
is even and supported. The same statement applies to odd omega and even omega_x. A function
outside `L²` has `(eLpNorm f 2).toReal = 0`, so no `L²` assumption is needed. -/
theorem eLpNorm_le_of_even_sq_weighted_energy
    {f w : ℝ → ℝ} {L a E : ℝ} (ha : 0 < a) (hE : 0 ≤ E)
    (heven : Function.Even (fun x ↦ f x ^ 2))
    (hsupport : ∀ x, L ≤ x → f x = 0)
    (hw : ∀ x ∈ Ioo 0 L, a ≤ w x)
    (hint : IntegrableOn (fun x ↦ f x ^ 2 * w x) (Ioo 0 L))
    (henergy : (∫ x in Ioo 0 L, f x ^ 2 * w x) ≤ E ^ 2) :
    (eLpNorm f 2 volume).toReal ≤ √(2 / a) * E := by
  by_cases hf : MemLp f 2 volume
  swap
  · rw [show eLpNorm f 2 volume = ⊤ from not_lt_top_iff.mp hf, ENNReal.toReal_top]
    exact mul_nonneg (Real.sqrt_nonneg _) hE
  have hhalf := norm_toLp_sq_le_integral_sq_mul_div ha (hf.restrict (Ioo 0 L))
    ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ hw x hx) hint
  rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq (hf.restrict (Ioo 0 L))]
    at hhalf
  have hsq : (eLpNorm f 2 volume).toReal ^ 2 ≤ (2 / a) * E ^ 2 := by
    rw [← integral_sq_eq_eLpNorm_toReal_sq hf,
      integral_eq_two_mul_integral_Ioo_of_even_support heven
        (fun x hx ↦ by rw [hsupport x hx]; norm_num)]
    calc
      _ ≤ 2 * ((∫ x in Ioo 0 L, f x ^ 2 * w x) / a) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ ≤ 2 * (E ^ 2 / a) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right henergy ha.le) (by norm_num)
      _ = _ := by cas
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg (Real.sqrt_nonneg _) hE)).mp
  simpa only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / a)] using hsq

/-- Positive floors for two weights control the sum of global L² norms by the
combined half-interval energy. Only the two squares must be even. -/
theorem eLpNorm_add_le_of_even_sq_weighted_energy
    {f g φ σ : ℝ → ℝ} {L a b E : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hE : 0 ≤ E)
    (hevenF : Function.Even (fun x ↦ f x ^ 2))
    (hevenG : Function.Even (fun x ↦ g x ^ 2))
    (hsupportF : ∀ x, L ≤ x → f x = 0) (hsupportG : ∀ x, L ≤ x → g x = 0)
    (hφ : ∀ x ∈ Ioo 0 L, a ≤ φ x) (hσ : ∀ x ∈ Ioo 0 L, b ≤ σ x)
    (hint : IntegrableOn (fun x ↦ f x ^ 2 * φ x) (Ioo 0 L))
    (hintG : IntegrableOn (fun x ↦ g x ^ 2 * σ x) (Ioo 0 L))
    (henergy : (∫ x in Ioo 0 L, f x ^ 2 * φ x) +
      (∫ x in Ioo 0 L, g x ^ 2 * σ x) ≤ E ^ 2) :
    (eLpNorm f 2 volume).toReal + (eLpNorm g 2 volume).toReal ≤
      (√(2 / a) + √(2 / b)) * E := by
  have hI : 0 ≤ ∫ x in Ioo 0 L, f x ^ 2 * φ x :=
    integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioo).mono
      fun x hx ↦ mul_nonneg (sq_nonneg _) (ha.le.trans (hφ x hx))
  have hJ : 0 ≤ ∫ x in Ioo 0 L, g x ^ 2 * σ x :=
    integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioo).mono
      fun x hx ↦ mul_nonneg (sq_nonneg _) (hb.le.trans (hσ x hx))
  have hF := eLpNorm_le_of_even_sq_weighted_energy ha hE hevenF hsupportF hφ hint
    ((le_add_of_nonneg_right hJ).trans henergy)
  have hG := eLpNorm_le_of_even_sq_weighted_energy hb hE hevenG hsupportG hσ hintG
    ((le_add_of_nonneg_left hI).trans henergy)
  exact (add_le_add hF hG).trans_eq (add_mul _ _ _).symm

end MeasureTheory
