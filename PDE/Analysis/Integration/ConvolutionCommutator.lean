/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2

/-!
# L² commutator bounds for Lipschitz multipliers

Let `a` be an L∞ scalar coefficient with a Lipschitz representative `v`.
Multiplication by `a` fails to commute with translation by `y` by at most
`Lip(v) ‖y‖` in operator norm on L². This follows from the almost-everywhere
formula `(v x - v (x - y)) • u (x - y)`.

Integrating the translation estimate against an integrable signed kernel `k`
bounds its convolution commutator by `Lip(v) ∫ ‖y‖ ‖k y‖`. The proof uses the
L²-valued convolution integral and Mathlib's bounded Hölder map.

The input may take values in any real Banach space. The first, purely translational
estimate does not need completeness.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The translation commutator of an L∞ coefficient with a Lipschitz representative
is bounded by its Lipschitz constant times the translation length. -/
theorem norm_lpSMul_translateL2_sub_le
    (a : Lp ℝ ∞ (volume : Measure (ℝ^n)))
    {v : ℝ^n → ℝ} {K : ℝ≥0} (hv : LipschitzWith K v) (ha : v =ᵐ[volume] a)
    (y : ℝ^n) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    ‖a • translateL2 ℝ y u - translateL2 ℝ y (a • u)‖ ≤ (K : ℝ) * ‖y‖ * ‖u‖ := by
  have hshift : (fun x ↦ v (x - y)) =ᵐ[volume] fun x ↦ a (x - y) := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (measurePreserving_add_left volume (-y)).quasiMeasurePreserving.ae_eq_comp ha
  have hproduct : (fun x ↦ (a • u : Lp E 2 volume) (x - y)) =ᵐ[volume]
      fun x ↦ a (x - y) • u (x - y) := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm, Pi.smul_apply'] using
      (measurePreserving_add_left volume (-y)).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a u)
  have hpointwise : ∀ᵐ x ∂volume,
      ‖(a • translateL2 ℝ y u - translateL2 ℝ y (a • u) : Lp E 2 volume) x‖ ≤
        ((K : ℝ) * ‖y‖) * ‖translateL2 ℝ y u x‖ := by
    filter_upwards [Lp.coeFn_sub (a • translateL2 ℝ y u) (translateL2 ℝ y (a • u)),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a (translateL2 ℝ y u),
      translateL2_ae_eq ℝ y u, translateL2_ae_eq ℝ y (a • u),
      hproduct, ha, hshift] with x hsub hleft hu hau hproduct ha hshift
    simp only [Pi.sub_apply, Pi.smul_apply'] at hsub hleft
    rw [hsub, hleft, hu, hau, hproduct, ← ha, ← hshift, ← sub_smul, norm_smul]
    have hdiff : ‖v x - v (x - y)‖ ≤ (K : ℝ) * ‖y‖ := by
      simpa only [dist_eq_norm, sub_sub_cancel] using hv.dist_le_mul x (x - y)
    exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
  simpa only [norm_translateL2] using Lp.norm_le_mul_norm_of_ae_le_mul hpointwise

variable [CompleteSpace E]

/-- An integrable kernel with finite first absolute moment has an L² commutator
bound determined by that moment and the coefficient's Lipschitz constant.
No derivative of the L² input is assumed. -/
theorem norm_lpSMul_convolutionL2CLM_sub_le
    (a : Lp ℝ ∞ (volume : Measure (ℝ^n)))
    {v : ℝ^n → ℝ} {K : ℝ≥0} (hv : LipschitzWith K v) (ha : v =ᵐ[volume] a)
    (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (hmoment : Integrable (fun y ↦ ‖y‖ * ‖k y‖) volume)
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    ‖a • convolutionL2CLM k hk u - convolutionL2CLM k hk (a • u)‖ ≤
      (K : ℝ) * (∫ y, ‖y‖ * ‖k y‖) * ‖u‖ := by
  let M : Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp E 2 volume :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).holderL volume ∞ 2 2 a
  have hM (w : Lp E 2 (volume : Measure (ℝ^n))) : M w = a • w := by
    apply Lp.ext
    filter_upwards
      [(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).coeFn_holder
        (r := (2 : ℝ≥0∞)) a w,
        Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a w] with x hleft hright
    change M w x = (a • w : Lp E 2 volume) x
    exact hleft.trans hright.symm
  have hleft : Integrable (fun y ↦ M (k y • translateL2 ℝ y u)) volume :=
    M.integrable_comp (integrable_smul_translateL2 hk u)
  have hright : Integrable (fun y ↦ k y • translateL2 ℝ y (a • u)) volume :=
    integrable_smul_translateL2 hk (a • u)
  have hcomm :
      a • convolutionL2CLM k hk u - convolutionL2CLM k hk (a • u) =
        ∫ y, k y • (a • translateL2 ℝ y u - translateL2 ℝ y (a • u)) := by
    rw [← hM (convolutionL2CLM k hk u), convolutionL2CLM_apply,
      convolutionL2CLM_apply,
      ← M.integral_comp_comm (integrable_smul_translateL2 hk u),
      ← integral_sub hleft hright]
    apply integral_congr_ae
    filter_upwards with y
    rw [map_smul, hM, smul_sub]
  have hbound (y : ℝ^n) :
      ‖k y • (a • translateL2 ℝ y u - translateL2 ℝ y (a • u))‖ ≤
        ((K : ℝ) * (‖y‖ * ‖k y‖)) * ‖u‖ := by
    rw [norm_smul]
    calc
      ‖k y‖ * ‖a • translateL2 ℝ y u - translateL2 ℝ y (a • u)‖ ≤
          ‖k y‖ * ((K : ℝ) * ‖y‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_lpSMul_translateL2_sub_le a hv ha y u)
          (norm_nonneg _)
      _ = ((K : ℝ) * (‖y‖ * ‖k y‖)) * ‖u‖ := by ac_rfl
  rw [hcomm]
  calc
    ‖∫ y, k y • (a • translateL2 ℝ y u - translateL2 ℝ y (a • u))‖ ≤
        ∫ y, ((K : ℝ) * (‖y‖ * ‖k y‖)) * ‖u‖ :=
      norm_integral_le_of_norm_le ((hmoment.const_mul (K : ℝ)).mul_const ‖u‖)
        (.of_forall hbound)
    _ = (K : ℝ) * (∫ y, ‖y‖ * ‖k y‖) * ‖u‖ := by
      rw [integral_mul_const, integral_const_mul]

end PDE.Analysis
