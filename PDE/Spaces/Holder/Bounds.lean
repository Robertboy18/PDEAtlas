/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.On

/-!
# Bundling uniform and Hölder bounds

For a metric type `X`, a function `f : X → ℝ` with `HolderWith K γ f` and `‖f x‖ ≤ B` for every `x`
defines an element `ofBound f hf B hB` of `C0GammaOn X γ`, whose norm is at most `B + K` when
`0 ≤ B` (`norm_ofBound_le`). The extended norm of an element of `C0GammaOn X γ` is its extended sup
norm `⨆ x, ‖f x‖ₑ` plus Mathlib's extended Hölder seminorm `eHolderNorm`
(`enorm_eq_iSup_enorm_add_eHolderNorm`).
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace HolderSpace.C0GammaOn

variable {X : Type*} [MetricSpace X] {γ : Exponent}

/-- The element of `C0GammaOn X γ` given by a function `f` with `HolderWith K γ f` and `‖f x‖ ≤ B`
for every `x`. -/
def ofBound (f : X → ℝ) {K : ℝ≥0} (hf : HolderWith K (γ : ℝ≥0) f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : C0GammaOn X γ where
  toBoundedContinuousFunction :=
    BoundedContinuousFunction.ofNormedAddCommGroup f (hf.continuous γ.pos) B hB
  memHolder := hf.memHolder

/-- `ofBound f hf B hB` agrees with `f` at every point. -/
@[simp]
theorem ofBound_apply (f : X → ℝ) {K : ℝ≥0} (hf : HolderWith K (γ : ℝ≥0) f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) (x : X) :
    ofBound f hf B hB x = f x :=
  rfl

/-- If `0 ≤ B`, the norm of `ofBound f hf B hB` is at most `B + K`. -/
theorem norm_ofBound_le (f : X → ℝ) {K : ℝ≥0} (hf : HolderWith K (γ : ℝ≥0) f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖f x‖ ≤ B) :
    ‖ofBound f hf B hB‖ ≤ B + K := by
  rw [norm_def]
  exact add_le_add
    (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (hf.continuous γ.pos) hB0 hB)
    (NNReal.coe_le_coe.mpr hf.nnholderNorm_le)

/-- The extended norm `‖f‖ₑ` of `f : C0GammaOn X γ` is `⨆ x, ‖f x‖ₑ` plus Mathlib's extended Hölder
seminorm `eHolderNorm γ f`. -/
theorem enorm_eq_iSup_enorm_add_eHolderNorm (f : C0GammaOn X γ) :
    ‖f‖ₑ = (⨆ x, ‖f x‖ₑ) + eHolderNorm (γ : ℝ≥0) (fun x ↦ f x) := by
  rw [← ofReal_norm, norm_def,
    ENNReal.ofReal_add (norm_nonneg _) (NNReal.coe_nonneg _),
    ofReal_norm, BoundedContinuousFunction.enorm_eq_iSup_enorm,
    ENNReal.ofReal_coe_nnreal]
  exact congrArg ((⨆ x, ‖f x‖ₑ) + ·) f.memHolder.coe_nnHolderNorm_eq_eHolderNorm

end HolderSpace.C0GammaOn
