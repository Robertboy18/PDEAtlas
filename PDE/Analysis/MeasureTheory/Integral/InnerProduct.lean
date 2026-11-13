/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gram identities for Hilbert-valued integrals

An integrable Hilbert-valued family has squared integral norm equal to its iterated
real Gram pairing. A positive majorant bounds this pairing without any Fubini or
sigma-finiteness premise.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The square of the norm of a Hilbert-valued integral is its iterated real Gram pairing.
Integrability of the vector-valued family suffices; no product-measure hypotheses are needed. -/
theorem norm_integral_sq_eq_integral_integral_re_inner {f : α → E} (hf : Integrable f μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 = ∫ x, ∫ y, RCLike.re (inner 𝕜 (f x) (f y)) ∂μ ∂μ := by
  simp_rw [integral_re (hf.const_inner _), integral_inner hf,
    inner_re_symm (f _) (∫ y, f y ∂μ)]
  rw [integral_re (hf.const_inner _), integral_inner hf, ← norm_sq_eq_re_inner]

/-- A positive majorant of the real Gram kernel controls the squared integral norm. -/
theorem ofReal_norm_integral_sq_le_lintegral_lintegral_re_inner
    {f : α → E} (hf : Integrable f μ) :
    ENNReal.ofReal (‖∫ x, f x ∂μ‖ ^ 2) ≤
      ∫⁻ x, ∫⁻ y, ‖RCLike.re (inner 𝕜 (f x) (f y))‖ₑ ∂μ ∂μ := by
  rw [← Real.enorm_of_nonneg (sq_nonneg _),
    norm_integral_sq_eq_integral_integral_re_inner (𝕜 := 𝕜) hf]
  apply (enorm_integral_le_lintegral_enorm _).trans
  exact lintegral_mono fun x ↦ enorm_integral_le_lintegral_enorm _

end MeasureTheory
