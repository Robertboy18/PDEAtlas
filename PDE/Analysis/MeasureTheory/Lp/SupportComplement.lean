/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Zero Lp tails outside a cover of the support

A measurable cover of the support inside an almost-everywhere domain makes the
function zero on the exact complementary restriction. This constructs Lp
membership and the zero Lp element for any exponent, without regularity or
integrability assumptions on the function elsewhere.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

/-- Covering the nonzero set inside an almost-everywhere domain makes the
function almost everywhere zero on the exact complement of the cover. -/
theorem ae_eq_zero_restrict_compl_of_support_cover
    (μ : Measure α) (domain cover : Set α) (f : α → E)
    (hcover : MeasurableSet cover) (hdomain : ∀ᵐ x ∂μ, x ∈ domain)
    (hsupport : domain ∩ Function.support f ⊆ cover) :
    f =ᵐ[μ.restrict coverᶜ] 0 := by
  filter_upwards [ae_restrict_of_ae hdomain, ae_restrict_mem hcover.compl] with x hx hc
  exact Function.notMem_support.mp fun hf ↦ hc (hsupport ⟨hx, hf⟩)

/-- The complementary restriction has an Lp witness whose Lp element is
zero. The cover need only contain support in the domain carrying the measure. -/
theorem exists_memLp_eq_zero_restrict_compl_of_support_cover
    (μ : Measure α) (domain cover : Set α) (f : α → E) (p : ℝ≥0∞)
    (hcover : MeasurableSet cover) (hdomain : ∀ᵐ x ∂μ, x ∈ domain)
    (hsupport : domain ∩ Function.support f ⊆ cover) :
    ∃ h : MemLp f p (μ.restrict coverᶜ), h.toLp f = 0 := by
  have hz := ae_eq_zero_restrict_compl_of_support_cover
    μ domain cover f hcover hdomain hsupport
  have h : MemLp f p (μ.restrict coverᶜ) := (memLp_congr_ae hz).mpr MemLp.zero
  exact ⟨h, (h.toLp_congr MemLp.zero hz).trans (MemLp.toLp_zero _)⟩

end MeasureTheory
