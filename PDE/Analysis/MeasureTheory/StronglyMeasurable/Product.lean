/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Almost-everywhere identities from product sections

Sectionwise equality implies product almost-everywhere equality when both
fields are jointly almost-everywhere strongly measurable. Measurable versions
reduce this to Mathlib's product null-set theorem. Joint measurability is needed:
arbitrary sectionwise null sets cannot be combined in this way.
-/

@[expose] public section

namespace MeasureTheory

open TopologicalSpace

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [TopologicalSpace E] [MetrizableSpace E]
  {μ : Measure α} {ν : Measure β} [SFinite ν] {f g : α × β → E}

/-- Joint almost-everywhere strong measurability makes sectionwise
almost-everywhere equality an identity for the product measure. -/
theorem ae_eq_prod_of_ae_eq_sections
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (h : ∀ᵐ t ∂μ, (fun x ↦ f (t, x)) =ᵐ[ν] fun x ↦ g (t, x)) :
    f =ᵐ[μ.prod ν] g := by
  have hmk : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae
      (hf.stronglyMeasurable_mk.measurableSet_eq_fun hg.stronglyMeasurable_mk)).mpr
    filter_upwards [h, Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with t ht hft hgt
    filter_upwards [ht, hft, hgt] with x hx hfx hgx
    exact hfx.symm.trans (hx.trans hgx)
  exact hf.ae_eq_mk.trans (hmk.trans hg.ae_eq_mk.symm)

end MeasureTheory
