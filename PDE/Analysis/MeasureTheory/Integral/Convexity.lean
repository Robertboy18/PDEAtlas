/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.LowerBounded

/-!
# Equality in a midpoint integral inequality

An integrable lower bound and finite signed endpoint energy justify equality
almost everywhere in the pointwise midpoint inequality. Integrability is a
consequence, rather than an additional hypothesis on the densities.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace PDE.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g h b : X → ℝ}

/-- Equal finite endpoint energies and minimality against a midpoint force
equality almost everywhere in its pointwise convexity inequality. The lower
bound may depend on space, and the measure need not be finite. -/
theorem ae_eq_average_of_lowerBoundedIntegral_le
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) (hb : Integrable b μ)
    (hf_lower : ∀ᵐ x ∂μ, -b x ≤ f x) (hg_lower : ∀ᵐ x ∂μ, -b x ≤ g x)
    (hh_lower : ∀ᵐ x ∂μ, -b x ≤ h x)
    (hfinite : lowerBoundedIntegral μ f ≠ ⊤)
    (heq : lowerBoundedIntegral μ f = lowerBoundedIntegral μ g)
    (hmin : lowerBoundedIntegral μ f ≤ lowerBoundedIntegral μ h)
    (hmid : ∀ᵐ x ∂μ, h x ≤ (f x + g x) / 2) :
    ∀ᵐ x ∂μ, h x = (f x + g x) / 2 := by
  have hfi := (integrable_iff_lowerBoundedIntegral_ne_top hf hb hf_lower).mpr hfinite
  have hgi := (integrable_iff_lowerBoundedIntegral_ne_top hg hb hg_lower).mpr
    (heq ▸ hfinite)
  have havg : Integrable (fun x ↦ (f x + g x) / 2) μ := (hfi.add hgi).div_const 2
  have hhi : Integrable h μ := integrable_of_le_of_le hh hh_lower hmid hb.neg havg
  rw [lowerBoundedIntegral_eq_integral hfi, lowerBoundedIntegral_eq_integral hgi,
    EReal.coe_eq_coe_iff] at heq
  rw [lowerBoundedIntegral_eq_integral hfi, lowerBoundedIntegral_eq_integral hhi,
    EReal.coe_le_coe_iff] at hmin
  apply (integral_eq_iff_of_ae_le hhi havg hmid).mp
  have hu := integral_mono_ae hhi havg hmid
  rw [integral_div, integral_add hfi hgi] at hu ⊢
  linarith

end PDE.Analysis
