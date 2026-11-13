/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Joint representatives of real multipliers

A coefficient with values in spatial L∞ need not be Bochner measurable in L∞. It is
enough here that multiplication by each fixed spatial L² function gives a Bochner L²
curve. Apply the joint-representative construction to indicators of a finite-measure
exhaustion, then select the representative from the first set containing the spatial
point. This constructs a measurable coefficient on the product space.

The scalar pairing result uses L² membership of the multiplied test, not integrability
of the coefficient alone. Fubini then identifies its product-space integral with the
time integral of the spatial L² pairing.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal InnerProductSpace MeasureTheory

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- A real L∞ coefficient has a joint measurable representative if its products with
fixed spatial L² functions are Bochner L². Only the spatial measure must be sigma-finite.
The coefficient itself is not assumed Bochner measurable in the L∞ norm. -/
theorem exists_jointRepresentative_of_memLp_multiplier [SigmaFinite ν]
    (c : α → Lp ℝ ∞ ν)
    (hc : ∀ w : Lp ℝ 2 ν, MemLp (fun t ↦ (c t • w : Lp ℝ 2 ν)) 2 μ) :
    ∃ C : α × β → ℝ, StronglyMeasurable C ∧
      ∀ᵐ t ∂μ, (fun x ↦ C (t, x)) =ᵐ[ν] (c t : β → ℝ) := by
  classical
  let w (k : ℕ) : Lp ℝ 2 ν :=
    indicatorConstLp 2 (measurableSet_spanningSets ν k)
      (measure_spanningSets_lt_top ν k).ne (1 : ℝ)
  have hproducts (k : ℕ) := (hc (w k)).exists_jointRepresentative
  choose V hV _hVmem hVsection using hproducts
  let C (z : α × β) : ℝ := V (spanningSetsIndex ν z.2) z
  have hVm : Measurable (fun z : ℕ × (α × β) ↦ V z.1 z.2) :=
    measurable_from_prod_countable_right fun k ↦ (hV k).measurable
  have hindex : Measurable (fun z : α × β ↦ spanningSetsIndex ν z.2) :=
    (measurableSet_spanningSetsIndex ν).comp measurable_snd
  have hCm : Measurable C := hVm.comp (hindex.prodMk measurable_id)
  refine ⟨C, hCm.stronglyMeasurable, ?_⟩
  have hw (k : ℕ) :
      ∀ᵐ x ∂ν, x ∈ spanningSets ν k → (w k) x = 1 :=
    indicatorConstLp_coeFn_mem
  filter_upwards [ae_all_iff.2 hVsection] with t ht
  have hmul (k : ℕ) :
      ∀ᵐ x ∂ν, (c t • w k : Lp ℝ 2 ν) x = (c t) x * (w k) x := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (c t) (w k)] with x hx
    exact hx
  filter_upwards [ae_all_iff.2 ht, ae_all_iff.2 hmul, ae_all_iff.2 hw] with
    x htx hmx hwx
  change V (spanningSetsIndex ν x) (t, x) = (c t) x
  rw [htx _, hmx _, hwx _ (mem_spanningSetsIndex ν x), mul_one]

/-- Joint representatives identify the raw coefficient-weighted pairing with its
iterated L² pairing. The Bochner L² bound on the multiplied test supplies integrability;
no separate integrability or time regularity of the coefficient is required. -/
theorem integral_mul_prod_eq_integral_L2_inner_multiplier [SFinite ν]
    {c : α → Lp ℝ ∞ ν} {u v : α → Lp ℝ 2 ν} {C U V : α × β → ℝ}
    (hu : MemLp u 2 μ)
    (hcv : MemLp (fun t ↦ (c t • v t : Lp ℝ 2 ν)) 2 μ)
    (hC : AEStronglyMeasurable C (μ.prod ν))
    (hU : AEStronglyMeasurable U (μ.prod ν))
    (hV : AEStronglyMeasurable V (μ.prod ν))
    (hCsection : ∀ᵐ t ∂μ, (fun x ↦ C (t, x)) =ᵐ[ν] (c t : β → ℝ))
    (hUsection : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → ℝ))
    (hVsection : ∀ᵐ t ∂μ, (fun x ↦ V (t, x)) =ᵐ[ν] (v t : β → ℝ)) :
    Integrable (fun z ↦ U z * (C z * V z)) (μ.prod ν) ∧
      (∫ z, U z * (C z * V z) ∂μ.prod ν) =
        ∫ t, inner ℝ (u t) (c t • v t : Lp ℝ 2 ν) ∂μ := by
  have hCV : AEStronglyMeasurable (fun z ↦ C z * V z) (μ.prod ν) :=
    hC.mul hV
  have hCVsection : ∀ᵐ t ∂μ,
      (fun x ↦ C (t, x) * V (t, x)) =ᵐ[ν] (c t • v t : Lp ℝ 2 ν) := by
    filter_upwards [hCsection, hVsection] with t hct hvt
    filter_upwards [hct, hvt, Lp.coeFn_lpSMul (r := 2) (c t) (v t)] with
      x hcx hvx hproduct
    rw [hcx, hvx, hproduct]
    rfl
  constructor
  · simpa only [Real.inner_apply] using
      (integrable_inner_prod_of_ae_eq_L2_sections hu hcv hU hCV hUsection hCVsection)
  · simpa only [Real.inner_apply] using
      (integral_inner_prod_eq_integral_L2_inner hu hcv hU hCV hUsection hCVsection)

end MeasureTheory
