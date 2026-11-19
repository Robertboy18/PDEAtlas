/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Fubini
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Basic

/-!
# Joint representatives of Bochner L² curves

Summably accurate simple-function approximations give a jointly strongly measurable
representative. Fubini transfers Bochner L² integrability to product-space L².
The product and iterated L² norms agree whenever their sections agree almost everywhere.

Only the spatial measure is assumed s-finite. The joint representative agrees with the
given L² sections for almost every time, so it carries no value at a single time.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

/-- A product-space L² class and its Bochner L² sections have the same norm.
Only almost-everywhere agreement of the spatial sections is needed. -/
theorem Lp.norm_eq_of_ae_eq_L2_sections [SFinite ν]
    (u : Lp (Lp E 2 ν) 2 μ) (U : Lp E 2 (μ.prod ν))
    (hsection : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E)) :
    ‖U‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg U) (norm_nonneg u)).1
  rw [Lp.norm_sq_eq_integral_norm_sq U, Lp.norm_sq_eq_integral_norm_sq u,
    integral_prod_real _ ((Lp.memLp U).norm.integrable_sq)]
  apply integral_congr_ae
  filter_upwards [hsection] with t ht
  calc
    (∫ x, ‖U (t, x)‖ ^ 2 ∂ν) = ∫ x, ‖(u t) x‖ ^ 2 ∂ν :=
      integral_congr_ae (ht.fun_comp fun v : E ↦ ‖v‖ ^ 2)
    _ = ‖u t‖ ^ 2 := (Lp.norm_sq_eq_integral_norm_sq (u t)).symm

variable [SFinite ν] [CompleteSpace E]

/-- A Bochner L² curve admits a jointly strongly measurable product-space L²
representative whose spatial sections agree with the curve almost everywhere.
The representative is constructed by simple-function approximation and completeness. -/
theorem MemLp.exists_jointRepresentative
    {u : α → Lp E 2 ν} (hu : MemLp u 2 μ) :
    ∃ U : α × β → E, StronglyMeasurable U ∧ MemLp U 2 (μ.prod ν) ∧
      ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E) := by
  obtain ⟨U, hU, hsection⟩ :=
    (Lp.stronglyMeasurable (hu.toLp u)).exists_stronglyMeasurable_jointLpRepresentative
  have hsection' : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E) := by
    filter_upwards [hu.coeFn_toLp] with t ht
    simpa only [ht] using hsection t
  exact ⟨U, hU, memLp_prod_of_ae_eq_L2_sections hu hU.aestronglyMeasurable hsection',
    hsection'⟩

end MeasureTheory
