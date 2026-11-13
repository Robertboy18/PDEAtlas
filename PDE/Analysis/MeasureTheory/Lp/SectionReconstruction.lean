/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Distance

/-!
# Bochner L² sections of a product-space L² function

A square-integrable function on a product has square-integrable spatial slices at
almost every parameter. On those slices we take the L² class; on the exceptional
set we use zero. To prove that this class-valued map is strongly measurable, we express
its squared distance to each fixed L² function as a measurable spatial integral.
Separability of the spatial L² space then gives strong measurability.

Only the inner measure is s-finite. The outer measure can have infinite mass. Separability
is stated as a property of the spatial L² space; Mathlib supplies it for a separable
range and a separable measure, in particular for a countably generated spatial sigma
algebra with an s-finite measure.
-/

@[expose] public section

noncomputable section

open Filter TopologicalSpace
open scoped ENNReal MeasureTheory

namespace MeasureTheory

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

/-- The L² norm identity for a difference, with its spatial representatives
identified only almost everywhere. This is the scalar integral used to test
measurability of the class-valued section map. -/
private theorem dist_sq_eq_integral_of_ae_eq
    (u v : Lp E 2 ν) {f : β → E} (hf : f =ᵐ[ν] (u : β → E)) :
    dist u v ^ 2 = ∫ x, ‖f x - v x‖ ^ 2 ∂ν := by
  rw [dist_eq_norm, Lp.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v, hf] with x hsub hx
  rw [hsub, hx, Pi.sub_apply]

variable [SFinite ν]

/-- Every product-space L² function has an Bochner L² class of spatial sections,
provided the spatial L² space is separable. Slice membership and strong measurability
of the section map are derived from product L² membership. The reconstructed class has
exactly the product L² norm; its representative is specified only almost everywhere. -/
theorem MemLp.exists_L2_sections [SeparableSpace (Lp E 2 ν)]
    {U : α × β → E} (hU : MemLp U 2 (μ.prod ν)) :
    ∃ u : Lp (Lp E 2 ν) 2 μ,
      (∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E)) ∧
      ‖u‖ = ‖hU.toLp U‖ := by
  classical
  have hsq : Integrable (fun z ↦ ‖U z‖ ^ 2) (μ.prod ν) :=
    hU.norm.integrable_sq
  have hslices : ∀ᵐ t ∂μ, MemLp (fun x ↦ U (t, x)) 2 ν := by
    filter_upwards [hU.aestronglyMeasurable.prodMk_left,
      ((integrable_prod_iff hsq.aestronglyMeasurable).mp hsq).1] with t ht htsq
    exact (memLp_two_iff_integrable_sq_norm ht).mpr htsq
  let v (t : α) : Lp E 2 ν :=
    if ht : MemLp (fun x ↦ U (t, x)) 2 ν then ht.toLp (fun x ↦ U (t, x)) else 0
  have hvsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (v t : β → E) := by
    filter_upwards [hslices] with t ht
    dsimp only [v]
    rw [dite_eq_left ht]
    exact ht.coeFn_toLp.symm
  have hvmeas : AEStronglyMeasurable v μ := by
    apply aestronglyMeasurable_of_aemeasurable_dist
    intro w
    have hw : AEStronglyMeasurable (fun z : α × β ↦ w z.2) (μ.prod ν) :=
      ((Lp.stronglyMeasurable w).comp_measurable measurable_snd).aestronglyMeasurable
    have hdist : AEMeasurable
        (fun t ↦ √(∫ x, ‖U (t, x) - w x‖ ^ 2 ∂ν)) μ :=
      ((hU.aestronglyMeasurable.sub hw).norm.pow 2).integral_prod_right'.aemeasurable.sqrt
    apply hdist.congr
    filter_upwards [hvsec] with t ht
    rw [← dist_sq_eq_integral_of_ae_eq (v t) w ht, Real.sqrt_sq dist_nonneg]
  have hvnorm : (fun t ↦ ∫ x, ‖U (t, x)‖ ^ 2 ∂ν) =ᵐ[μ] fun t ↦ ‖v t‖ ^ 2 := by
    filter_upwards [hvsec] with t ht
    calc
      (∫ x, ‖U (t, x)‖ ^ 2 ∂ν) = ∫ x, ‖(v t) x‖ ^ 2 ∂ν :=
        integral_congr_ae (ht.fun_comp fun y : E ↦ ‖y‖ ^ 2)
      _ = ‖v t‖ ^ 2 := (Lp.norm_sq_eq_integral_norm_sq (v t)).symm
  have hv : MemLp v 2 μ :=
    (memLp_two_iff_integrable_sq_norm hvmeas).mpr
      (hsq.integral_prod_left.congr hvnorm)
  have hsection : ∀ᵐ t ∂μ,
      (fun x ↦ U (t, x)) =ᵐ[ν] ((hv.toLp v) t : β → E) := by
    filter_upwards [hvsec, hv.coeFn_toLp] with t ht hvt
    rw [hvt]
    exact ht
  refine ⟨hv.toLp v, hsection, ?_⟩
  refine (Lp.norm_eq_of_ae_eq_L2_sections (hv.toLp v) (hU.toLp U) ?_).symm
  have htoLp : ∀ᵐ t ∂μ,
      (fun x ↦ (hU.toLp U) (t, x)) =ᵐ[ν] fun x ↦ U (t, x) :=
    Measure.ae_ae_of_ae_prod hU.coeFn_toLp
  filter_upwards [htoLp, hsection] with t ht hs
  exact Filter.EventuallyEq.trans ht hs

/-- A finite family of product-space L² functions determines a Bochner L² curve in the
finite ℓ² product of spatial L² spaces. Each coordinate is reconstructed by
`MemLp.exists_L2_sections`; Mathlib's `memLp_piLp_iff` assembles the family. -/
theorem exists_L2_sections_pi [SeparableSpace (Lp E 2 ν)]
    {ι : Type*} [Fintype ι] {U : ι → α × β → E}
    (hU : ∀ i, MemLp (U i) 2 (μ.prod ν)) :
    ∃ u : Lp (PiLp 2 (fun _ : ι ↦ Lp E 2 ν)) 2 μ,
      ∀ i, ∀ᵐ t ∂μ, (fun x ↦ U i (t, x)) =ᵐ[ν] (u t i : β → E) := by
  classical
  choose v hvsec _hvnorm using fun i ↦ (hU i).exists_L2_sections
  let w (t : α) : PiLp 2 (fun _ : ι ↦ Lp E 2 ν) :=
    WithLp.toLp 2 (fun i ↦ v i t)
  have hw : MemLp w 2 μ := by
    apply memLp_piLp_iff.mpr
    intro i
    exact Lp.memLp (v i)
  refine ⟨hw.toLp w, ?_⟩
  intro i
  filter_upwards [hvsec i, hw.coeFn_toLp] with t ht hwt
  rw [hwt]
  exact ht

end MeasureTheory
