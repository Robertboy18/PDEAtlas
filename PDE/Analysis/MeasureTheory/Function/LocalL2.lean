/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Local L² integrability on an open cover

An almost everywhere measurable function that is L² on each member of an open
cover is L² on every compact subset of the covered set. Local integrability of
its square gives the conclusion without a global norm bound.

A function whose squared norm is locally integrable has locally integrable norm, products of
the norms of two such functions are locally integrable, and so is the squared norm of their
sum; an `L²` function has locally integrable squared norm.
-/

@[expose] public section

open Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {Ω : Set X} {f : X → ℝ}

/-- Local L² bounds on an open cover imply L² on every compact subset of the
covered set. The index type and the measure need not be finite or countable. -/
theorem memLp_two_on_compact_of_open_cover
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : Ω ⊆ ⋃ i, U i)
    (hmem : ∀ i, MemLp f 2 (μ.restrict (U i)))
    {K : Set X} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    MemLp f 2 (μ.restrict K) := by
  have hloc : LocallyIntegrableOn (fun x ↦ f x ^ 2) Ω μ := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨U i, mem_nhdsWithin_of_mem_nhds ((hU i).mem_nhds hi),
      (hmem i).integrable_sq⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU (hKΩ.trans hcover)
  have hsub : K ⊆ ⋃ i : t, U i := fun x hx ↦ by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hf : AEStronglyMeasurable f (μ.restrict K) :=
    (AEStronglyMeasurable.iUnion fun i : t ↦ (hmem i).aestronglyMeasurable).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  exact (memLp_two_iff_integrable_sq hf).mpr (hloc.integrableOn_compact_subset hKΩ hK)

section SquareIntegrable

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {g : X → E} {h : X → F}

/-- An `L²` function has locally integrable squared norm. -/
theorem MemLp.locallyIntegrable_norm_sq (hg : MemLp g 2 μ) :
    LocallyIntegrable (fun x ↦ ‖g x‖ ^ 2) μ :=
  ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg).locallyIntegrable

/-- A function with locally integrable squared norm has locally integrable norm. -/
theorem locallyIntegrable_norm_of_sq [IsLocallyFiniteMeasure μ]
    (hg : AEStronglyMeasurable g μ) (h2 : LocallyIntegrable (fun x ↦ ‖g x‖ ^ 2) μ) :
    LocallyIntegrable (fun x ↦ ‖g x‖) μ := by
  refine ((locallyIntegrable_const 1).add h2).mono hg.norm (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_norm]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖g x‖ ^ 2)]
  nlinarith [sq_nonneg (‖g x‖ - 1), norm_nonneg (g x)]

/-- The product of the norms of two functions with locally integrable squared norms is locally
integrable. -/
theorem locallyIntegrable_norm_mul_norm (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) (hg2 : LocallyIntegrable (fun x ↦ ‖g x‖ ^ 2) μ)
    (hh2 : LocallyIntegrable (fun x ↦ ‖h x‖ ^ 2) μ) :
    LocallyIntegrable (fun x ↦ ‖g x‖ * ‖h x‖) μ := by
  refine (hg2.add hh2).mono (hg.norm.mul hh.norm) (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_norm]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g x‖ ^ 2 + ‖h x‖ ^ 2)]
  nlinarith [sq_nonneg (‖g x‖ - ‖h x‖), norm_nonneg (g x), norm_nonneg (h x)]

/-- The squared norm of a sum of two functions with locally integrable squared norms is locally
integrable. -/
theorem locallyIntegrable_norm_add_sq {g h : X → E} (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) (hg2 : LocallyIntegrable (fun x ↦ ‖g x‖ ^ 2) μ)
    (hh2 : LocallyIntegrable (fun x ↦ ‖h x‖ ^ 2) μ) :
    LocallyIntegrable (fun x ↦ ‖g x + h x‖ ^ 2) μ := by
  refine ((hg2.add hh2).smul (2 : ℝ)).mono ((hg.add hh).norm.pow 2)
    (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, norm_pow, norm_norm]
  rw [Real.norm_of_nonneg (by positivity)]
  have hle := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (g x) (h x)) 2
  nlinarith [norm_nonneg (g x), norm_nonneg (h x), sq_nonneg (‖g x‖ - ‖h x‖)]

end SquareIntegrable

/-- A locally integrable real function times a continuous compactly supported one is integrable:
`LocallyIntegrable.integrable_smul_right_of_hasCompactSupport` for real multiplication. -/
theorem LocallyIntegrable.integrable_mul_right_of_hasCompactSupport [OpensMeasurableSpace X]
    [T2Space X] {u v : X → ℝ} (hu : LocallyIntegrable u μ) (hv : Continuous v)
    (hvc : HasCompactSupport v) : Integrable (fun x ↦ u x * v x) μ :=
  hu.integrable_smul_right_of_hasCompactSupport hv hvc

end MeasureTheory
