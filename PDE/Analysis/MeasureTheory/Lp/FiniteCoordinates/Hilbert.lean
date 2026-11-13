/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Finite ℓ² products of Bochner L² classes

Finite families of L² classes assemble into the `PiLp 2` product,
with a common almost-everywhere representative identity. The squared norm is
the sum of the component squared norms, including an empty component family.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {μ : Measure α}

/-- The squared Bochner L² norm of a finite ℓ² product is the sum of the squared
norms of any almost-everywhere identified coordinate classes. -/
theorem norm_sq_piLp_of_ae_coordinates
    (u : Lp (PiLp 2 E) 2 μ) (v : ∀ i, Lp (E i) 2 μ)
    (h : ∀ᵐ x ∂μ, ∀ i, u x i = v i x) :
    ‖u‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [Lp.norm_sq_eq_integral_norm_sq]
  calc
    (∫ x, ‖u x‖ ^ 2 ∂μ) = ∫ x, ∑ i, ‖v i x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [h] with x hx
      simp only [PiLp.norm_sq_eq_of_L2, hx]
    _ = ∑ i, ∫ x, ‖v i x‖ ^ 2 ∂μ :=
      integral_finsetSum _ fun i _ ↦ (Lp.memLp (v i)).integrable_norm_pow (by norm_num)
    _ = ∑ i, ‖v i‖ ^ 2 := by
      simp only [Lp.norm_sq_eq_integral_norm_sq]

/-- Finite L² families give a Bochner class in the finite ℓ²
product, with its exact squared norm and all component representatives. -/
theorem exists_piLp_L2 (v : ∀ i, Lp (E i) 2 μ) :
    ∃ u : Lp (PiLp 2 E) 2 μ,
      (∀ᵐ x ∂μ, ∀ i, u x i = v i x) ∧ ‖u‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  let f (x : α) : PiLp 2 E := WithLp.toLp 2 (fun i ↦ v i x)
  have hf : MemLp f 2 μ := memLp_piLp_iff.mpr fun i ↦ Lp.memLp (v i)
  have h : ∀ᵐ x ∂μ, ∀ i, hf.toLp f x i = v i x := by
    filter_upwards [hf.coeFn_toLp] with x hx
    intro i
    rw [hx]
  exact ⟨hf.toLp f, h, norm_sq_piLp_of_ae_coordinates (hf.toLp f) v h⟩

end MeasureTheory.Lp
