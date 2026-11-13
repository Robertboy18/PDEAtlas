/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition

/-!
# Lipschitz superposition with an integrable offset

A Lipschitz map need not vanish at zero to act on `Lᵖ`: it suffices that its
constant value at zero belongs to the output `Lᵖ` space. This includes every
Lipschitz map on a finite measure space. Subtracting the offset reduces
membership to Mathlib's zero-preserving composition theorem.

The superposition construction keeps the scalar Lipschitz constant. Its proof compares
differences pointwise, so it does not require the measure to be finite or the target to be
complete.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- A Lipschitz map preserves `Lᵖ` whenever its constant offset belongs to `Lᵖ`. -/
theorem LipschitzWith.comp_memLp_of_memLp_const
    {g : E → F} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hzero : MemLp (fun _ : α ↦ g 0) p μ)
    {u : α → E} (hu : MemLp u p μ) :
    MemLp (fun x ↦ g (u x)) p μ := by
  have hsub : LipschitzWith K (fun z ↦ g z - g 0) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [sub_eq_add_neg, dist_add_right] using hg.dist_le_mul x y
  have hmem := hsub.comp_memLp (sub_self (g 0)) hu
  have hsum := hmem.add hzero
  change MemLp (fun x ↦ (g (u x) - g 0) + g 0) p μ at hsum
  simpa only [sub_add_cancel] using hsum

/-- Pointwise application of a Lipschitz map has the same Lipschitz constant
on `Lᵖ`. The membership premise is supplied, for example, by the offset theorem. -/
theorem LipschitzWith.lipschitzWith_superposition
    [Fact (1 ≤ p)] {g : E → F} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hmem : ∀ u : Lp E p μ, MemLp (fun x ↦ g (u x)) p μ) :
    LipschitzWith K (Lp.superposition (fun _ ↦ g) hmem) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards
    [Lp.coeFn_sub (Lp.superposition (fun _ ↦ g) hmem u)
      (Lp.superposition (fun _ ↦ g) hmem v),
     Lp.coeFn_superposition (fun _ ↦ g) hmem u,
     Lp.coeFn_superposition (fun _ ↦ g) hmem v,
     Lp.coeFn_sub u v] with x hsub hu hv huv
  simpa only [hsub, Pi.sub_apply, hu, hv, huv] using hg.norm_sub_le (u x) (v x)
