/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
public import PDE.Elliptic.Variational.PrincipalForms

/-!
# Gradient reactions on the zero-boundary Sobolev space

A globally Lipschitz scalar function acts on the `L²` gradient. Boundedness of the
domain makes its constant offset integrable; no normalization at zero is required. The
reaction defines a dual load whose difference is controlled by the gradient difference.
Keeping that sharper bound is essential for absorbing an arbitrarily large Lipschitz
constant into the mass term.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace.GradientReaction

variable {n : ℕ} {Ω : Set (ℝ^n)} {K : ℝ≥0} {b : ℝ^n → ℝ}

/-- A Lipschitz reaction has an integrable constant offset on a bounded domain. -/
theorem memLp_comp (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (g : Lp (ℝ^n) 2 (domainMeasure n Ω)) :
    MemLp (fun x ↦ b (g x)) 2 (domainMeasure n Ω) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  exact hb.comp_memLp_of_memLp_const (memLp_const (b 0)) (Lp.memLp g)

/-- The scalar `L²` field `b(Du)`, with the weak gradient as input. -/
def reaction (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u : H¹₀(Ω)) : DerivLp n 2 Ω :=
  Lp.superposition (fun _ ↦ b) (memLp_comp hbounded hb) (∇ (u : H¹(Ω)))

/-- The reaction's representative is pointwise composition almost everywhere. -/
theorem reaction_coeFn (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u : H¹₀(Ω)) :
    (reaction hbounded hb u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ b (∇ (u : H¹(Ω)) x) :=
  Lp.coeFn_superposition _ _ _

/-- The reaction difference is controlled by the gradient difference, without an offset. -/
theorem norm_reaction_sub_le (hbounded : Bornology.IsBounded Ω)
    (hb : LipschitzWith K b) (u v : H¹₀(Ω)) :
    ‖reaction hbounded hb u - reaction hbounded hb v‖ ≤
      (K : ℝ) * ‖∇ ((u - v : H¹₀(Ω)) : H¹(Ω))‖ := by
  change ‖reaction hbounded hb u - reaction hbounded hb v‖ ≤
    (K : ℝ) * ‖gradientCLM (u - v)‖
  simpa only [reaction, map_sub, ← wkpGradientCLM_h10SubtypeL, h10SubtypeL_apply] using
    (hb.lipschitzWith_superposition (memLp_comp hbounded hb)).norm_sub_le
      (gradientCLM u) (gradientCLM v)

/-- Superposition after the gradient is globally Lipschitz in the full `H¹` norm. -/
theorem lipschitzWith_reaction (hbounded : Bornology.IsBounded Ω)
    (hb : LipschitzWith K b) : LipschitzWith K (reaction hbounded hb) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  exact (norm_reaction_sub_le hbounded hb u v).trans
    (mul_le_mul_of_nonneg_left (gradientCLM_norm_le (u - v)) K.coe_nonneg)

/-- The gradient reaction as a continuous linear functional in the test function. -/
def load (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u : H¹₀(Ω)) : StrongDual ℝ (H¹₀(Ω)) :=
  loadFunctional (reaction hbounded hb u)

/-- The nonlinear load has the expected `L²` pairing with the test function. -/
theorem load_apply (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u v : H¹₀(Ω)) :
    load hbounded hb u v = ⟪reaction hbounded hb u, baseCoordCLM v⟫_ℝ :=
  rfl

/-- The pointwise reaction paired with a test field is integrable. -/
theorem integrable_reaction_mul (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u v : H¹₀(Ω)) :
    Integrable (fun x ↦ b (∇ (u : H¹(Ω)) x) * baseCoordCLM v x) (domainMeasure n Ω) := by
  apply ((Lp.memLp (reaction hbounded hb u)).integrable_mul (Lp.memLp (baseCoordCLM v))).congr
  filter_upwards [reaction_coeFn hbounded hb u] with x hx
  exact congrArg (· * baseCoordCLM v x) hx

/-- The nonlinear dual load is the integral of the original pointwise reaction. -/
theorem load_eq_integral (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u v : H¹₀(Ω)) :
    load hbounded hb u v =
      ∫ x, b (∇ (u : H¹(Ω)) x) * baseCoordCLM v x ∂domainMeasure n Ω := by
  rw [load, loadFunctional_eq_integral]
  apply integral_congr_ae
  filter_upwards [reaction_coeFn hbounded hb u] with x hx
  exact congrArg (· * baseCoordCLM v x) hx

/-- The dual reaction map is globally Lipschitz. -/
theorem lipschitzWith_load (hbounded : Bornology.IsBounded Ω)
    (hb : LipschitzWith K b) : LipschitzWith K (load hbounded hb) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖load hbounded hb u - load hbounded hb v‖
        = ‖loadFunctional (reaction hbounded hb u - reaction hbounded hb v)‖ := by
          rw [loadFunctional_sub]
          rfl
    _ ≤ ‖reaction hbounded hb u - reaction hbounded hb v‖ := norm_loadFunctional_le _
    _ ≤ (K : ℝ) * ‖u - v‖ := (lipschitzWith_reaction hbounded hb).norm_sub_le u v

/-- The cross term in the monotonicity estimate retains both coordinate norms. -/
theorem abs_load_sub_apply_le (hbounded : Bornology.IsBounded Ω)
    (hb : LipschitzWith K b) (u v : H¹₀(Ω)) :
    |(load hbounded hb u - load hbounded hb v) (u - v)| ≤
      (K : ℝ) * ‖∇ ((u - v : H¹₀(Ω)) : H¹(Ω))‖ * ‖baseCoordCLM (u - v)‖ := by
  change |⟪reaction hbounded hb u, baseCoordCLM (u - v)⟫_ℝ -
    ⟪reaction hbounded hb v, baseCoordCLM (u - v)⟫_ℝ| ≤ _
  rw [← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_reaction_sub_le hbounded hb u v) (norm_nonneg _))

end SobolevSpace.GraphSpace.GradientReaction
