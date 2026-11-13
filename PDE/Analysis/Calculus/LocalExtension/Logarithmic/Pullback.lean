/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Composition
public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Radial

import CAS.ExactTactic

/-!
# Hessian bounds for logarithmic cutoff pullbacks

The second chain rule controls the full bilinear operator norm by the outer
Hessian and the curvature of the inner map. For the radial logarithmic cutoff,
the same fixed scalar constant gives weighted estimates after a coordinate
change. The sharper estimate retains one factor of the coordinate radius in
front of the coordinate Hessian bound.
-/

@[expose] public noncomputable section

open Function Set
open scoped ContDiff

namespace PDE.Analysis

section Composition

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full second Fréchet derivative of a composition is bounded by the outer
Hessian times the squared inner derivative norm, plus the outer derivative
norm times the inner Hessian norm. Only local `C²` regularity is required. -/
theorem norm_fderiv_fderiv_comp_le {f : E → F} {g : D → E} {x : D}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ g)) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (g x)‖ * ‖fderiv ℝ g x‖ ^ 2 +
        ‖fderiv ℝ f (g x)‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  have hDcomp := ((hf.comp x hg).fderiv_right (m := 1) (by decide)).differentiableAt_one
  have hDg := (hg.fderiv_right (m := 1) (by decide)).differentiableAt_one
  have hchain (v w : D) :
      fderiv ℝ (fderiv ℝ (f ∘ g)) x v w =
        fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
          fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
    have h := fderiv_fderiv_comp_apply hf hg v w
    rw [fderiv_clm_apply hDcomp (differentiableAt_const w),
      fderiv_clm_apply hDg (differentiableAt_const w)] at h
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using h
  refine (fderiv ℝ (fderiv ℝ (f ∘ g)) x).opNorm_le_bound₂ ?_ ?_
  · exact add_nonneg
      (mul_nonneg (fderiv ℝ (fderiv ℝ f) (g x)).opNorm_nonneg (sq_nonneg _))
      (mul_nonneg (fderiv ℝ f (g x)).opNorm_nonneg
        (fderiv ℝ (fderiv ℝ g) x).opNorm_nonneg)
  · intro v w
    rw [hchain]
    calc
      ‖fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
          fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w)‖ ≤
          ‖fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)‖ +
            ‖fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (g x)‖ *
            (‖fderiv ℝ g x‖ * ‖v‖) * (‖fderiv ℝ g x‖ * ‖w‖) +
          ‖fderiv ℝ f (g x)‖ * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖v‖ * ‖w‖) :=
        add_le_add
          ((fderiv ℝ (fderiv ℝ f) (g x)).le_of_opNorm₂_le_of_le le_rfl
            ((fderiv ℝ g x).le_opNorm v) ((fderiv ℝ g x).le_opNorm w))
          ((fderiv ℝ f (g x)).le_opNorm_of_le
            ((fderiv ℝ (fderiv ℝ g) x).le_opNorm₂ v w))
      _ = (‖fderiv ℝ (fderiv ℝ f) (g x)‖ * ‖fderiv ℝ g x‖ ^ 2 +
          ‖fderiv ℝ f (g x)‖ * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖v‖ * ‖w‖ := by
        cas

end Composition

section Radial

variable {D E : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One constant, chosen before the cutoff parameters and the coordinate map,
controls both weighted derivatives of the actual radial cutoff pullback.
Smoothness on any supplied set and both closed plateaus transfer by composition.
The quantitative estimate needs only local `C²` coordinates. Its curvature term
is `‖z x‖ * B`, which can be replaced by `B` when `‖z x‖ ≤ 1`. -/
theorem exists_pos_radialLogarithmicCutoff_pullback_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ δ L : ℝ, 0 < δ → 1 ≤ L → ∀ z : D → E,
      (∀ s : Set D, ContDiffOn ℝ ∞ z s →
        ContDiffOn ℝ ∞ (radialLogarithmicCutoff δ L ∘ z) s) ∧
      (∀ x : D, ‖z x‖ ≤ δ * Real.exp (-L) →
        (radialLogarithmicCutoff δ L ∘ z) x = 1) ∧
      (∀ x : D, δ ≤ ‖z x‖ → (radialLogarithmicCutoff δ L ∘ z) x = 0) ∧
      (∀ x : D, (radialLogarithmicCutoff δ L ∘ z) x ∈ Icc (0 : ℝ) 1) ∧
      (∀ (x : D) (A B : ℝ), ContDiffAt ℝ 2 z x → 0 < ‖z x‖ →
        ‖fderiv ℝ z x‖ ≤ A → ‖fderiv ℝ (fderiv ℝ z) x‖ ≤ B →
        ‖z x‖ * ‖fderiv ℝ (radialLogarithmicCutoff δ L ∘ z) x‖ ≤ C * A / L ∧
        ‖z x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ
          (radialLogarithmicCutoff δ L ∘ z)) x‖ ≤ C * (3 * A ^ 2 + ‖z x‖ * B) / L ∧
        (‖z x‖ ≤ 1 →
          ‖z x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ
            (radialLogarithmicCutoff δ L ∘ z)) x‖ ≤ C * (3 * A ^ 2 + B) / L)) := by
  obtain ⟨C, hC, hradial⟩ := exists_pos_radialLogarithmicCutoff_bounds (E := E)
  refine ⟨C, hC, ?_⟩
  intro δ L hδ hL z
  obtain ⟨hχ, hone, hzero, hrange, _, hbounds⟩ := hradial δ L hδ hL
  refine ⟨(fun s hz ↦ hχ.comp_contDiffOn hz),
    (fun x hx ↦ hone (z x) hx), (fun x hx ↦ hzero (z x) hx),
    (fun x ↦ hrange (z x)), ?_⟩
  intro x A B hz hr hA hB
  let χ : E → ℝ := radialLogarithmicCutoff δ L
  have hχ2 : ContDiffAt ℝ 2 χ (z x) := (hχ.of_le (by simp)).contDiffAt
  have hA0 : 0 ≤ A := (fderiv ℝ z x).opNorm_nonneg.trans hA
  have hB0 : 0 ≤ B := (fderiv ℝ (fderiv ℝ z) x).opNorm_nonneg.trans hB
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hweighted := hbounds (z x) (norm_pos_iff.mp hr)
  have hfirst : ‖fderiv ℝ (χ ∘ z) x‖ ≤ ‖fderiv ℝ χ (z x)‖ * A := by
    rw [fderiv_comp x (hχ2.differentiableAt two_ne_zero)
      (hz.differentiableAt two_ne_zero)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left hA (fderiv ℝ χ (z x)).opNorm_nonneg)
  have hsecond : ‖fderiv ℝ (fderiv ℝ (χ ∘ z)) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ χ) (z x)‖ * A ^ 2 + ‖fderiv ℝ χ (z x)‖ * B := by
    refine (norm_fderiv_fderiv_comp_le hχ2 hz).trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (fderiv ℝ z x).opNorm_nonneg hA 2)
        (fderiv ℝ (fderiv ℝ χ) (z x)).opNorm_nonneg
    · exact mul_le_mul_of_nonneg_left hB (fderiv ℝ χ (z x)).opNorm_nonneg
  have hsharp : ‖z x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ (χ ∘ z)) x‖ ≤
      C * (3 * A ^ 2 + ‖z x‖ * B) / L := by
    calc
      ‖z x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ (χ ∘ z)) x‖ ≤
          ‖z x‖ ^ 2 * (‖fderiv ℝ (fderiv ℝ χ) (z x)‖ * A ^ 2 +
            ‖fderiv ℝ χ (z x)‖ * B) :=
        mul_le_mul_of_nonneg_left hsecond (sq_nonneg ‖z x‖)
      _ = (‖z x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ χ) (z x)‖) * A ^ 2 +
          (‖z x‖ * ‖fderiv ℝ χ (z x)‖) * (‖z x‖ * B) := by cas
      _ ≤ (3 * C / L) * A ^ 2 + (C / L) * (‖z x‖ * B) := add_le_add
        (mul_le_mul_of_nonneg_right hweighted.2 (sq_nonneg A))
        (mul_le_mul_of_nonneg_right hweighted.1 (mul_nonneg hr.le hB0))
      _ = C * (3 * A ^ 2 + ‖z x‖ * B) / L := by cas using [hLpos]
  refine ⟨?_, hsharp, ?_⟩
  · calc
      ‖z x‖ * ‖fderiv ℝ (χ ∘ z) x‖ ≤ ‖z x‖ * (‖fderiv ℝ χ (z x)‖ * A) :=
        mul_le_mul_of_nonneg_left hfirst hr.le
      _ = (‖z x‖ * ‖fderiv ℝ χ (z x)‖) * A := by cas
      _ ≤ (C / L) * A := mul_le_mul_of_nonneg_right hweighted.1 hA0
      _ = C * A / L := by cas using [hLpos]
  · intro hr1
    refine hsharp.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hC.le) hLpos.le)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hB0

end Radial

end PDE.Analysis
