/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Constant
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness under a strict exponential growth bound

A homogeneous real-rate orbit cannot grow more slowly than its exponential
mode in both time directions. This removes the unwanted homogeneous terms in
the whole-line Green representation.
-/

@[expose] public noncomputable section

open Filter NormedSpace
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integrating factor of a homogeneous real-rate equation is constant.
This is the scalar-rate specialization of the bounded-operator identity. -/
theorem exp_neg_mul_smul_eq_initial {b : ℝ} {u : ℝ → E}
    (hu : ∀ t, HasDerivAt u (b • u t) t) (t : ℝ) :
    Real.exp (-(b * t)) • u t = u 0 := by
  have he (r : ℝ) : exp (r • (1 : E →L[ℝ] E)) = Real.exp r • (1 : E →L[ℝ] E) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using
      (algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := E →L[ℝ] E) r).symm
  have hd (s : ℝ) : HasDerivAt (fun r ↦ Real.exp (-(b * r)) • u r) 0 s := by
    have h := hasDerivAt_exp_sub_apply (b • (1 : E →L[ℝ] E))
      (g := (0 : E)) (by simpa using hu s) 0
    simpa only [zero_sub, smul_smul, he, smul_apply,
      one_apply_eq_self, map_zero, smul_zero, neg_mul, mul_neg, mul_comm] using h
  have h := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simpa only [mul_zero, neg_zero, Real.exp_zero, one_smul] using h

/-- A growing homogeneous mode vanishes if a strictly smaller exponential
bound holds in positive time. -/
theorem eq_zero_of_hasDerivAt_of_exp_bound_atTop {b η C : ℝ} {u : ℝ → E}
    (hu : ∀ t, HasDerivAt u (b • u t) t) (hgap : η < b)
    (hbound : ∀ t, 0 ≤ t → ‖u t‖ ≤ Real.exp (η * t) * C) :
    u = 0 := by
  have hle (t : ℝ) (ht : 0 ≤ t) :
      ‖u 0‖ ≤ Real.exp ((η - b) * t) * C := by
    rw [← exp_neg_mul_smul_eq_initial hu t, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(b * t)) * ‖u t‖ ≤
          Real.exp (-(b * t)) * (Real.exp (η * t) * C) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_nonneg _)
      _ = Real.exp ((η - b) * t) * C := by
        rw [← mul_assoc, ← Real.exp_add, sub_mul, sub_eq_add_neg, add_comm (η * t)]
  have hlim : Tendsto (fun t : ℝ ↦ Real.exp ((η - b) * t) * C) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ ↦ (η - b) * t) atTop atBot :=
      tendsto_const_nhds.neg_mul_atTop (sub_neg.mpr hgap) tendsto_id
    simpa only [zero_mul, Function.comp_apply] using
      (Real.tendsto_exp_atBot.comp ht).mul_const C
  have hzero : u 0 = 0 := norm_eq_zero.mp <| le_antisymm
    (ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, hle⟩)) (norm_nonneg _)
  funext t
  have h := exp_neg_mul_smul_eq_initial hu t
  rw [hzero] at h
  exact (smul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)

/-- A homogeneous mode with rate outside the allowed symmetric exponential
weight has only the zero whole-line orbit. -/
theorem eq_zero_of_hasDerivAt_of_exponential_bound {b η C : ℝ} {u : ℝ → E}
    (hu : ∀ t, HasDerivAt u (b • u t) t) (hgap : η < |b|)
    (hbound : ∀ t, ‖u t‖ ≤ Real.exp (η * |t|) * C) :
    u = 0 := by
  by_cases hb : 0 ≤ b
  · apply eq_zero_of_hasDerivAt_of_exp_bound_atTop (C := C) hu
      (by simpa only [abs_of_nonneg hb] using hgap)
    intro t ht
    simpa only [abs_of_nonneg ht] using hbound t
  · have hbn : b < 0 := lt_of_not_ge hb
    have hneg (t : ℝ) : HasDerivAt (fun s ↦ u (-s)) ((-b) • u (-t)) t := by
      simpa only [neg_smul, one_smul, Function.comp_def] using
        (hu (-t)).scomp t ((hasDerivAt_id t).neg)
    have hz := eq_zero_of_hasDerivAt_of_exp_bound_atTop hneg
      (by simpa only [abs_of_neg hbn] using hgap) (C := C) (by
        intro t ht
        simpa only [abs_neg, abs_of_nonneg ht] using hbound (-t))
    funext t
    simpa only [neg_neg, Pi.zero_apply] using congrFun hz (-t)

end PDE.Analysis.Evolution
