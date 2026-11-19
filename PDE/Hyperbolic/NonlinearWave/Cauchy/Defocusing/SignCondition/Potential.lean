/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.Basic

/-!
# Scalar potentials under the wave sign condition

The condition `s * f s ≥ 0` makes the primitive based at zero nonnegative.
It imposes no monotonicity or growth bound on the reaction. Multiplying the
reaction by a continuous factor between zero and one decreases its potential;
this is the domination needed for the arbitrary-growth approximation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Continuity and the sign condition force the reaction to vanish at zero. -/
theorem reaction_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ z, 0 ≤ z * f z) : f 0 = 0 := by
  apply le_antisymm
  · apply le_on_closure (s := Iio (0 : ℝ)) (f := f) (g := fun _ ↦ 0)
      (fun z hz ↦ (mul_nonneg_iff.mp (hs z)).resolve_left (fun h ↦ (not_le_of_gt hz) h.1) |>.2)
      hf.continuousOn continuousOn_const
    simp
  · apply le_on_closure (s := Ioi (0 : ℝ)) (f := fun _ ↦ 0) (g := f)
      (fun z hz ↦ (mul_nonneg_iff.mp (hs z)).resolve_right (fun h ↦ (not_le_of_gt hz) h.1) |>.2)
      continuousOn_const hf.continuousOn
    simp

/-- On the nonnegative half-line, the reaction is nonnegative. -/
theorem reaction_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ z, 0 ≤ z * f z) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ f z := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [reaction_zero hf hs]
  · exact (mul_nonneg_iff.mp (hs z)).resolve_right (fun h ↦ (not_le_of_gt hz) h.1) |>.2

/-- On the nonpositive half-line, the reaction is nonpositive. -/
theorem reaction_nonpos {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ z, 0 ≤ z * f z) {z : ℝ} (hz : z ≤ 0) : f z ≤ 0 := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [reaction_zero hf hs]
  · exact (mul_nonneg_iff.mp (hs z)).resolve_left (fun h ↦ (not_le_of_gt hz) h.1) |>.2

/-- The sign condition gives nonnegative potential at every amplitude. -/
theorem primitive_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ z, 0 ≤ z * f z) (z : ℝ) : 0 ≤ primitive f z := by
  rcases le_total 0 z with hz | hz
  · exact intervalIntegral.integral_nonneg hz fun s hs' ↦ reaction_nonneg hf hs hs'.1
  · unfold primitive
    rw [intervalIntegral.integral_symm]
    apply neg_nonneg.mpr
    simpa using intervalIntegral.integral_mono_on hz (hf.intervalIntegrable z 0)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume z 0)
      (fun s hs' ↦ reaction_nonpos hf hs hs'.2)

/-- Cutting off a sign-preserving reaction decreases its normalized potential. -/
theorem primitive_mul_le {f χ : ℝ → ℝ} (hf : Continuous f) (hχ : Continuous χ)
    (hs : ∀ z, 0 ≤ z * f z) (hχ₁ : ∀ z, χ z ≤ 1)
    (z : ℝ) : primitive (fun s ↦ χ s * f s) z ≤ primitive f z := by
  have hsign (s : ℝ) : 0 ≤ s * ((1 - χ s) * f s) := by
    rw [mul_left_comm]
    exact mul_nonneg (sub_nonneg.mpr (hχ₁ s)) (hs s)
  have h := primitive_nonneg ((continuous_const.sub hχ).mul hf) hsign z
  have heq : primitive (fun s ↦ (1 - χ s) * f s) z =
      primitive f z - primitive (fun s ↦ χ s * f s) z := by
    unfold primitive
    simp only [sub_mul, one_mul]
    exact intervalIntegral.integral_sub (hf.intervalIntegrable 0 z)
      ((hχ.mul hf).intervalIntegrable 0 z)
  change 0 ≤ primitive (fun s ↦ (1 - χ s) * f s) z at h
  rw [heq] at h
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
