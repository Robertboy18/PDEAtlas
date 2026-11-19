/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Fields homogeneous of degree -1

For `A` homogeneous of degree `0`, the field `x ↦ ‖x‖⁻¹ A x` is homogeneous of degree `-1`, and
it is as smooth as `A` away from the origin. A function `u` homogeneous of degree `-1` vanishes
at the origin; if it is continuous away from the origin of a finite-dimensional space, it is
bounded by a multiple of `‖x‖⁻¹`, since it is bounded on the compact unit sphere. A function
continuous away from one point is almost everywhere strongly measurable for every measure
without atoms.
-/

@[expose] public section

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- For `A` homogeneous of degree `0`, the field `‖x‖⁻¹ A x` is homogeneous of degree `-1`. -/
theorem inv_norm_smul_apply_smul_of_homogeneous [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → F} (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) (x : E) {c : ℝ} (hc : 0 < c) :
    ‖c • x‖⁻¹ • A (c • x) = c⁻¹ • (‖x‖⁻¹ • A x) := by
  rw [hA x c hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_inv, smul_smul]

/-- Away from the origin, `‖x‖⁻¹ A x` is as smooth as `A`. -/
theorem contDiffAt_inv_norm_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E → F}
    {x : E} {m : WithTop ℕ∞} (hx : x ≠ 0) (hA : ContDiffAt ℝ m A x) :
    ContDiffAt ℝ m (fun y ↦ ‖y‖⁻¹ • A y) x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul hA

/-- A function homogeneous of degree `-1` vanishes at the origin. -/
theorem apply_zero_eq_zero_of_homogeneous [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → F}
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x) : u 0 = 0 := by
  have h := hhom 0 2 two_pos
  rw [smul_zero] at h
  have h2 : (1 - 2⁻¹ : ℝ) • u 0 = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- A function homogeneous of degree `-1` and continuous away from the origin of a
finite-dimensional space is bounded by a multiple of `‖x‖⁻¹`. -/
theorem exists_norm_le_mul_inv_norm_of_homogeneous [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → F}
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContinuousAt u x) : ∃ M, 0 ≤ M ∧ ∀ x, ‖u x‖ ≤ M * ‖x‖⁻¹ := by
  have hcont : ContinuousOn u (Metric.sphere 0 1) := fun x hx ↦
    (hu x (by rintro rfl; simp at hx)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [apply_zero_eq_zero_of_homogeneous hhom]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by simp [norm_smul, hpos.ne']
    have hxy : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    calc ‖u x‖ = ‖u (‖x‖ • (‖x‖⁻¹ • x))‖ := by rw [← hxy]
      _ = ‖x‖⁻¹ * ‖u (‖x‖⁻¹ • x)‖ := by
        rw [hhom _ _ hpos, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
      _ ≤ ‖x‖⁻¹ * max C 0 :=
        mul_le_mul_of_nonneg_left ((hC _ hy).trans (le_max_left _ _)) (inv_nonneg.mpr hpos.le)
      _ = max C 0 * ‖x‖⁻¹ := mul_comm _ _

omit [NormedSpace ℝ F] in
/-- A function continuous away from one point is almost everywhere strongly measurable for
every measure without atoms. -/
theorem aestronglyMeasurable_of_continuousAt_of_ne [TopologicalSpace E] [T1Space E]
    [SecondCountableTopologyEither E F] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} [NullSingletonClass μ] {x₀ : E} {u : E → F}
    (hu : ∀ x, x ≠ x₀ → ContinuousAt u x) : AEStronglyMeasurable u μ := by
  have hc : ContinuousOn u {x₀}ᶜ := fun x hx ↦ (hu x hx).continuousWithinAt
  have h := hc.aestronglyMeasurable (μ := μ) (measurableSet_singleton x₀).compl
  rwa [restrict_compl_singleton] at h

end PDE
