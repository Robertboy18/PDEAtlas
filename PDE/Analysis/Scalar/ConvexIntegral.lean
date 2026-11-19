/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Continuous
import CAS.IntegrationTactic

/-!
# Integral bounds for strictly convex scalar functions

The strict upper Hermite–Hadamard inequality on a real interval. A strictly
convex function lies strictly below its endpoint chord
at an interior point, so its integral is strictly smaller than the area of
the corresponding trapezoid.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Scalar

open MeasureTheory

private def endpointChord (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b

private theorem intervalIntegral_endpointChord
    (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, endpointChord f a b x) =
      (b - a) * (f a + f b) / 2 := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  cas using hne

/-- The strict upper Hermite–Hadamard inequality on a nondegenerate real
interval. -/
theorem intervalIntegral_lt_trapezoid_of_strictConvexOn
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : StrictConvexOn ℝ Set.univ f) (hab : a < b) :
    (∫ x in a..b, f x) <
      (b - a) * (f a + f b) / 2 := by
  let chord : ℝ → ℝ := endpointChord f a b
  have hcontinuous : Continuous f :=
    continuousOn_univ.mp (hf.convexOn.continuousOn isOpen_univ)
  have hdenom : 0 < b - a := sub_pos.mpr hab
  have hle : ∀ x ∈ Set.Ioc a b, f x ≤ chord x := by
    intro x hx
    have hleft : 0 ≤ (b - x) / (b - a) :=
      div_nonneg (sub_nonneg.mpr hx.2) hdenom.le
    have hright : 0 ≤ (x - a) / (b - a) :=
      div_nonneg (sub_nonneg.mpr hx.1.le) hdenom.le
    have hsum :
        (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
      field_simp
      ring
    have hpoint :
        (b - x) / (b - a) * a +
            (x - a) / (b - a) * b =
          x := by
      field_simp
      ring
    have hconvex :=
      hf.convexOn.2 (Set.mem_univ a) (Set.mem_univ b)
        hleft hright hsum
    calc
      f x =
          f ((b - x) / (b - a) * a +
            (x - a) / (b - a) * b) := by
        rw [hpoint]
      _ ≤
          (b - x) / (b - a) * f a +
            (x - a) / (b - a) * f b := by
        simpa only [smul_eq_mul] using hconvex
      _ = chord x := by rfl
  have hmidpoint : (a + b) / 2 ∈ Set.Icc a b := by
    constructor <;> linarith
  have hstrict : f ((a + b) / 2) < chord ((a + b) / 2) := by
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    have hconvex :=
      hf.2 (Set.mem_univ a) (Set.mem_univ b) hab.ne
        hhalf hhalf hsum
    have hpoint :
        (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b =
          (a + b) / 2 := by
      ring
    have hchord :
        (1 / 2 : ℝ) * f a + (1 / 2 : ℝ) * f b =
          chord ((a + b) / 2) := by
      dsimp [chord, endpointChord]
      cas
    calc
      f ((a + b) / 2) =
          f ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) := by
        rw [hpoint]
      _ < (1 / 2 : ℝ) * f a + (1 / 2 : ℝ) * f b := by
        simpa only [smul_eq_mul] using hconvex
      _ = chord ((a + b) / 2) := hchord
  have hchordContinuous : Continuous chord := by
    unfold chord endpointChord
    fun_prop
  have hcomparison :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab hcontinuous.continuousOn hchordContinuous.continuousOn hle
      ⟨(a + b) / 2, hmidpoint, hstrict⟩
  rw [intervalIntegral_endpointChord f hab] at hcomparison
  exact hcomparison

end PDE.Analysis.Scalar
