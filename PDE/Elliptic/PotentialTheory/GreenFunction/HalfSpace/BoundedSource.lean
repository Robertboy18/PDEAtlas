/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# The planar half-space Green potential of bounded integrable sources

In the plane `G(y, x) = (2π)⁻¹ (log |x - y*| - log |x - y|)` with `y*` the reflection of `y`,
valid at the poles too since `log 0 = 0`. The two distances differ by at most `2|x₁|`, so
`|G(y, x)| ≤ (2π)⁻¹ (|log |x - y|| 1_{|x-y|<1} + |log |x - y*|| 1_{|x-y*|<1} + 2|x₁|)`:
the kernel is bounded away from its two poles and has integrable logarithmic singularities.
Hence every bounded source integrable on the upper half-plane has an absolutely convergent Green
potential at every point. No logarithmic moment of the source is needed: the pairing of the two
logarithms cancels their growth at infinity.

## Main results

* `halfSpaceGreenFunction_two_eq`: `G(y, x) = (2π)⁻¹ (log |x - y*| - log |x - y|)`.
* `abs_halfSpaceGreenFunction_two_le`: the displayed bound on `|G(y, x)|`.
* `hasIntegrableHalfSpaceGreenPotential_of_bounded`: a source bounded and integrable on the upper
  half-plane has an absolutely convergent Green potential at every point.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open SobolevSpace

namespace GreenFunction

/-- The planar half-space Green function in logarithmic form. -/
theorem halfSpaceGreenFunction_two_eq (y x : ℝ^2) :
    halfSpaceGreenFunction y x =
      1 / (2 * Real.pi) * (Real.log ‖x - HalfSpace.reflect 2 y‖ - Real.log ‖x - y‖) := by
  rw [halfSpaceGreenFunction, PotentialTheory.fundamentalSolution_two,
    PotentialTheory.fundamentalSolution_two]
  ring

/-- `|log b - log a| ≤ |log a| 1_{a<1} + |log b| 1_{b<1} + d` when `|a - b| ≤ d`. -/
private theorem abs_log_sub_log_le {a b d : ℝ} (hab : |a - b| ≤ d) :
    |Real.log b - Real.log a| ≤
      (if a < 1 then |Real.log a| else 0) + (if b < 1 then |Real.log b| else 0) + d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hab
  have hlog1 : ∀ {s t : ℝ}, 1 ≤ s → s ≤ t → Real.log t - Real.log s ≤ t - s := by
    intro s t hs hst
    have hs0 : 0 < s := by linarith
    rw [← Real.log_div (by linarith) hs0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) hs0)).trans ?_
    rw [div_sub_one hs0.ne', div_le_iff₀ hs0]
    nlinarith
  have hpos : ∀ {s : ℝ}, 1 ≤ s → s ≤ 1 + d → 0 ≤ Real.log s ∧ Real.log s ≤ d := fun {s} hs h ↦
    ⟨Real.log_nonneg hs, (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)⟩
  rw [abs_le] at hab
  by_cases ha1 : a < 1 <;> by_cases hb1 : b < 1 <;> simp only [ha1, hb1, ↓reduceIte]
  · have := abs_sub (Real.log b) (Real.log a); linarith [abs_nonneg (Real.log a)]
  · have hb' := hpos (not_lt.mp hb1) (by linarith)
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log a)]
  · have ha' := hpos (not_lt.mp ha1) (by linarith)
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log b), le_abs_self (Real.log b)]
  · rw [abs_le]
    rcases le_total a b with h | h
    · have := hlog1 (not_lt.mp ha1) h
      have := Real.log_le_log (by linarith) h
      constructor <;> linarith
    · have := hlog1 (not_lt.mp hb1) h
      have := Real.log_le_log (by linarith) h
      constructor <;> linarith

/-- **The planar Green function is bounded away from its poles**, with integrable logarithmic
singularities at the pole `y = x` and at the image pole `y = x*`. -/
theorem abs_halfSpaceGreenFunction_two_le (y x : ℝ^2) :
    |halfSpaceGreenFunction y x| ≤ 1 / (2 * Real.pi) *
      ((if ‖x - y‖ < 1 then |Real.log ‖x - y‖| else 0) +
        (if ‖HalfSpace.reflect 2 x - y‖ < 1 then |Real.log ‖HalfSpace.reflect 2 x - y‖| else 0) +
        2 * |x 1|) := by
  have hR : ‖x - HalfSpace.reflect 2 y‖ = ‖HalfSpace.reflect 2 x - y‖ := by
    rw [← HalfSpace.norm_reflect 2 (x - HalfSpace.reflect 2 y), HalfSpace.reflect_sub,
      HalfSpace.reflect_involutive]
  have hd : |‖x - y‖ - ‖HalfSpace.reflect 2 x - y‖| ≤ 2 * |x 1| := by
    refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
    rw [show x - y - (HalfSpace.reflect 2 x - y) = x - HalfSpace.reflect 2 x by abel,
      ← sq_eq_sq₀ (norm_nonneg _) (by positivity), EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two]
    simp [HalfSpace.reflect, PDE.Common.lastIndex]
    ring_nf
    rw [sq_abs]
  rw [halfSpaceGreenFunction_two_eq, hR, abs_mul, abs_of_pos (by positivity)]
  gcongr
  exact abs_log_sub_log_le hd

/-- The logarithmic singularity, cut off at radius one, is integrable. -/
private theorem integrable_indicator_log :
    Integrable fun z : ℝ^2 ↦ if ‖z‖ < 1 then |Real.log ‖z‖| else 0 := by
  have h := (PotentialTheory.locallyIntegrable_fundamentalSolution 2).integrableOn_isCompact
    (isCompact_closedBall (0 : ℝ^2) 1)
  have h1 : IntegrableOn (fun z ↦ 2 * Real.pi * ‖PotentialTheory.fundamentalSolution 2 z‖)
      (ball (0 : ℝ^2) 1) := (h.mono_set ball_subset_closedBall).norm.const_mul _
  have h' : IntegrableOn (fun z : ℝ^2 ↦ |Real.log ‖z‖|) (ball (0 : ℝ^2) 1) := by
    refine h1.congr_fun (fun z _ ↦ ?_) measurableSet_ball
    change 2 * Real.pi * ‖PotentialTheory.fundamentalSolution 2 z‖ = |Real.log ‖z‖|
    rw [PotentialTheory.fundamentalSolution_two, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    field_simp
  refine (h'.integrable_indicator measurableSet_ball).congr (Eventually.of_forall fun z ↦ ?_)
  by_cases hz : ‖z‖ < 1
  · rw [indicator_of_mem (by simpa using hz)]; simp [hz]
  · rw [indicator_of_notMem (by simpa using hz)]; simp [hz]

/-- **Bounded integrable sources have absolutely convergent Green potentials.** If `f` is
a.e.-strongly measurable on the upper half-plane, bounded there and integrable there, then its
Green integrand is integrable at every evaluation point. -/
theorem hasIntegrableHalfSpaceGreenPotential_of_bounded {f : ℝ^2 → ℝ} {B : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (HalfSpace.upper 2)))
    (hB : ∀ y ∈ HalfSpace.upper 2, |f y| ≤ B) (hf : IntegrableOn f (HalfSpace.upper 2)) :
    HasIntegrableHalfSpaceGreenPotential f := by
  intro x
  set F : ℝ^2 → ℝ := fun z ↦ if ‖z‖ < 1 then |Real.log ‖z‖| else 0
  have hF := integrable_indicator_log
  have hdom : Integrable (fun y ↦ 1 / (2 * Real.pi) * (B * (F (x - y) +
      F (HalfSpace.reflect 2 x - y)) + 2 * |x 1| * |f y|))
      (volume.restrict (HalfSpace.upper 2)) :=
    ((((hF.comp_sub_left x).add (hF.comp_sub_left (HalfSpace.reflect 2 x))).const_mul B).restrict
      |>.add (hf.abs.const_mul (2 * |x 1|))).const_mul (1 / (2 * Real.pi))
  have hGm : AEStronglyMeasurable (fun y : ℝ^2 ↦ halfSpaceGreenFunction y x)
      (volume.restrict (HalfSpace.upper 2)) := by
    simp only [halfSpaceGreenFunction_two_eq]
    refine (Measurable.aestronglyMeasurable ?_)
    have hr : Measurable (HalfSpace.reflect 2) :=
      (HalfSpace.reflectLinearIsometryEquiv 2).continuous.measurable
    fun_prop
  refine hdom.mono' (hGm.mul hfm) ?_
  filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
  have hG := abs_halfSpaceGreenFunction_two_le y x
  have hfy := hB y hy
  have hF0 : ∀ z, 0 ≤ F z := fun z ↦ by
    simp only [F]; split_ifs <;> simp
  rw [Real.norm_eq_abs, abs_mul]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hfy
  calc |halfSpaceGreenFunction y x| * |f y|
      ≤ 1 / (2 * Real.pi) * (F (x - y) + F (HalfSpace.reflect 2 x - y) + 2 * |x 1|) * |f y| :=
        mul_le_mul_of_nonneg_right hG (abs_nonneg _)
    _ = 1 / (2 * Real.pi) * ((F (x - y) + F (HalfSpace.reflect 2 x - y)) * |f y| +
          2 * |x 1| * |f y|) := by ring
    _ ≤ 1 / (2 * Real.pi) * (B * (F (x - y) + F (HalfSpace.reflect 2 x - y)) +
          2 * |x 1| * |f y|) := by
        have h1 : (F (x - y) + F (HalfSpace.reflect 2 x - y)) * |f y| ≤
            B * (F (x - y) + F (HalfSpace.reflect 2 x - y)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hfy (add_nonneg (hF0 _) (hF0 _))
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end GreenFunction
