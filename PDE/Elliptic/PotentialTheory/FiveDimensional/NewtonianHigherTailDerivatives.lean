/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHigherTailBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating the separated Newtonian tail

The source may be merely measurable. Once it vanishes near the evaluation
point, all derivatives fall on the smooth kernel, and one absolutely
convergent Newtonian pairing dominates every finite derivative.

The conclusion identifies derivatives of the potential integral.
This matters when splitting a source into annuli: a bound for an auxiliary
kernel integral alone would not identify the derivatives being estimated.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

/-- Every mixed kernel row is smooth away from the pole. The finite order
is arbitrary, since only the kernel is being differentiated here. -/
theorem contDiffAt_iteratedPartialDeriv_fiveDimensionalGamma
    (indices : List (Fin 5)) (m : ℕ) (X : ℝ^5) (hX : X ≠ 0) :
    ContDiffAt ℝ m (iteratedPartialDeriv indices (fundamentalSolution 5)) X := by
  induction indices generalizing m with
  | nil =>
      exact (contDiffAt_fundamentalSolution 5 X hX).of_le
        (WithTop.coe_le_coe.mpr le_top)
  | cons i rest ih =>
      exact PDE.contDiffAt_partialDeriv m (ih (m + 1)) i

/-- A mixed kernel integral can be differentiated once more on a separated
tail. Both the derivative integral and the differentiation theorem follow
from the same original Newtonian majorant. -/
theorem hasFDerivAt_integral_iteratedPartialDeriv_fundamentalSolution_five_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (indices : List (Fin 5))
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      g Y • fderiv ℝ (iteratedPartialDeriv indices (fundamentalSolution 5)) (X - Y)) ∧
      HasFDerivAt
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5,
          iteratedPartialDeriv indices (fundamentalSolution 5) (Z - Y) * g Y)
        (∫ Y : ℝ^5,
          g Y • fderiv ℝ (iteratedPartialDeriv indices (fundamentalSolution 5)) (X - Y))
        X := by
  let K := iteratedPartialDeriv indices (fundamentalSolution 5)
  let F (Z Y : ℝ^5) : ℝ := K (Z - Y) * g Y
  let D (Z Y : ℝ^5) : ℝ^5 →L[ℝ] ℝ := g Y • fderiv ℝ K (Z - Y)
  let C := 5 * fiveDimensionalHigherTailConstant (indices.length + 1) r
  let bound (Y : ℝ^5) : ℝ := C * ‖fundamentalSolution 5 (X - Y) * g Y‖
  have hFmeas (Z : ℝ^5) : Measurable (F Z) :=
    ((measurable_iteratedPartialDeriv_fiveDimensionalGamma indices).comp
      (measurable_const.sub measurable_id)).mul hg
  have hDmeas (Z : ℝ^5) : Measurable (D Z) :=
    hg.smul ((measurable_fderiv ℝ K).comp (measurable_const.sub measurable_id))
  have hbound : Integrable bound := hInt.norm.const_mul _
  have haway (Y : ℝ^5) (hY : g Y ≠ 0) : r ≤ ‖X - Y‖ :=
    not_lt.1 fun h ↦ hY (hzero Y (by rwa [Metric.mem_ball, dist_comm, dist_eq_norm]))
  have hnear (Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) : ‖Z - X‖ ≤ r / 2 :=
    (mem_ball_iff_norm.1 hZ).le
  have hD_bound (Y Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) :
      ‖D Z Y‖ ≤ bound Y := by
    by_cases hY : g Y = 0
    · simp only [D, bound, hY, zero_smul, norm_zero, mul_zero, le_refl]
    have hk := norm_fderiv_iteratedPartialDeriv_fundamentalSolution_five_sub_le_of_near
      indices hr (hnear Z hZ) (haway Y hY)
    calc ‖D Z Y‖ = ‖g Y‖ * ‖fderiv ℝ K (Z - Y)‖ := norm_smul _ _
      _ ≤ ‖g Y‖ * (C * |fundamentalSolution 5 (X - Y)|) := by gcongr
      _ = bound Y := by simp only [bound, norm_mul, Real.norm_eq_abs]; ring
  have hdiff (Y Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) :
      HasFDerivAt (fun W : ℝ^5 ↦ F W Y) (D Z Y) Z := by
    by_cases hY : g Y = 0
    · simpa only [F, D, hY, mul_zero, zero_smul] using
        (hasFDerivAt_const (c := (0 : ℝ)) Z)
    have hZY : Z - Y ≠ 0 := fun h ↦
      hY (hzero Y (sub_eq_zero.mp h ▸ Metric.ball_subset_ball (by linarith) hZ))
    have hK : DifferentiableAt ℝ K (Z - Y) :=
      (contDiffAt_iteratedPartialDeriv_fiveDimensionalGamma indices 1 (Z - Y) hZY
        ).differentiableAt one_ne_zero
    have hchain : HasFDerivAt (fun W : ℝ^5 ↦ K (W - Y)) (fderiv ℝ K (Z - Y)) Z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
        hK.hasFDerivAt.comp Z ((hasFDerivAt_id Z).sub_const Y)
    exact hchain.mul_const (g Y)
  refine ⟨hbound.mono' (hDmeas X).aestronglyMeasurable
    (Eventually.of_forall fun Y ↦
      hD_bound Y X (Metric.mem_ball_self (half_pos hr))), ?_⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds X (half_pos hr))
    (Eventually.of_forall fun Z ↦ (hFmeas Z).aestronglyMeasurable)
    (integrable_and_norm_integral_iteratedPartialDeriv_fundamentalSolution_five_of_zero_on_ball
      g hg indices X X r hr
      (by simpa only [sub_self, norm_zero] using (half_pos hr).le) hzero hInt).1
    (hDmeas X).aestronglyMeasurable
    (Eventually.of_forall hD_bound) hbound (Eventually.of_forall hdiff)

/-- Every mixed coordinate derivative of the separated potential is
the absolutely convergent integral of the corresponding kernel derivative.
No derivative integrability of the source is required. -/
theorem iteratedPartialDeriv_fundamentalSolution_five_integral_eq_integral_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (indices : List (Fin 5))
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y) * g Y) ∧
      iteratedPartialDeriv indices
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y) X =
        ∫ Y : ℝ^5, iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y) * g Y := by
  induction indices generalizing X r with
  | nil => exact ⟨hInt, rfl⟩
  | cons i rest ih =>
      obtain ⟨hD, hdiff⟩ :=
        hasFDerivAt_integral_iteratedPartialDeriv_fundamentalSolution_five_of_zero_on_ball
          g hg rest X r hr hzero hInt
      have hactual : HasFDerivAt
          (iteratedPartialDeriv rest
            (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y))
          (∫ Y : ℝ^5,
            g Y • fderiv ℝ (iteratedPartialDeriv rest (fundamentalSolution 5)) (X - Y))
          X := by
        apply hdiff.congr_of_eventuallyEq
        filter_upwards [Metric.ball_mem_nhds X (half_pos hr)] with Z hZ
        obtain ⟨hIntZ, -⟩ :=
          integrable_and_norm_integral_iteratedPartialDeriv_fundamentalSolution_five_of_zero_on_ball
            g hg [] X Z r hr (mem_ball_iff_norm.1 hZ).le hzero hInt
        exact (ih Z (r / 2) (half_pos hr) (fun Y hY ↦ hzero Y (Metric.ball_subset_ball'
          (by linarith [Metric.mem_ball.mp hZ]) hY)) hIntZ).2
      refine ⟨
        (integrable_and_norm_integral_iteratedPartialDeriv_fundamentalSolution_five_of_zero_on_ball
        g hg (i :: rest) X X r hr
        (by simpa only [sub_self, norm_zero] using (half_pos hr).le) hzero hInt).1, ?_⟩
      change (fderiv ℝ
        (iteratedPartialDeriv rest
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y)) X)
            (EuclideanSpace.single i (1 : ℝ)) = _
      rw [hactual.fderiv, ContinuousLinearMap.integral_apply hD]
      exact integral_congr_ae (.of_forall fun Y ↦ mul_comm (g Y) _)

end PotentialTheory
