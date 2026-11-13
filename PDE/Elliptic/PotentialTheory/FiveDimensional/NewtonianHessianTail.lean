/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianNoncompactGradient
import PDE.FDeriv.Calculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import CAS.ExactTactic

/-!
# Newtonian Hessian tails

Outside a fixed ball around the evaluation point, the Hessian kernel
is controlled by the Newtonian kernel at that point. The comparison is uniform
as the evaluation point moves by half the ball radius. Absolute convergence
of one Newtonian pairing therefore gives an integrable Hessian tail, without
compact support or a separate Hessian integrability assumption.

Differentiating the first-gradient integral then gives the classical Hessian
of the tail potential. Its absolute integrability is derived from the
same Newtonian pairing, with no source regularity assumption.

These estimates concern the separated tail; the principal value and the local diagonal
correction at the pole are in `NewtonianHessianNear` and `PrincipalValueHessian`.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter
open scoped Topology


namespace PotentialTheory

/-- The classical Hessian inherits the regularized kernel's uniform bound.
The constant is independent of the two coordinate indices. -/
theorem abs_fundamentalSolution_five_hessian_le
    (i j : Fin 5) (X : ℝ^5) (hX : X ≠ 0) :
    |iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X| ≤
      (18 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-5 : ℝ) := by
  apply le_of_tendsto
    (fiveDimensionalGammaRegularized_hessian_tendsto j i X hX).abs
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact fiveDimensionalGammaRegularized_hessian_bound ε hε.ne' j i X hX

/-- Every Hessian entry has a common Newtonian majorant on a ball that stays
away from the source. The non-sharp constant is useful for differentiation
under the tail integral, since the majorant does not move with `Z`. -/
theorem abs_fundamentalSolution_five_hessian_sub_le_of_near
    (i j : Fin 5) {X Z Y : ℝ^5} {r : ℝ}
    (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    |iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (Z - Y)| ≤
      (576 / r ^ 2) * |fundamentalSolution 5 (X - Y)| := by
  have htriangle : ‖X - Y‖ ≤ ‖Z - X‖ + ‖Z - Y‖ := by
    simpa only [sub_add_sub_cancel, norm_sub_rev X Z] using
      norm_add_le (X - Z) (Z - Y)
  have hsep : r / 2 ≤ ‖Z - Y‖ := by linarith
  have hpos : 0 < ‖Z - Y‖ := (half_pos hr).trans_le hsep
  have hsq : (r / 2) ^ 2 ≤ ‖Z - Y‖ ^ 2 := by gcongr
  have hratio : (18 : ℝ) / ‖Z - Y‖ ^ 2 ≤ 72 / r ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hpos) (sq_pos_of_pos hr)).2
    nlinarith
  have hpow : ‖Z - Y‖ ^ (-5 : ℝ) = ‖Z - Y‖ ^ (-3 : ℝ) / ‖Z - Y‖ ^ 2 := by
    simpa only [show (-3 : ℝ) - 2 = -5 by norm_num, Real.rpow_two] using
      Real.rpow_sub hpos (-3) 2
  have hgamma : 0 ≤ fundamentalSolution 5 (Z - Y) := by
    rw [fundamentalSolution_five]
    positivity
  calc
    _ ≤ (18 / (8 * Real.pi ^ 2)) * ‖Z - Y‖ ^ (-5 : ℝ) :=
      abs_fundamentalSolution_five_hessian_le i j (Z - Y) (norm_ne_zero_iff.mp hpos.ne')
    _ = (18 / ‖Z - Y‖ ^ 2) * |fundamentalSolution 5 (Z - Y)| := by
      rw [abs_of_nonneg hgamma, fundamentalSolution_five, hpow]
      cas
    _ ≤ (72 / r ^ 2) * |fundamentalSolution 5 (Z - Y)| :=
      mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    _ ≤ (72 / r ^ 2) * (8 * |fundamentalSolution 5 (X - Y)|) :=
      mul_le_mul_of_nonneg_left
        (abs_fundamentalSolution_five_sub_le_of_near hr hZ hY) (by positivity)
    _ = (576 / r ^ 2) * |fundamentalSolution 5 (X - Y)| := by cas

/-- A measurable source that vanishes near the anchor has an absolutely
convergent Hessian tail at every point in the smaller ball. Its integral is
bounded using only the original Newtonian pairing at the anchor. -/
theorem integrable_and_norm_integral_fundamentalSolution_five_hessian_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (i j : Fin 5) (X Z : ℝ^5)
    (r : ℝ) (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (Z - Y) * g Y) ∧
      ‖∫ Y : ℝ^5,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (Z - Y) * g Y‖ ≤
        (576 / r ^ 2) * ∫ Y : ℝ^5, ‖fundamentalSolution 5 (X - Y) * g Y‖ := by
  let F : ℝ^5 → ℝ := fun Y ↦
    iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (Z - Y) * g Y
  let B : ℝ^5 → ℝ := fun Y ↦
    (576 / r ^ 2) * ‖fundamentalSolution 5 (X - Y) * g Y‖
  have hFmeas : Measurable F :=
    ((measurable_fundamentalSolution_five_hessian i j).comp
      (measurable_const.sub measurable_id)).mul hg
  have hB : Integrable B := hInt.norm.const_mul _
  have hbound (Y : ℝ^5) : ‖F Y‖ ≤ B Y := by
    by_cases hY : g Y = 0
    · simp only [F, B, hY, mul_zero, norm_zero, le_refl]
    have haway : r ≤ ‖X - Y‖ := by
      by_contra h
      refine hY (hzero Y ?_)
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev Y X] using lt_of_not_ge h
    have hk := abs_fundamentalSolution_five_hessian_sub_le_of_near i j hr hZ haway
    simp only [F, B, norm_mul, Real.norm_eq_abs, ← mul_assoc]
    gcongr
  have hF : Integrable F := hB.mono' hFmeas.aestronglyMeasurable (.of_forall hbound)
  refine ⟨hF, (norm_integral_le_integral_norm _).trans ?_⟩
  exact (integral_mono hF.norm hB hbound).trans_eq (integral_const_mul _ _)

/-- A row of the Newtonian Hessian has a fixed integrable tail majorant.
Summing the five entry bounds is enough for Fréchet differentiation under the
integral; no estimate at the pole is used. -/
theorem norm_fderiv_partialDeriv_fundamentalSolution_five_sub_le_of_near
    (j : Fin 5) {X Z Y : ℝ^5} {r : ℝ}
    (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    ‖fderiv ℝ (∂[j] (fundamentalSolution 5)) (Z - Y)‖ ≤
      (2880 / r ^ 2) * |fundamentalSolution 5 (X - Y)| := by
  have hrow :
      ‖fderiv ℝ (∂[j] (fundamentalSolution 5)) (Z - Y)‖ ≤
        ∑ i : Fin 5, |iteratedPartialDeriv [i, j] (fundamentalSolution 5) (Z - Y)| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    intro v
    rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
    calc
      _ ≤ ∑ i : Fin 5,
          ‖(∂[i] (∂[j] (fundamentalSolution 5))) (Z - Y) * v i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 5,
          |iteratedPartialDeriv [i, j] (fundamentalSolution 5) (Z - Y)| * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i _hi
        simp only [norm_mul, Real.norm_eq_abs, iteratedPartialDeriv]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ ∑ i : Fin 5, |iteratedPartialDeriv [i, j] (fundamentalSolution 5) (Z - Y)| := hrow
    _ ≤ ∑ _i : Fin 5, (576 / r ^ 2) * |fundamentalSolution 5 (X - Y)| :=
      Finset.sum_le_sum fun i _hi ↦
        abs_fundamentalSolution_five_hessian_sub_le_of_near i j hr hZ hY
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- On a separated tail, the first-gradient formula can use the
coordinate derivative of the fundamental solution. The assigned derivative
at the pole disappears because the source vanishes there. -/
private theorem integral_partialDeriv_fundamentalSolution_five_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (j : Fin 5)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦ (∂[j] (fundamentalSolution 5)) (X - Y) * g Y) ∧
      (∂[j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y)) X =
        ∫ Y : ℝ^5, (∂[j] (fundamentalSolution 5)) (X - Y) * g Y := by
  obtain ⟨hD, hgrad⟩ :=
    hasFDerivAt_fundamentalSolution_five_integral_of_zero_on_ball g hg X r hr hzero hInt
  have heq (Y : ℝ^5) :
      (g Y • fiveDimensionalGammaFDerivKernel (X - Y)) (EuclideanSpace.single j (1 : ℝ)) =
        (∂[j] (fundamentalSolution 5)) (X - Y) * g Y := by
    by_cases hY : g Y = 0
    · simp only [hY, zero_smul, zero_apply, mul_zero]
    have hXY : X - Y ≠ 0 := by
      intro h
      apply hY
      apply hzero Y
      rw [← sub_eq_zero.mp h]
      exact Metric.mem_ball_self hr
    unfold partialDeriv
    rw [(hasFDerivAt_fiveDimensionalGamma (X - Y) hXY).fderiv]
    simp only [smul_apply, smul_eq_mul, mul_comm]
  have hcoord : Integrable (fun Y : ℝ^5 ↦
      (g Y • fiveDimensionalGammaFDerivKernel (X - Y))
        (EuclideanSpace.single j (1 : ℝ))) := by
    simpa only [ContinuousLinearMap.apply_apply] using!
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).integrable_comp hD
  refine ⟨hcoord.congr (Filter.Eventually.of_forall heq), ?_⟩
  change (fderiv ℝ
    (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y) X)
      (EuclideanSpace.single j (1 : ℝ)) = _
  rw [hgrad.fderiv, ContinuousLinearMap.integral_apply hD]
  exact integral_congr_ae (Filter.Eventually.of_forall heq)

/-- Differentiating a separated first-gradient integral gives the
Hessian row. Its integrability follows from the Newtonian pairing at the
anchor and the uniform row bound, rather than being an extra hypothesis. -/
theorem hasFDerivAt_integral_partialDeriv_fundamentalSolution_five_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (j : Fin 5)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      g Y • fderiv ℝ (∂[j] (fundamentalSolution 5)) (X - Y)) ∧
      HasFDerivAt
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5,
          (∂[j] (fundamentalSolution 5)) (Z - Y) * g Y)
        (∫ Y : ℝ^5, g Y • fderiv ℝ (∂[j] (fundamentalSolution 5)) (X - Y)) X := by
  let F (Z Y : ℝ^5) : ℝ := (∂[j] (fundamentalSolution 5)) (Z - Y) * g Y
  let D (Z Y : ℝ^5) : ℝ^5 →L[ℝ] ℝ :=
    g Y • fderiv ℝ (∂[j] (fundamentalSolution 5)) (Z - Y)
  let bound (Y : ℝ^5) : ℝ :=
    (2880 / r ^ 2) * ‖fundamentalSolution 5 (X - Y) * g Y‖
  have hFmeas (Z : ℝ^5) : Measurable (F Z) :=
    ((measurable_fderiv_apply_const ℝ (fundamentalSolution 5)
      (EuclideanSpace.single j (1 : ℝ))).comp (measurable_const.sub measurable_id)).mul hg
  have hDmeas (Z : ℝ^5) : Measurable (D Z) :=
    hg.smul ((measurable_fderiv ℝ (∂[j] (fundamentalSolution 5))).comp
      (measurable_const.sub measurable_id))
  have hbound : Integrable bound := hInt.norm.const_mul _
  have haway (Y : ℝ^5) (hY : g Y ≠ 0) : r ≤ ‖X - Y‖ := by
    by_contra h
    refine hY (hzero Y ?_)
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev Y X] using lt_of_not_ge h
  have hD_bound (Y Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) : ‖D Z Y‖ ≤ bound Y := by
    by_cases hY : g Y = 0
    · simp only [D, bound, hY, zero_smul, norm_zero, mul_zero, le_refl]
    have hk := norm_fderiv_partialDeriv_fundamentalSolution_five_sub_le_of_near j hr
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hZ.le) (haway Y hY)
    simp only [D, bound, norm_smul, norm_mul, Real.norm_eq_abs]
    calc _ ≤ |g Y| * (2880 / r ^ 2 * |fundamentalSolution 5 (X - Y)|) := by gcongr
      _ = _ := by ring
  have hdiff (Y Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) :
      HasFDerivAt (fun W : ℝ^5 ↦ F W Y) (D Z Y) Z := by
    by_cases hY : g Y = 0
    · simpa only [F, D, hY, mul_zero, zero_smul] using
        (hasFDerivAt_const (c := (0 : ℝ)) Z)
    have hZY : Z - Y ≠ 0 := fun h ↦ hY (hzero Y (by
      rw [← sub_eq_zero.mp h]
      exact Metric.ball_subset_ball (by linarith) hZ))
    have hΓj : DifferentiableAt ℝ (∂[j] (fundamentalSolution 5)) (Z - Y) :=
      (PDE.contDiffAt_partialDeriv 1 ((contDiffAt_fundamentalSolution 5 (Z - Y) hZY).of_le
        (WithTop.coe_le_coe.mpr le_top)) j).differentiableAt one_ne_zero
    have hchain : HasFDerivAt
        (fun W : ℝ^5 ↦ (∂[j] (fundamentalSolution 5)) (W - Y))
        (fderiv ℝ (∂[j] (fundamentalSolution 5)) (Z - Y)) Z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
        hΓj.hasFDerivAt.comp Z ((hasFDerivAt_id Z).sub_const Y)
    exact hchain.mul_const (g Y)
  exact ⟨hbound.mono' (hDmeas X).aestronglyMeasurable
    (.of_forall fun Y ↦ hD_bound Y X (Metric.mem_ball_self (half_pos hr))),
    hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds X (half_pos hr))
      (.of_forall fun Z ↦ (hFmeas Z).aestronglyMeasurable)
      (integral_partialDeriv_fundamentalSolution_five_of_zero_on_ball g hg j X r hr hzero hInt).1
      (hDmeas X).aestronglyMeasurable (.of_forall hD_bound) hbound (.of_forall hdiff)⟩

/-- The original Newtonian majorant also controls the potential at nearby
points when the source vanishes on the excluded ball. Continuity of the
source is not needed for this separated-tail comparison. -/
private theorem integrable_fundamentalSolution_five_mul_of_zero_on_ball_of_near
    (g : ℝ^5 → ℝ) (hg : Measurable g) (X Z : ℝ^5)
    (r : ℝ) (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y) * g Y) := by
  have hΓ : Measurable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y)) := by
    simp_rw [fundamentalSolution_five]
    fun_prop
  apply (hInt.norm.const_mul 8).mono' (hΓ.mul hg).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro Y
  change ‖fundamentalSolution 5 (Z - Y) * g Y‖ ≤
    8 * ‖fundamentalSolution 5 (X - Y) * g Y‖
  by_cases hY : g Y = 0
  · simp only [hY, mul_zero, norm_zero, le_refl]
  have haway : r ≤ ‖X - Y‖ := by
    by_contra h
    apply hY
    apply hzero Y
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev Y X] using lt_of_not_ge h
  have hk := abs_fundamentalSolution_five_sub_le_of_near hr hZ haway
  calc
    ‖fundamentalSolution 5 (Z - Y) * g Y‖ =
        |fundamentalSolution 5 (Z - Y)| * |g Y| := by
      simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ (8 * |fundamentalSolution 5 (X - Y)|) * |g Y| :=
      mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    _ = 8 * ‖fundamentalSolution 5 (X - Y) * g Y‖ := by
      simp only [norm_mul, Real.norm_eq_abs, mul_assoc]

/-- The first coordinate derivative of a separated Newtonian tail is
Fréchet differentiable. The first-gradient identity holds on a neighborhood,
so dominated differentiation of its integral identifies the classical second
derivative, rather than only an auxiliary kernel expression. -/
theorem hasFDerivAt_partialDeriv_fundamentalSolution_five_integral_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (j : Fin 5)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      g Y • fderiv ℝ (∂[j] (fundamentalSolution 5)) (X - Y)) ∧
      HasFDerivAt
        (∂[j]
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y))
        (∫ Y : ℝ^5, g Y • fderiv ℝ (∂[j] (fundamentalSolution 5)) (X - Y)) X := by
  have hd := hasFDerivAt_integral_partialDeriv_fundamentalSolution_five_of_zero_on_ball
    g hg j X r hr hzero hInt
  refine ⟨hd.1, hd.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Metric.ball_mem_nhds X (half_pos hr)] with Z hZ
  have hnear : ‖Z - X‖ ≤ r / 2 :=
    (show ‖Z - X‖ < r / 2 by simpa only [Metric.mem_ball, dist_eq_norm] using hZ).le
  have hIntZ := integrable_fundamentalSolution_five_mul_of_zero_on_ball_of_near
    g hg X Z r hr hnear hzero hInt
  have hzeroZ : ∀ Y ∈ Metric.ball Z (r / 2), g Y = 0 := by
    intro Y hY
    apply hzero Y
    apply Metric.mem_ball.mpr
    have hYZ := Metric.mem_ball.mp hY
    have hZX := Metric.mem_ball.mp hZ
    exact (dist_triangle Y Z X).trans_lt (by linarith)
  exact (integral_partialDeriv_fundamentalSolution_five_of_zero_on_ball
    g hg j Z (r / 2) (half_pos hr) hzeroZ hIntZ).2

/-- Every classical second coordinate derivative of a separated Newtonian
tail is the absolutely convergent integral of the Hessian entry.
No principal value or diagonal correction is needed because the source
vanishes on a neighborhood of the evaluation point. -/
theorem fundamentalSolution_five_integral_hessian_eq_integral_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (i j : Fin 5)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      iteratedPartialDeriv [i, j] (fundamentalSolution 5) (X - Y) * g Y) ∧
      iteratedPartialDeriv [i, j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y) X =
        ∫ Y : ℝ^5, iteratedPartialDeriv [i, j] (fundamentalSolution 5) (X - Y) * g Y := by
  obtain ⟨hD, hdiff⟩ :=
    hasFDerivAt_partialDeriv_fundamentalSolution_five_integral_of_zero_on_ball
      g hg j X r hr hzero hInt
  have hentry := integrable_and_norm_integral_fundamentalSolution_five_hessian_of_zero_on_ball
    g hg i j X X r hr (by simpa only [sub_self, norm_zero] using (half_pos hr).le) hzero hInt
  refine ⟨hentry.1, ?_⟩
  change (fderiv ℝ
    (∂[j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y)) X)
        (EuclideanSpace.single i (1 : ℝ)) = _
  rw [hdiff.fderiv, ContinuousLinearMap.integral_apply hD]
  apply integral_congr_ae
  filter_upwards [] with Y
  change g Y * (∂[i] (∂[j] (fundamentalSolution 5))) (X - Y) =
    (∂[i] (∂[j] (fundamentalSolution 5))) (X - Y) * g Y
  exact mul_comm _ _

end PotentialTheory
