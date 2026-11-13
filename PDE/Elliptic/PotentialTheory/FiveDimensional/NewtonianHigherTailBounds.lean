/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHigherKernelDecay
public import PDE.FDeriv.Calculus
public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianTail

/-!
# A common majorant for higher Newtonian derivatives

When the source vanishes on a ball, every kernel derivative on the smaller
half-radius ball has the same integrable majorant: the original Newtonian
pairing at the center, multiplied by an explicit constant. Thus absolute
convergence of one potential pairing also controls every separated derivative.

The constants serve to justify differentiation of the tail integral at any finite order.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

/-- A fixed majorant constant on the ball of radius `r / 2`. The radius
loss grows with the number of derivatives, while the source majorant stays
the original Newtonian kernel at the center. -/
def fiveDimensionalHigherTailConstant (k : ℕ) (r : ℝ) : ℝ :=
  64 * Real.pi ^ 2 * fiveDimensionalHigherKernelConstant k * (2 / r) ^ k

/-- The separated-tail constant is positive for every positive radius. -/
theorem fiveDimensionalHigherTailConstant_pos (k : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < fiveDimensionalHigherTailConstant k r := by
  unfold fiveDimensionalHigherTailConstant
  exact mul_pos (mul_pos (by positivity) (fiveDimensionalHigherKernelConstant_pos k))
    (pow_pos (div_pos (by norm_num) hr) k)

/-- Every mixed coordinate derivative has a common Newtonian majorant as
the evaluation point varies inside a separated half-radius ball. -/
theorem abs_iteratedPartialDeriv_fundamentalSolution_five_sub_le_of_near
    (indices : List (Fin 5)) {X Z Y : ℝ^5} {r : ℝ}
    (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    |iteratedPartialDeriv indices (fundamentalSolution 5) (Z - Y)| ≤
      fiveDimensionalHigherTailConstant indices.length r *
        |fundamentalSolution 5 (X - Y)| := by
  let k := indices.length
  let C := fiveDimensionalHigherKernelConstant k
  have hC : 0 < C := fiveDimensionalHigherKernelConstant_pos k
  have htriangle : ‖X - Y‖ ≤ ‖Z - X‖ + ‖Z - Y‖ := by
    simpa only [sub_add_sub_cancel, norm_sub_rev X Z] using
      norm_add_le (X - Z) (Z - Y)
  have hsep : r / 2 ≤ ‖Z - Y‖ := by linarith
  have hpos : 0 < ‖Z - Y‖ := (half_pos hr).trans_le hsep
  have hratio : 1 / ‖Z - Y‖ ≤ 2 / r := by
    apply (div_le_div_iff₀ hpos hr).2
    linarith
  have hgamma :
      |fundamentalSolution 5 (Z - Y)| =
        (1 / (8 * Real.pi ^ 2)) / ‖Z - Y‖ ^ 3 := by
    rw [fundamentalSolution_five, Real.rpow_neg (norm_nonneg (Z - Y))]
    rw [abs_of_nonneg (by positivity)]
    simp only [div_eq_mul_inv, Real.rpow_ofNat]
  calc
    _ ≤ C / ‖Z - Y‖ ^ (k + 3) :=
      abs_iteratedPartialDeriv_fundamentalSolution_five_le
        indices (Z - Y) (norm_ne_zero_iff.mp hpos.ne')
    _ = (8 * Real.pi ^ 2 * C * (1 / ‖Z - Y‖) ^ k) *
        |fundamentalSolution 5 (Z - Y)| := by
      rw [hgamma]
      simp only [div_pow, one_pow, pow_add]
      field_simp
    _ ≤ (8 * Real.pi ^ 2 * C * (2 / r) ^ k) *
        |fundamentalSolution 5 (Z - Y)| := by
      gcongr
    _ ≤ (8 * Real.pi ^ 2 * C * (2 / r) ^ k) *
        (8 * |fundamentalSolution 5 (X - Y)|) :=
      mul_le_mul_of_nonneg_left
        (abs_fundamentalSolution_five_sub_le_of_near hr hZ hY) (by positivity)
    _ = _ := by
      dsimp only [fiveDimensionalHigherTailConstant, C, k]
      ring

/-- The total coordinate derivative is measurable even at its assigned value
at the pole. Away from the pole it agrees with the smooth kernel derivative. -/
theorem measurable_iteratedPartialDeriv_fiveDimensionalGamma
    (indices : List (Fin 5)) :
    Measurable (iteratedPartialDeriv indices (fundamentalSolution 5)) := by
  cases indices with
  | nil =>
      simp only [iteratedPartialDeriv, fundamentalSolution_five]
      fun_prop
  | cons i rest =>
      exact measurable_fderiv_apply_const ℝ
        (iteratedPartialDeriv rest (fundamentalSolution 5))
        (EuclideanSpace.single i (1 : ℝ))

/-- One absolutely convergent Newtonian pairing controls the integral of
every mixed derivative on the separated tail. Neither derivative
integrability nor source decay is assumed. -/
theorem integrable_and_norm_integral_iteratedPartialDeriv_fundamentalSolution_five_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (indices : List (Fin 5)) (X Z : ℝ^5)
    (r : ℝ) (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦
      iteratedPartialDeriv indices (fundamentalSolution 5) (Z - Y) * g Y) ∧
      ‖∫ Y : ℝ^5,
        iteratedPartialDeriv indices (fundamentalSolution 5) (Z - Y) * g Y‖ ≤
        fiveDimensionalHigherTailConstant indices.length r *
          ∫ Y : ℝ^5, ‖fundamentalSolution 5 (X - Y) * g Y‖ := by
  let F : ℝ^5 → ℝ := fun Y ↦
    iteratedPartialDeriv indices (fundamentalSolution 5) (Z - Y) * g Y
  let B : ℝ^5 → ℝ := fun Y ↦
    fiveDimensionalHigherTailConstant indices.length r *
      ‖fundamentalSolution 5 (X - Y) * g Y‖
  have hFmeas : Measurable F :=
    ((measurable_iteratedPartialDeriv_fiveDimensionalGamma indices).comp
      (measurable_const.sub measurable_id)).mul hg
  have hB : Integrable B := hInt.norm.const_mul _
  have hbound (Y : ℝ^5) : ‖F Y‖ ≤ B Y := by
    by_cases hY : g Y = 0
    · simp only [F, B, hY, mul_zero, norm_zero, le_refl]
    have haway : r ≤ ‖X - Y‖ := by
      by_contra h
      apply hY
      apply hzero Y
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev Y X] using lt_of_not_ge h
    have hk := abs_iteratedPartialDeriv_fundamentalSolution_five_sub_le_of_near
      indices hr hZ haway
    calc
      ‖F Y‖ =
          |iteratedPartialDeriv indices (fundamentalSolution 5) (Z - Y)| * |g Y| := by
            simp only [F, norm_mul, Real.norm_eq_abs]
      _ ≤ (fiveDimensionalHigherTailConstant indices.length r *
          |fundamentalSolution 5 (X - Y)|) * |g Y| :=
        mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      _ = B Y := by simp only [B, norm_mul, Real.norm_eq_abs, mul_assoc]
  have hF : Integrable F :=
    hB.mono' hFmeas.aestronglyMeasurable (Eventually.of_forall hbound)
  refine ⟨hF, ?_⟩
  calc
    ‖∫ Y : ℝ^5, F Y‖ ≤ ∫ Y : ℝ^5, ‖F Y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ Y : ℝ^5, B Y := integral_mono hF.norm hB hbound
    _ = _ := integral_const_mul _ _

/-- The Fréchet derivative of a mixed kernel row has a fixed integrable
majorant too. Summing its five coordinate entries suffices for dominated
differentiation; no sharp matrix norm is needed here. -/
theorem norm_fderiv_iteratedPartialDeriv_fundamentalSolution_five_sub_le_of_near
    (indices : List (Fin 5)) {X Z Y : ℝ^5} {r : ℝ}
    (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    ‖fderiv ℝ (iteratedPartialDeriv indices (fundamentalSolution 5)) (Z - Y)‖ ≤
      (5 * fiveDimensionalHigherTailConstant (indices.length + 1) r) *
        |fundamentalSolution 5 (X - Y)| := by
  have hrow :
      ‖fderiv ℝ (iteratedPartialDeriv indices (fundamentalSolution 5)) (Z - Y)‖ ≤
        ∑ i : Fin 5,
          |iteratedPartialDeriv (i :: indices) (fundamentalSolution 5) (Z - Y)| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    intro v
    rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
    calc
      _ ≤ ∑ i : Fin 5,
          ‖(∂[i] (iteratedPartialDeriv indices (fundamentalSolution 5)))
            (Z - Y) * v i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 5,
          |iteratedPartialDeriv (i :: indices) (fundamentalSolution 5) (Z - Y)| * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [norm_mul, Real.norm_eq_abs, iteratedPartialDeriv]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ ∑ i : Fin 5,
        |iteratedPartialDeriv (i :: indices) (fundamentalSolution 5) (Z - Y)| := hrow
    _ ≤ ∑ _i : Fin 5,
        fiveDimensionalHigherTailConstant (indices.length + 1) r *
          |fundamentalSolution 5 (X - Y)| :=
      Finset.sum_le_sum fun i _ ↦
        abs_iteratedPartialDeriv_fundamentalSolution_five_sub_le_of_near
          (i :: indices) hr hZ hY
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end PotentialTheory
