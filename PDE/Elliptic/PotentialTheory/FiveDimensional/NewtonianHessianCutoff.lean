/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianNoncompactHessian
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Compact cutoffs converge to the Newtonian Hessian

For a C¹ source with an absolutely convergent Newtonian pairing at one anchor,
expanding smooth cutoffs recover the Hessian at every point. In the
centered formula, the near integral and diagonal correction eventually agree
exactly. The exterior integral converges by domination with the uncut source.
No global L² assumption is needed for this pointwise limit.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

/-- Expanding compact cutoffs recover the Hessian of a noncompact
C¹ source pointwise. The Newtonian pairing at one anchor supplies all decay
needed for the exterior integral; Hessian integrability is derived from
the centered formula. The cutoffs need only be C¹, bounded in norm by one,
and eventually equal to one on each bounded ball. -/
theorem tendsto_fundamentalSolution_five_integral_hessian_cutoff_mul
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (χ : ℕ → ℝ^5 → ℝ) (hχC1 : ∀ n, ContDiff ℝ 1 (χ n))
    (hχc : ∀ n, HasCompactSupport (χ n)) (hχbound : ∀ n Y, ‖χ n Y‖ ≤ 1)
    (hχ : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ Y : ℝ^5, ‖Y‖ ≤ R → χ n Y = 1)
    (i j : Fin 5) (X : ℝ^5) :
    Tendsto (fun n ↦ iteratedPartialDeriv [i, j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5,
        fundamentalSolution 5 (Z - Y) * (χ n Y * f Y)) X) atTop
      (𝓝 (iteratedPartialDeriv [i, j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X)) := by
  let F : ℕ → ℝ^5 → ℝ := fun n Y ↦ χ n Y * f Y
  let K : ℝ^5 → ℝ := iteratedPartialDeriv [i, j] (fundamentalSolution 5)
  let B : Set (ℝ^5) := Metric.ball 0 1
  have hF (n : ℕ) : ContDiff ℝ 1 (F n) := (hχC1 n).mul hf
  have hFInt (n : ℕ) : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * F n Y) :=
    ((hχc n).mul_right.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) (hF n).continuous A).integrable_swap
  have hactual := fundamentalSolution_five_integral_hessian_eq_centered_of_integrable_at_anchor
    f hf A X hInt i j 1 (by norm_num)
  have hcompact (n : ℕ) :=
    fundamentalSolution_five_integral_hessian_eq_centered_of_integrable_at_anchor
      (F n) (hF n) A X (hFInt n) i j 1 (by norm_num)
  have htail : Tendsto (fun n ↦ ∫ H in Bᶜ, K H * F n (X - H)) atTop
      (𝓝 (∫ H in Bᶜ, K H * f (X - H))) := by
    refine tendsto_integral_of_dominated_convergence (fun H ↦ ‖K H * f (X - H)‖)
      (fun n ↦ (hcompact n).2.1.aestronglyMeasurable) hactual.2.1.norm
      (fun n ↦ .of_forall fun H ↦ ?_) (.of_forall fun H ↦ ?_)
    · rw [show K H * F n (X - H) = χ n (X - H) * (K H * f (X - H)) by simp only [F]; ring,
        norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχbound n (X - H))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hχ ‖X - H‖] with n hn
      simp only [F, hn (X - H) le_rfl, one_mul]
  have hstabilize : ∀ᶠ n in atTop,
      iteratedPartialDeriv [i, j]
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * F n Y) X =
        (∫ H in B, K H * (f (X - H) - f X)) +
          (∫ H in Bᶜ, K H * F n (X - H)) - (if i = j then f X / 5 else 0) := by
    filter_upwards [hχ (‖X‖ + 1)] with n hn
    have hcenter : F n X = f X := by simp only [F, hn X (by linarith), one_mul]
    have hnear : ∀ H ∈ B, K H * (F n (X - H) - f X) = K H * (f (X - H) - f X) := by
      intro H hH
      have hH : ‖H‖ < 1 := by simpa [B] using hH
      simp only [F, hn (X - H) ((norm_sub_le X H).trans (by linarith)), one_mul]
    refine (hcompact n).2.2.trans ?_
    rw [hcenter, setIntegral_congr_fun measurableSet_ball hnear]
  rw [hactual.2.2]
  exact ((tendsto_const_nhds.add htail).sub tendsto_const_nhds).congr'
    (hstabilize.mono fun _ hn ↦ hn.symm)

/-- Expanding centered smooth bumps recover the Newtonian Hessian.
This is the bump specialization of the compact cutoff convergence theorem. -/
theorem tendsto_fundamentalSolution_five_integral_hessian_bump_mul
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (χ : ℕ → ContDiffBump (0 : ℝ^5))
    (hχ : Tendsto (fun n ↦ (χ n).rIn) atTop atTop)
    (i j : Fin 5) (X : ℝ^5) :
    Tendsto (fun n ↦ iteratedPartialDeriv [i, j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5,
        fundamentalSolution 5 (Z - Y) * (χ n Y * f Y)) X) atTop
      (𝓝 (iteratedPartialDeriv [i, j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X)) := by
  apply tendsto_fundamentalSolution_five_integral_hessian_cutoff_mul f hf A hInt
    (fun n ↦ χ n) (fun n ↦ (χ n).contDiff) (fun n ↦ (χ n).hasCompactSupport)
  · intro n Y
    rw [Real.norm_of_nonneg (χ n).nonneg]
    exact (χ n).le_one
  · intro R
    filter_upwards [hχ.eventually (eventually_ge_atTop R)] with n hn Y hY
    exact (χ n).one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hY.trans hn)

end PotentialTheory
