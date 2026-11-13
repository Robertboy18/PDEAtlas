/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.SpatialDifferentiation
import PDE.Parabolic.Heat.ConvolutionSpace.Equation
import PDE.Parabolic.Heat.ConvolutionTime
import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Heat-time derivatives controlled by the datum

The heat-time derivative is the heat evolution of the datum’s Laplacian. Bounds on
the pure second derivatives give a Lipschitz estimate that extends through heat age
zero by continuity. The constant negative-time branch is handled by the 1-Lipschitz map
`r ↦ max r 0`.
-/

@[expose] public section

open PDE (laplacian)

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- The positive heat-time derivative is the sum of the heat evolutions of the pure second
coordinate derivatives of the datum. -/
theorem hasDerivAt_initialValueSolution_time_sourceSecond
    (g : ℝ^n → ℝ)
    (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x : ℝ^n) (r : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun q ↦ initialValueSolution (n := n) g x q)
      (∑ i : Fin n,
        initialValueSolution (n := n)
          (fun y ↦
            (∂[i]
              (fun z ↦ (∂[i] g) z)) y)
          x r)
      r := by
  have hg_cont : Continuous g := hg2.continuous
  obtain ⟨M, hM⟩ := hg_cont.bounded_above_of_compact_support hgc
  have hg_bdd : ∃ M : ℝ, ∀ y, |g y| ≤ M := by
    refine ⟨M, fun y ↦ ?_⟩
    simpa [Real.norm_eq_abs] using hM y
  have hdiff :
      DifferentiableAt ℝ
        (fun q ↦ initialValueSolution (n := n) g x q) r :=
    (hasDerivAt_initialValueSolution_time
      (n := n) g x r hr hg_cont hg_bdd).differentiableAt
  apply hdiff.hasDerivAt.congr_deriv
  rw [deriv_initialValueSolution_time_eq_laplacian
    (n := n) g x r hr hg_cont hg_bdd]
  unfold laplacian
  exact Finset.sum_congr rfl fun i _hi ↦
    secondPartial_initialValueSolution_eq_convolution_source
      (n := n) g hg2 hgc x r hr i i

/-- Bounds on the pure second derivatives of the datum bound the positive heat-time derivative
by their sum. This is the heat equation combined with the heat kernel's supremum norm bound. -/
theorem norm_deriv_initialValueSolution_time_le
    (g : ℝ^n → ℝ) (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (C : Fin n → ℝ)
    (hC : ∀ (i : Fin n) (y : ℝ^n),
      |(∂[i] (fun z ↦ (∂[i] g) z)) y| ≤ C i)
    (x : ℝ^n) (r : ℝ) (hr : 0 < r) :
    ‖deriv (fun q ↦ initialValueSolution g x q) r‖ ≤ ∑ i : Fin n, C i := by
  rw [(hasDerivAt_initialValueSolution_time_sourceSecond g hg2 hgc x r hr).deriv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  have hsecond_cont : Continuous (fun y ↦ (∂[i] (fun z ↦ (∂[i] g) z)) y) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0)
      (PDE.contDiff_partialDeriv_of_succ (m := 1) hg2)).continuous
  simpa only [Real.norm_eq_abs] using
    abs_initialValueSolution_le _ hsecond_cont (hC i) x r

/-- If all pure second derivatives of a compactly supported `C²` datum are bounded, its heat
evolution, extended by the datum at negative times, is globally Lipschitz in heat time. The
positive-time estimate follows from the heat equation. Continuity extends it through time zero,
and composition with `r ↦ max r 0` extends the bound to the constant negative-time branch. -/
theorem lipschitzWith_initialValueSolution_time_of_second_bound
    (g : ℝ^n → ℝ)
    (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (C : Fin n → ℝ)
    (hC : ∀ (i : Fin n) (y : ℝ^n),
      |(∂[i]
        (fun z ↦ (∂[i] g) z)) y| ≤ C i)
    (x : ℝ^n) :
    LipschitzWith (Real.nnabs (∑ i : Fin n, C i))
      (fun r ↦ initialValueSolution (n := n) g x r) := by
  let P : ℝ → ℝ := fun r ↦ initialValueSolution (n := n) g x r
  let B : ℝ := ∑ i : Fin n, C i
  have hCi (i : Fin n) : 0 ≤ C i :=
    (abs_nonneg
      ((∂[i]
        (fun z ↦ (∂[i] g) z)) 0)).trans (hC i 0)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _hi ↦ hCi i
  have hpos :
      LipschitzOnWith (Real.nnabs B) P (Set.Ioi (0 : ℝ)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    · intro r hr
      exact
        (hasDerivAt_initialValueSolution_time_sourceSecond
          (n := n) g hg2 hgc x r hr).differentiableAt
    · intro r hr
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hB]
      exact norm_deriv_initialValueSolution_time_le g hg2 hgc C hC x r hr
    · exact convex_Ioi (𝕜 := ℝ) (0 : ℝ)
  obtain ⟨M, hM⟩ := hg2.continuous.bounded_above_of_compact_support hgc
  have hcont : Continuous P :=
    (continuous_initialValueSolution_family (T := Unit)
      (g := fun p : Unit × ℝ^n ↦ g p.2)
      (hg2.continuous.comp continuous_snd) (fun p ↦ hM p.2)).comp
        ((continuous_const (y := ())).prodMk (continuous_const.prodMk continuous_id))
  have hnonneg : LipschitzOnWith (Real.nnabs B) P (Set.Ici (0 : ℝ)) := by
    simpa only [closure_Ioi] using hpos.closure hcont.continuousOn
  have hclamp : LipschitzWith 1 (fun r : ℝ ↦ max r 0) := LipschitzWith.id.max_const 0
  have hPclamp (r : ℝ) : P (max r 0) = P r := by
    by_cases hr : 0 ≤ r
    · rw [max_eq_left hr]
    · have hr0 : r ≤ 0 := le_of_not_ge hr
      simp [P, initialValueSolution_of_t_le_zero, hr0]
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist (P a) (P b) ≤ (Real.nnabs B : ℝ) * dist a b
  rw [← hPclamp a, ← hPclamp b]
  refine (hnonneg.dist_le_mul (max a 0) (le_max_right _ _)
    (max b 0) (le_max_right _ _)).trans ?_
  exact mul_le_mul_of_nonneg_left (by simpa using hclamp.dist_le_mul a b) NNReal.zero_le_coe

end HeatEquation
