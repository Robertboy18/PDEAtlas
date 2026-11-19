/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MeanValue.ThreePointDeterminant
public import PDE.Analysis.Integration.BumpMoments.Interval
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Regularity

import CAS.ExactTactic

/-!
# Independent scalar moments for the clock weights

A uniform passage gap of at least `8 / 5` on `(205, 205.1)` makes the
evaluation determinant of the weights `(1, R, Q)` negative at
`205.02`, `205.05`, and `205.08`. Their local continuity then supplies
one family of three smooth nonnegative unit-mass bumps with disjoint
compact supports in `(205.01, 205.09)` and a nonsingular moment matrix.
Signed combinations of this fixed family realize every scalar moment vector.

The gap is a hypothesis. These are the moments of the integral
weights in `clockPassageData`.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators ContDiff Matrix

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open PDE.Analysis Gate.Weights

private theorem contDiffOn_clock_weights (base upTime terminalTime speedConstant : ℝ) :
    let D := clockPassageData base upTime terminalTime speedConstant; ContDiffOn ℝ 2 D.R
      (Ioo (205 : ℝ) (2051 / 10)) ∧ ContDiffOn ℝ 2 D.Q (Ioo (205 : ℝ) (2051 / 10)) := by
  have hreg := gateRegularity_clockPassageData base upTime terminalTime speedConstant
  have hg : ContDiffOn ℝ 2 (clockPassageData base upTime terminalTime speedConstant).g
      (Ioo (205 : ℝ) (2051 / 10)) :=
    MiddleClock.contDiff_g.contDiffOn.of_le (by simp)
  exact ⟨GateRegularity.contDiffOn_R (h := hreg) hg, GateRegularity.contDiffOn_Q (h := hreg) hg⟩

/-- Ordered columns of weight evaluations have negative determinant.
Only the passage gap is assumed; regularity and curvature come from the clock. -/
theorem clock_weight_evaluation_det_neg (base upTime terminalTime speedConstant : ℝ)
    (hgap : ∀ y ∈ Ioo (205 : ℝ) (2051 / 10), (8 / 5 : ℝ) ≤
      (clockPassageData base upTime terminalTime speedConstant).tMinus y -
        (clockPassageData base upTime terminalTime speedConstant).tPlus y) :
    let D := clockPassageData base upTime terminalTime speedConstant; Matrix.det
      !![1, 1, 1; D.R (20502 / 100), D.R (20505 / 100), D.R (20508 / 100); D.Q (20502 / 100),
      D.Q (20505 / 100), D.Q (20508 / 100)] < 0 := by
  obtain ⟨hR, hQ⟩ := contDiffOn_clock_weights base upTime terminalTime speedConstant
  refine three_point_det_neg_of_curvature_neg
    (x0 := 20502 / 100) (x1 := 20505 / 100) (x2 := 20508 / 100) hR hQ
    (fun y hy ↦ deriv_clock_weight_ratio_pos base upTime terminalTime speedConstant hy)
    ?_ (by cas) (by cas) (by cas) (by cas)
  exact fun y hy ↦ (clock_weight_relative_curvature_lt base upTime terminalTime speedConstant
    hy (hgap y hy)).trans (by cas)

/-- One family of nonnegative normalized bumps has independent moments
and realizes every signed target by changing only its three coefficients.
The supports lie strictly inside the gate. -/
theorem exists_clock_bumps_moment_matrix_det_ne_zero (base upTime terminalTime speedConstant : ℝ)
    (hgap : ∀ y ∈ Ioo (205 : ℝ) (2051 / 10), (8 / 5 : ℝ) ≤ (clockPassageData base upTime
      terminalTime speedConstant).tMinus y -
      (clockPassageData base upTime terminalTime speedConstant).tPlus y) :
    let D := clockPassageData base upTime terminalTime speedConstant
    let W : ℝ → Fin 3 → ℝ := fun y ↦ ![1, D.R y, D.Q y]
    ∃ β : Fin 3 → ℝ → ℝ,
      (∀ j, ContDiff ℝ ∞ (β j) ∧ HasCompactSupport (β j) ∧
        tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) ∧
        (∀ t, 0 ≤ β j t) ∧ (∫ t, β j t) = 1 ∧
        ∀ i, Integrable (fun t ↦ β j t * W t i)) ∧
      Pairwise (fun j k ↦ Disjoint (tsupport (β j)) (tsupport (β k))) ∧
      (bumpMomentMatrix W β).det ≠ 0 ∧
      Function.Surjective (fun c : Fin 3 → ℝ ↦ fun i : Fin 3 ↦
        ∫ t, (∑ j, c j * β j t) * W t i) := by
  let D := clockPassageData base upTime terminalTime speedConstant
  let W : ℝ → Fin 3 → ℝ := fun y ↦ ![1, D.R y, D.Q y]
  let x : Fin 3 → ℝ := ![20502 / 100, 20505 / 100, 20508 / 100]
  have hsubset : Icc (20501 / 100 : ℝ) (20509 / 100) ⊆ Ioo (205 : ℝ) (2051 / 10) :=
    fun y hy ↦ ⟨(by cas : (205 : ℝ) < 20501 / 100).trans_le hy.1,
      hy.2.trans_lt (by cas : (20509 / 100 : ℝ) < 2051 / 10)⟩
  obtain ⟨hR, hQ⟩ := contDiffOn_clock_weights base upTime terminalTime speedConstant
  have hW : ContinuousOn W (Icc (20501 / 100 : ℝ) (20509 / 100)) := by
    refine continuousOn_pi.2 fun i ↦ ?_
    fin_cases i
    · exact continuousOn_const
    · exact hR.continuousOn.mono hsubset
    · exact hQ.continuousOn.mono hsubset
  have hx : ∀ j, x j ∈ Ioo (20501 / 100 : ℝ) (20509 / 100) := by
    intro j
    fin_cases j
    · change (20501 / 100 : ℝ) < 20502 / 100 ∧ 20502 / 100 < 20509 / 100
      constructor <;> cas
    · change (20501 / 100 : ℝ) < 20505 / 100 ∧ 20505 / 100 < 20509 / 100
      constructor <;> cas
    · change (20501 / 100 : ℝ) < 20508 / 100 ∧ 20508 / 100 < 20509 / 100
      constructor <;> cas
  have hmatrix : (Matrix.of fun i j : Fin 3 ↦ W (x j) i) = !![1, 1, 1;
        D.R (20502 / 100), D.R (20505 / 100), D.R (20508 / 100);
        D.Q (20502 / 100), D.Q (20505 / 100), D.Q (20508 / 100)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdet : (Matrix.of fun i j : Fin 3 ↦ W (x j) i).det ≠ 0 := by
    rw [hmatrix]
    exact ne_of_lt (clock_weight_evaluation_det_neg base upTime terminalTime speedConstant hgap)
  obtain ⟨β, hβ, hdisjoint, hmoment⟩ := exists_bumps_moment_matrix_det_ne_zero_of_continuousOn_Icc
      (by cas : (20501 / 100 : ℝ) ≤ 20509 / 100) hW x hx hdet
  exact ⟨β, hβ, hdisjoint, hmoment, surjective_integral_sum_mul_of_bumpMomentMatrix_det_ne_zero W β
      (fun j i ↦ (hβ j).2.2.2.2.2 i) hmoment⟩

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
