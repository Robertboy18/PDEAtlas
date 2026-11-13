/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harnack.Local.ScaledGrowth
import CAS.ExactTactic

/-!
# Positive superlevel mass near an almost maximal value

If a solution grows by at most a fixed small fraction of its value at the
center, its complement is a nonnegative solution with value one there.
The contact estimate for that complement gives a fixed amount of mass above
one quarter of the original center value.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- An almost maximal positive value forces positive superlevel mass. The
allowed excess and the measure constant are chosen before the solution. -/
theorem exists_peak_superlevel_measure_bound
    {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
        (z : ℝ^n) (r : ℝ), 0 < r → r ≤ 1 →
        (∀ x ∈ ball z r, (a x).PosSemidef) →
        (∀ x ∈ ball z r, ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball z r, (a x).trace ≤ τ) →
        (∀ x ∈ ball z r, ‖b x‖ ≤ B) →
        ∀ u : ℝ^n → ℝ, ContinuousOn u (closedBall z r) →
        (∀ x ∈ ball z r, ContDiffAt ℝ 2 u x) →
        (∀ x ∈ ball z r, matrixOperator a b (fun _ ↦ 0) u x = 0) →
        0 < u z → (∀ x ∈ closedBall z r, u x ≤ (1 + ε) * u z) →
          r ^ n * volume.real (closedBall (0 : ℝ^n) (1 / 2)) ≤
            D * volume.real (ball z r ∩ {x | u z / 4 < u x}) := by
  obtain ⟨M, D, hM, hD, hbound⟩ :=
    exists_scaled_sublevel_measure_bound (n := n) (R := 1) (ρ := 1)
      zero_lt_one zero_lt_one hα hB
  let ε := (2 * M)⁻¹
  have hMpos : 0 < M := by linarith
  have hε : 0 < ε := inv_pos.mpr (mul_pos (by norm_num) hMpos)
  have hεM : ε * M = 1 / 2 := by
    dsimp [ε]
    cas using hMpos.ne'
  refine ⟨ε, D, hε, hD, ?_⟩
  intro a b z r hr hr₁ ha hell htrace hdrift u hu hreg hsol huz hupper
  let w := fun x ↦ (ε * u z)⁻¹ * ((1 + ε) * u z - u x)
  have hwreg : ∀ x ∈ ball z r, ContDiffAt ℝ 2 w x :=
    fun x hx ↦ contDiffAt_const.mul (contDiffAt_const.sub (hreg x hx))
  have hwcont : ContinuousOn w (closedBall z r) :=
    (continuousOn_const.sub hu).const_mul _
  have hwnonneg : ∀ x ∈ closedBall z r, 0 ≤ w x :=
    fun x hx ↦ mul_nonneg (inv_nonneg.mpr (mul_nonneg hε.le huz.le))
      (sub_nonneg.mpr (hupper x hx))
  have hwsuper : ∀ x ∈ ball z r, 0 ≤ matrixOperator a b (fun _ ↦ 0) w x := by
    intro x hx
    change 0 ≤ matrixOperator a b (fun _ ↦ 0)
      (fun y ↦ (ε * u z)⁻¹ * ((1 + ε) * u z - u y)) x
    rw [matrixOperator_const_mul a b (fun _ ↦ 0)
      ((contDiffAt_const.sub (hreg x hx)).differentiableAt (by norm_num))]
    rw [matrixOperator_sub a b (fun _ ↦ 0) contDiffAt_const (hreg x hx),
      matrixOperator_const, hsol x hx]
    simp
  have hwz : w z = 1 := by
    dsimp [w]
    cas using (mul_pos hε huz).ne'
  have hgrowth := hbound a b z r hr hr₁ (by simpa using ha) (by simpa using hell)
    (by simpa using htrace) (by simpa using hdrift) w (by simpa using hwcont)
    (by simpa using hwreg) (by simpa using hwnonneg) (by simpa using hwsuper)
    1 zero_lt_one z (by simp [hr.le]) hwz.le
  simp only [mul_one] at hgrowth
  have hsubset : ball z r ∩ {x | w x ≤ M} ⊆ ball z r ∩ {x | u z / 4 < u x} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hlow : (ε * u z)⁻¹ * ((1 + ε) * u z - u x) ≤ M := hx.2
    have hlow' := (inv_mul_le_iff₀ (mul_pos hε huz)).mp hlow
    change u z / 4 < u x
    have hid : ε * u z * M = u z / 2 := by
      calc
        ε * u z * M = (ε * M) * u z := by ring
        _ = u z / 2 := by rw [hεM]; ring
    rw [hid] at hlow'
    nlinarith [mul_pos hε huz]
  exact hgrowth.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono hsubset
      (measure_mono inter_subset_left |>.trans_lt measure_ball_lt_top).ne) hD.le)

end EllipticHarnack
