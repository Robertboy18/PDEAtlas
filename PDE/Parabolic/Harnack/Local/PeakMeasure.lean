/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.ScaledGrowth
import CAS.ExactTactic

/-!
# Positive superlevel mass before an almost maximal value

The complement of an almost maximal positive solution is a nonnegative
solution with normalized value one at the top center. Applying the contact
estimate to that complement gives a fixed amount of earlier superlevel mass.
All constants, including the permitted excess, precede the solution.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A solution bounded above by a fixed multiple of its positive top-center
value has a quantitative amount of superlevel mass earlier in the cylinder. -/
theorem exists_peak_superlevel_measure_bound
    {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ η D ε : ℝ, 0 < η ∧ 0 < D ∧ 0 < ε ∧ ε ≤ 1 / 64 ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (z : ℝ^n) (s r : ℝ), 0 < r → r ≤ 1 →
        (∀ p ∈ ball z r ×ˢ Ioc s (s + r ^ 2 * (1 / 16)),
          (a p.1 p.2).PosSemidef) →
        (∀ p ∈ ball z r ×ˢ Ioc s (s + r ^ 2 * (1 / 16)), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a p.1 p.2).toEuclideanLin v⟫) →
        (∀ p ∈ ball z r ×ˢ Ioc s (s + r ^ 2 * (1 / 16)),
          (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ ball z r ×ˢ Ioc s (s + r ^ 2 * (1 / 16)), ‖d p.1 p.2‖ ≤ B) →
        ∀ u : ℝ^n → ℝ → ℝ,
          (∀ p ∈ closedBall z r ×ˢ Icc s (s + r ^ 2 * (1 / 16)),
            ContDiffAt ℝ 2 (Function.uncurry u) p) →
          (∀ p ∈ ball z r ×ˢ Ioc s (s + r ^ 2 * (1 / 16)),
            matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2 = 0) →
          0 < u z (s + r ^ 2 * (1 / 16)) →
          (∀ p ∈ closedBall z r ×ˢ Icc s (s + r ^ 2 * (1 / 16)),
            u p.1 p.2 ≤ (1 + η) * u z (s + r ^ 2 * (1 / 16))) →
          r ^ (n + 2) *
              volume.real
                (closedBall (0 : ℝ^n) (1 / 2) ×ˢ Icc (1 / 64 : ℝ) (1 / 32)) ≤
            D * volume.real ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩
              {p | u z (s + r ^ 2 * (1 / 16)) / 4 < u p.1 p.2}) := by
  obtain ⟨M, D, ε, σ, hM, hD, hε, hεb, hσ, hbound⟩ :=
    exists_scaled_sublevel_measure_bound (n := n) (R := 1) (ρ := 1)
      (b := 1 / 16) zero_lt_one zero_lt_one hα hB (by norm_num) (by norm_num)
  let η := (2 * M)⁻¹
  have hMpos : 0 < M := by linarith only [hM]
  have hη : 0 < η := inv_pos.mpr (mul_pos (by norm_num) hMpos)
  have hηM : η * M = 1 / 2 := by
    dsimp only [η]
    clear * - hMpos
    cas using hMpos.ne'
  refine ⟨η, D, ε, hη, hD, hε, by norm_num at hεb ⊢; exact hεb, ?_⟩
  intro a d z s r hr hr₁ ha hell htrace hdrift u hreg hsol hpeak hupper
  let P := u z (s + r ^ 2 * (1 / 16))
  let w := fun x t ↦ (η * P)⁻¹ * ((1 + η) * P - u x t)
  have hwreg (p : ℝ^n × ℝ) (hp : p ∈ closedBall z r ×ˢ Icc s (s + r ^ 2 * (1 / 16))) :
      ContDiffAt ℝ 2 (Function.uncurry w) p :=
    contDiffAt_const.mul (contDiffAt_const.sub (hreg p hp))
  have hwnonneg (p : ℝ^n × ℝ) (hp : p ∈ closedBall z r ×ˢ Icc s (s + r ^ 2 * (1 / 16))) :
      0 ≤ w p.1 p.2 :=
    mul_nonneg (inv_nonneg.mpr (mul_nonneg hη.le hpeak.le)) (sub_nonneg.mpr (hupper p hp))
  have hwsol (p : ℝ^n × ℝ) (hp : p ∈ ball z r ×ˢ Ioc s (s + r ^ 2 * (1 / 16))) :
      matrixParabolicOperator a d (fun _ _ ↦ 0) w p.1 p.2 = 0 := by
    have hp' : p ∈ closedBall z r ×ˢ Icc s (s + r ^ 2 * (1 / 16)) :=
      ⟨ball_subset_closedBall hp.1, hp.2.1.le, hp.2.2⟩
    have hs := (hreg p hp').comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
    have ht := ((hreg p hp').comp p.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
    change matrixParabolicOperator a d (fun _ _ ↦ 0)
      (fun x t ↦ (η * P)⁻¹ * ((1 + η) * P - u x t)) p.1 p.2 = 0
    rw [matrixParabolicOperator_const_mul a d (fun _ _ ↦ 0)
      (u := fun x t ↦ (1 + η) * P - u x t) (x := p.1) (t := p.2)
      ((contDiffAt_const.sub hs).differentiableAt (by norm_num))
      ((differentiableAt_const _).sub ht)]
    rw [matrixParabolicOperator_sub a d (fun _ _ ↦ 0)
      (u := fun _ _ ↦ (1 + η) * P) (v := u) (x := p.1) (t := p.2) contDiffAt_const hs
      (differentiableAt_const _) ht, matrixParabolicOperator_const, hsol p hp]
    simp
  have hwpeak : w z (s + r ^ 2 * (1 / 16)) = 1 := by
    change (η * P)⁻¹ * ((1 + η) * P - P) = 1
    have hP : 0 < P := hpeak
    clear * - hη hP
    cas using (mul_pos hη hP).ne'
  have hgrowth := hbound a d z s r hr hr₁
    (by simpa only [mul_one] using ha)
    (by simpa only [mul_one] using hell)
    (by simpa only [mul_one] using htrace)
    (by simpa only [mul_one] using hdrift)
    w 1 zero_lt_one (by simpa only [mul_one] using hwreg)
    (by simpa only [mul_one] using hwnonneg)
    (fun p hp ↦ by
      rw [hwsol p (by simpa only [mul_one] using hp), mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) zero_le_one)
    z (by simp [hr.le]) hwpeak.le
  norm_num only [mul_one] at hgrowth
  have hsubset :
      ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩ {p | w p.1 p.2 ≤ M}) ⊆
        ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩ {p | P / 4 < u p.1 p.2}) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hlow := (inv_mul_le_iff₀ (mul_pos hη hpeak)).mp (show w p.1 p.2 ≤ M from hp.2)
    rw [mul_right_comm, hηM] at hlow
    change P / 4 < u p.1 p.2
    linarith only [hlow, hpeak, mul_pos hη hpeak]
  have hfinite : volume
      ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩ {p | P / 4 < u p.1 p.2}) ≠ ⊤ :=
    (measure_mono (show
      ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩ {p | P / 4 < u p.1 p.2}) ⊆
        closedBall z r ×ˢ Icc s (s + r ^ 2 * ε) from
      fun _ hp ↦ ⟨ball_subset_closedBall hp.1.1, hp.1.2.1.le, hp.1.2.2⟩) |>.trans_lt
      ((isCompact_closedBall z r).prod isCompact_Icc).measure_lt_top).ne
  exact hgrowth.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hD.le)

end ParabolicHarnack
