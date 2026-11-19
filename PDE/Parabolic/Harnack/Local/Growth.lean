/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.Barrier.Localization
public import PDE.Parabolic.Harnack.Local.ContactMeasure

/-!
# Earlier low-level measure from a later small value

A normalized expanding barrier and the parabolic contact Jacobian give
a low-level measure bound in an earlier inner cylinder. Geometry and coefficient
bounds determine the constants before the supersolution is supplied. A positive
forcing allowance is retained for approximation of `C²,¹` functions.

This is the smooth contact step: differentiability of the joint spatial gradient
is used by the change-of-variables argument.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A small value at the top forces a quantitative amount of low-level measure
in an earlier cylinder. The residual may have a small negative error, whose
allowance is also chosen before the coefficients and supersolution. -/
theorem exists_localized_sublevel_measure_bound
    {R ρ α τ B b : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hα : 0 < α)
    (hb : 0 < b) (hshort : b < R ^ 2 / 8) :
    ∃ M D ε σ : ℝ, 0 < M ∧ 0 < D ∧ 0 < ε ∧ ε ≤ b / 4 ∧ 0 < σ ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, (a p.1 p.2).PosSemidef) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, ∀ z : ℝ^n,
          α * ‖z‖ ^ 2 ≤ ⟪z, (a p.1 p.2).toEuclideanLin z⟫) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, ‖d p.1 p.2‖ ≤ B) →
        ∀ u : ℝ^n → ℝ → ℝ,
          (∀ p ∈ closedBall (0 : ℝ^n) R ×ˢ Icc 0 b,
            ContDiffAt ℝ 2 (Function.uncurry u) p) →
          (∀ p ∈ closedBall (0 : ℝ^n) R ×ˢ Icc 0 b, 0 ≤ u p.1 p.2) →
          (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b,
            -σ ≤ matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2) →
          ∀ x₀ ∈ closedBall (0 : ℝ^n) (R / 2), u x₀ b ≤ 1 →
            volume (closedBall (0 : ℝ^n) (R / 2) ×ˢ Icc (b / 4) (b / 2)) ≤
              ENNReal.ofReal D * volume ((ball (0 : ℝ^n) ρ ×ˢ Ioc 0 ε) ∩
                {p | u p.1 p.2 ≤ M}) := by
  -- A negative trace or drift bound cannot hold at `(0, b)`: the statement is then vacuous.
  by_cases hτB : 0 ≤ τ ∧ 0 ≤ B
  swap
  · refine ⟨1, 1, b / 4, 1, one_pos, one_pos, by positivity, le_rfl, one_pos, ?_⟩
    intro a d ha _ htrace hdrift
    exfalso
    have hp : ((0 : ℝ^n), b) ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b := ⟨mem_ball_self hR, hb, le_rfl⟩
    rcases not_and_or.mp hτB with hτ | hB
    · exact hτ ((ha _ hp).trace_nonneg.trans (htrace _ hp))
    · exact hB ((norm_nonneg _).trans (hdrift _ hp))
  obtain ⟨hτ, hB⟩ := hτB
  obtain ⟨φ, M, F, κ, ε, σ, hφ, hM, _, hκ, hscale, hε, hεb, hσ,
    hφbound, hφtop, hφinitial, hφlateral, hbarrier⟩ :=
    exists_barrier_for_contact_localization (n := n) hR hρ hb hα hτ hB
  let D₀ := ((τ + B * (2 * R) + κ⁻¹ * (F + σ) + 1) / α) ^ n *
    (τ + B * (2 * R) + κ⁻¹ * (F + σ) + 1)
  refine ⟨M + κ * b, max 1 D₀, ε, σ, by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), hε, hεb, hσ, ?_⟩
  intro a d ha hell htrace hdrift u hreg hnonneg hsuper x₀ hx₀ hsmall
  obtain ⟨hφres, hφoutside⟩ := hbarrier a d ha hell htrace hdrift
  let w := fun x t ↦ u x t - φ x t
  have hinside : ball (0 : ℝ^n) R ×ˢ Ioc 0 b ⊆ closedBall 0 R ×ˢ Icc 0 b :=
    fun _ hp ↦ ⟨ball_subset_closedBall hp.1, hp.2.1.le, hp.2.2⟩
  have hwreg (p : ℝ^n × ℝ) (hp : p ∈ closedBall 0 R ×ˢ Icc 0 b) :
      ContDiffAt ℝ 2 (Function.uncurry w) p := (hreg p hp).sub hφ.contDiffAt
  have hspace (p : ℝ^n × ℝ) (hp : p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b) :
      ContDiffAt ℝ 2 (fun x ↦ w x p.2) p.1 :=
    (hwreg p (hinside hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hres (p : ℝ^n × ℝ) (hp : p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b) :
      matrixParabolicOperator a d (fun _ _ ↦ 0) w p.1 p.2 =
        matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2 -
          matrixParabolicOperator a d (fun _ _ ↦ 0) φ p.1 p.2 :=
    matrixParabolicOperator_sub a d (fun _ _ ↦ 0)
      ((hreg p (hinside hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const))
      (hφ.contDiffAt.comp p.1 (contDiffAt_id.prodMk contDiffAt_const))
      (((hreg p (hinside hp)).comp p.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))
      ((hφ.contDiffAt.comp p.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))
  have hmeasure := vertex_measure_le_mul_sublevel_measure hR hκ hα hb hshort hscale
    a d hell htrace hdrift w
    (fun p hp ↦ (hwreg p hp).continuousAt.continuousWithinAt)
    (fun p hp ↦
      (contDiffAt_gradient_fst (m := 1) (hwreg p hp)).continuousAt.continuousWithinAt)
    (fun p hp ↦ (hwreg p (hinside hp)).differentiableAt (by norm_num))
    (fun p hp ↦ (contDiffAt_gradient_fst (m := 1)
      (hwreg p (hinside hp))).differentiableAt (by norm_num))
    hspace
    (F := F + σ) (fun p hp ↦ by rw [hres p hp]; linarith [hsuper p hp, hφres p hp])
    (ball (0 : ℝ^n) ρ ×ˢ Ioc 0 ε)
    (fun p hp hout ↦ by rw [hres p hp]; linarith [hsuper p hp, hφoutside p hp hout])
    (fun x hx ↦ by
      dsimp [w]
      rw [hφinitial, sub_zero]
      exact hnonneg (x, 0) ⟨hx, le_rfl, hb.le⟩)
    (fun x hx t ht ↦ by
      have hpos := hnonneg (x, t) ⟨sphere_subset_closedBall hx, ht⟩
      have hneg := hφlateral x hx t ht
      dsimp [w]
      linarith)
    hx₀ (by dsimp [w]; linarith [hφtop x₀ hx₀])
  refine hmeasure.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right 1 D₀))
    (measure_mono fun p hp ↦ ⟨hp.1.2, ?_⟩))
  have hwlow : u p.1 p.2 - φ p.1 p.2 ≤ κ * b := hp.2
  change u p.1 p.2 ≤ M + κ * b
  linarith [hφbound p.1 p.2 ⟨hp.1.1.2.1.le, hp.1.1.2.2⟩]

end ParabolicHarnack
