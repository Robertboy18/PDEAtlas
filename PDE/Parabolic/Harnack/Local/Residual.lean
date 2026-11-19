/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.SignedPotential
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator.Perturbation

/-!
# Local Harnack comparison with a residual error

Adding the residual bound to a nonnegative field makes it strictly positive.
Absorbing its remaining residual into the potential produces an exact solution
with a uniformly bounded potential. The signed-potential comparison therefore
gives an additive error that vanishes with the residual bound.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The local jointly C² comparison tolerates a uniformly small
residual. Its constant is independent of both the field and the error size. -/
theorem exists_local_comparison_with_residual
    {α τ B K : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (c : ℝ^n → ℝ → ℝ),
        let Q := closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64
        (∀ v ∈ Q, (a v.1 v.2).PosSemidef) →
        (∀ v ∈ Q, ∀ w : ℝ^n,
          α * ‖w‖ ^ 2 ≤ ⟪w, (a v.1 v.2).toEuclideanLin w⟫) →
        (∀ v ∈ Q, (a v.1 v.2).trace ≤ τ) →
        (∀ v ∈ Q, ‖d v.1 v.2‖ ≤ B) →
        (∀ v ∈ Q, |c v.1 v.2| ≤ K) →
        ∀ (u : ℝ^n → ℝ → ℝ) (ε : ℝ), 0 < ε →
          (∀ v ∈ Q, ContDiffAt ℝ 2 (Function.uncurry u) v) →
          (∀ v ∈ Q, 0 ≤ u v.1 v.2) →
          (∀ v ∈ Q, |matrixParabolicOperator a d c u v.1 v.2| ≤ ε) →
          ∀ x ∈ closedBall (0 : ℝ^n) (1 / 2), ∀ t ∈ Icc (-1 / 2) 0,
            ∀ y ∈ closedBall (0 : ℝ^n) 1, u x t ≤ C * (u y 64 + ε) := by
  obtain ⟨C, hC, hcompare⟩ := exists_local_signed_comparison_of_contDiff_two
    (n := n) (K := K + (1 + K)) hα hτ hB (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a d c
  dsimp only
  intro ha hell htrace hdrift hpotential u ε hε hreg hnonneg hres x hx t ht y hy
  let w : ℝ^n → ℝ → ℝ := fun z s ↦ u z s + ε
  let c' : ℝ^n → ℝ → ℝ :=
    fun z s ↦ c z s - matrixParabolicOperator a d c w z s / w z s
  have hw (p : ℝ^n × ℝ)
      (hp : p ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1 : ℝ) 64) :
      ε ≤ w p.1 p.2 := le_add_of_nonneg_left (hnonneg p hp)
  have hwres (p : ℝ^n × ℝ)
      (hp : p ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1 : ℝ) 64) :
      |matrixParabolicOperator a d c w p.1 p.2| ≤ (1 + K) * ε := by
    rw [show w = fun z s ↦ u z s + ε from rfl,
      matrixParabolicOperator_add_const a d c (u := u) (x := p.1) (t := p.2)
        ((hreg p hp).comp p.1 (contDiffAt_id.prodMk contDiffAt_const))
        (((hreg p hp).comp p.2
          (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))]
    calc
      _ ≤ ε + K * ε := (abs_add_le _ _).trans (add_le_add (hres p hp) (by
        rw [abs_mul, abs_of_pos hε]
        exact mul_le_mul_of_nonneg_right (hpotential p hp) hε.le))
      _ = _ := by rw [add_mul, one_mul]
  specialize hcompare a d c'
  dsimp only at hcompare
  specialize hcompare ha hell htrace hdrift
    (fun p hp ↦ abs_corrected_potential_le a d c w hε (by positivity)
      (hw p hp) (hpotential p hp) (hwres p hp)) w
    (fun p hp ↦ (hreg p hp).add contDiffAt_const)
    (fun p hp ↦ hε.le.trans (hw p hp))
    (fun p hp ↦ matrixParabolicOperator_correct_potential a d c w
      (hε.trans_le (hw p hp)).ne')
  have h := hcompare x hx t ht y hy
  exact (le_add_of_nonneg_right hε.le).trans h

end ParabolicHarnack
