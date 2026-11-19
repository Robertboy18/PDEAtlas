/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallOscillation
import PDE.Elliptic.Regularity.Coefficients.Restriction

/-!
# Geometric decay of the essential range

Restricting the weak solution to each smaller ball preserves its
coefficient bounds. The uniform oscillation contraction can therefore be
iterated. The centres of the essential ranges are constructed at each step;
neither continuity nor decay is an assumption on the solution.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A measurable-coefficient weak solution has a geometrically
shrinking essential range on balls whose radii decrease by a factor of four.
The contraction is uniform in the domain, ball, and solution. -/
theorem exists_geometric_oscillation_decay
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ (W : Set (ℝ^n)) (A : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ W →
      ∀ (c M : ℝ), 0 < M →
        (∀ᵐ x ∂volume.restrict (ball z R), |wkpBaseCoordinateCLM u x - c| ≤ M) →
        ∀ j : ℕ, ∃ d : ℝ,
          ∀ᵐ x ∂volume.restrict (ball z ((1 / 4 : ℝ) ^ j * R)),
            |wkpBaseCoordinateCLM u x - d| ≤ ρ ^ j * M := by
  obtain ⟨ρ, hρ, hρ1, hdrop⟩ :=
    exists_oscillation_contraction_on_rescaled_balls hq2 hq hα hΛ
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro W A hAΛ hA u hu z R hR hball c M hM hbound j
  induction j with
  | zero =>
      refine ⟨c, ?_⟩
      simpa only [pow_zero, one_mul] using hbound
  | succ j hj =>
      obtain ⟨d, hd⟩ := hj
      let s := ((1 / 4 : ℝ) ^ j * R) / 2
      have hs : 0 < s := div_pos (mul_pos (pow_pos (by norm_num) _) hR) (by norm_num)
      have hs2 : s * 2 = (1 / 4 : ℝ) ^ j * R := by dsimp only [s]; ring
      have hsHalf : s * (1 / 2) = (1 / 4 : ℝ) ^ (j + 1) * R := by
        dsimp only [s]
        rw [pow_succ]
        ring
      have hsR : s * 2 ≤ R := by
        rw [hs2]
        exact (mul_le_mul_of_nonneg_right
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)) hR.le).trans_eq
          (one_mul R)
      have hsub : ball z (s * 2) ⊆ W := (ball_subset_ball hsR).trans hball
      let v : H¹(ball z (s * 2)) := restrictCLM isOpen_ball.measurableSet hsub u
      let B (i j : Fin n) : DerivLp n ∞ (ball z (s * 2)) := restrictDerivLp hsub (A i j)
      have hv : IsInteriorWeakDivergenceSolution B 0 v := by
        simpa only [map_zero] using hu.restrict isOpen_ball hsub
      have hBΛ (i j : Fin n) : ‖B i j‖ ≤ Λ :=
        (norm_restrictDerivLp_le hsub (A i j)).trans (hAΛ i j)
      have hrep : (wkpBaseCoordinateCLM v : ℝ^n → ℝ)
          =ᵐ[volume.restrict (ball z (s * 2))] wkpBaseCoordinateCLM u :=
        restrictCLM_apply_ae isOpen_ball.measurableSet hsub u (baseIndex n 1)
      have hvbound : ∀ᵐ x ∂volume.restrict (ball z (s * 2)),
          |wkpBaseCoordinateCLM v x - d| ≤ ρ ^ j * M := by
        have hd' : ∀ᵐ x ∂volume.restrict (ball z (s * 2)),
            |wkpBaseCoordinateCLM u x - d| ≤ ρ ^ j * M := by
          rwa [hs2]
        filter_upwards [hrep, hd'] with x hx hb
        rwa [hx]
      obtain ⟨e, _, he⟩ := hdrop z s hs B hBΛ (hA.restrict hsub) v hv
        d (ρ ^ j * M) (mul_pos (pow_pos hρ _) hM) hvbound
      refine ⟨e, ?_⟩
      have hsm : volume.restrict (ball z (s * (1 / 2))) ≤
          volume.restrict (ball z (s * 2)) :=
        domainMeasure_le (ball_subset_ball (mul_le_mul_of_nonneg_left (by norm_num) hs.le))
      rw [← hsHalf]
      filter_upwards [he, hrep.filter_mono (ae_mono hsm)] with x hx hr
      rw [hr] at hx
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hx

end SobolevSpace.GraphSpace
