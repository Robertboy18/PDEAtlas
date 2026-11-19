/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallOscillation
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Forcing.Comparison

/-!
# De Giorgi oscillation contraction with bounded scalar forcing

Subtracting the zero-boundary particular solution reduces the equation
to the homogeneous one. The homogeneous De Giorgi theorem contracts its
essential range, while the correction contributes at most
`C R² ‖f‖∞`. Adding the correction back gives an oscillation contraction
with a quadratically decaying forcing error.

The contraction factor and error constant are independent of the ball and
the solution. The coefficient matrix remains merely measurable.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The essential range contracts on the quarter-radius ball, up to the
quadratic-radius error contributed by the bounded scalar forcing. -/
theorem exists_oscillation_contraction_of_bounded_load
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ (ρ C : ℝ), 0 < ρ ∧ ρ < 1 ∧ 0 < C ∧
      ∀ (z : ℝ^n) (s : ℝ), 0 < s →
      ∀ A : Fin n → Fin n → DerivLp n ∞ (ball z (s * 2)),
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (f : DerivLp n 2 (ball z (s * 2))) (u : H¹(ball z (s * 2))),
        IsInteriorWeakDivergenceSolution A f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n (ball z (s * 2)), ‖f x‖ ≤ M) →
      ∀ (c N : ℝ), 0 < N →
        (∀ᵐ x ∂volume.restrict (ball z (s * 2)),
          |wkpBaseCoordinateCLM u x - c| ≤ N) →
        ∃ d : ℝ, ∀ᵐ x ∂volume.restrict (ball z (s * (1 / 2))),
          |wkpBaseCoordinateCLM u x - d| ≤ ρ * N + C * (s * 2) ^ 2 * M := by
  obtain ⟨ρ, hρ, hρ1, hdrop⟩ :=
    exists_oscillation_contraction_on_rescaled_balls hq2 hq hα hΛ
  obtain ⟨K, hK, hcomparison⟩ := exists_bounded_load_homogeneous_comparison hq2 hq hα
  refine ⟨ρ, 2 * K, hρ, hρ1, mul_pos (by norm_num) hK, ?_⟩
  intro z s hs A hAΛ hA f u hu M hM hf c N hN hbound
  obtain ⟨w, _, hh, hw⟩ :=
    hcomparison z (s * 2) (mul_pos hs (by norm_num)) A hA f u hu M hM hf
  let v := u - (w : H¹(ball z (s * 2)))
  let δ := K * (s * 2) ^ 2 * M
  have hδ : 0 ≤ δ := mul_nonneg (mul_nonneg hK.le (sq_nonneg _)) hM
  have hrep : (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[
      domainMeasure n (ball z (s * 2))]
        fun x ↦ wkpBaseCoordinateCLM u x - baseCoordCLM w x :=
    baseRepresentative_sub_ae u (w : H¹(ball z (s * 2)))
  have hvBound : ∀ᵐ x ∂domainMeasure n (ball z (s * 2)),
      |wkpBaseCoordinateCLM v x - c| ≤ N + δ := by
    filter_upwards [hrep, hbound, hw] with x hx hb hw
    rw [hx, show wkpBaseCoordinateCLM u x - baseCoordCLM w x - c =
      (wkpBaseCoordinateCLM u x - c) - baseCoordCLM w x by ring]
    exact (abs_sub _ _).trans (add_le_add hb (by simpa only [Real.norm_eq_abs] using hw))
  obtain ⟨d, _, hd⟩ := hdrop z s hs A hAΛ hA v hh c (N + δ)
    (add_pos_of_pos_of_nonneg hN hδ) hvBound
  have hm : domainMeasure n (ball z (s * (1 / 2))) ≤
      domainMeasure n (ball z (s * 2)) :=
    domainMeasure_le (ball_subset_ball (mul_le_mul_of_nonneg_left (by norm_num) hs.le))
  refine ⟨d, ?_⟩
  filter_upwards [hd, hrep.filter_mono (ae_mono hm), hw.filter_mono (ae_mono hm)]
    with x hx hr hw
  have hid : wkpBaseCoordinateCLM u x - d =
      (wkpBaseCoordinateCLM v x - d) + baseCoordCLM w x := by rw [hr]; ring
  have hsmall : |wkpBaseCoordinateCLM u x - d| ≤ ρ * (N + δ) + δ := by
    rw [hid]
    exact (abs_add_le _ _).trans
      (add_le_add hx (by simpa only [Real.norm_eq_abs] using hw))
  have hρδ := mul_le_mul_of_nonneg_right hρ1.le hδ
  apply hsmall.trans
  change ρ * (N + δ) + δ ≤ ρ * N + 2 * K * (s * 2) ^ 2 * M
  dsimp only [δ] at hρδ ⊢
  nlinarith only [hρδ]

end SobolevSpace.GraphSpace
