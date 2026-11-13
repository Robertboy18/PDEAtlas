/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Forcing.Oscillation
import PDE.Elliptic.Regularity.Coefficients.Restriction

/-!
# Geometric oscillation decay for bounded forcing

The forcing error decreases by a factor of sixteen when the radius is
quartered. A slightly slower contraction than the homogeneous De Giorgi
factor absorbs this error at every step. Consequently the essential range
decays geometrically with amplitude controlled by the initial range and
`R² ‖f‖∞`.

Each step restricts the weak equation and its measurable coefficients
to the current ball.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A weak solution with bounded scalar forcing has a geometrically
shrinking essential range, including the derived forcing contribution. -/
theorem exists_geometric_oscillation_decay_of_bounded_load
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ (θ C : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < C ∧
      ∀ (W : Set ℝ^n) (A : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (f : DerivLp n 2 W) (u : H¹(W)), IsInteriorWeakDivergenceSolution A f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n W, ‖f x‖ ≤ M) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ W →
      ∀ (c N : ℝ), 0 < N →
        (∀ᵐ x ∂volume.restrict (ball z R), |wkpBaseCoordinateCLM u x - c| ≤ N) →
      ∀ j : ℕ, ∃ d : ℝ,
        ∀ᵐ x ∂volume.restrict (ball z ((1 / 4 : ℝ) ^ j * R)),
          |wkpBaseCoordinateCLM u x - d| ≤ θ ^ j * (N + C * R ^ 2 * M) := by
  obtain ⟨ρ, K, hρ, hρ1, hK, hdrop⟩ :=
    exists_oscillation_contraction_of_bounded_load hq2 hq hα hΛ
  let θ := (1 + ρ) / 2
  obtain ⟨hθ, hθ1, hgap⟩ : 0 < θ ∧ θ < 1 ∧ 0 < θ - ρ := by
    dsimp only [θ]
    exact ⟨by linarith, by linarith, by linarith⟩
  let C := K / (θ - ρ)
  have hC : 0 < C := div_pos hK hgap
  have hcancel : (θ - ρ) * C = K := by dsimp only [C]; field_simp
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro W A hAΛ hA f u hu M hM hf z R hR hball c N hN hbound
  let T := N + C * R ^ 2 * M
  have hNM : N ≤ T := le_add_of_nonneg_right (by positivity)
  have hT : 0 < T := hN.trans_le hNM
  have hamp : K * R ^ 2 * M ≤ (θ - ρ) * T := by
    rw [← hcancel]
    linarith [mul_nonneg hgap.le hN.le]
  intro j
  induction j with
  | zero =>
      exact ⟨c, by simpa only [pow_zero, one_mul] using hbound.mono fun _ hx ↦ hx.trans hNM⟩
  | succ j hj =>
      obtain ⟨d, hd⟩ := hj
      let s := ((1 / 4 : ℝ) ^ j * R) / 2
      have hs : 0 < s := by positivity
      have hs2 : s * 2 = (1 / 4 : ℝ) ^ j * R := by dsimp only [s]; ring
      have hsHalf : s * (1 / 2) = (1 / 4 : ℝ) ^ (j + 1) * R := by
        dsimp only [s]
        rw [pow_succ]
        ring
      have hsR : s * 2 ≤ R := by
        rw [hs2]
        exact mul_le_of_le_one_left hR.le (pow_le_one₀ (by norm_num) (by norm_num))
      have hsub : ball z (s * 2) ⊆ W := (ball_subset_ball hsR).trans hball
      let v : H¹(ball z (s * 2)) := restrictCLM isOpen_ball.measurableSet hsub u
      let B (i j : Fin n) : DerivLp n ∞ (ball z (s * 2)) := restrictDerivLp hsub (A i j)
      let g : DerivLp n 2 (ball z (s * 2)) := restrictDerivLp hsub f
      have hv : IsInteriorWeakDivergenceSolution B g v := hu.restrict isOpen_ball hsub
      have hBΛ (i j : Fin n) : ‖B i j‖ ≤ Λ :=
        (norm_restrictDerivLp_le hsub (A i j)).trans (hAΛ i j)
      have hg : ∀ᵐ x ∂domainMeasure n (ball z (s * 2)), ‖g x‖ ≤ M := by
        filter_upwards [restrictDerivLp_apply_ae hsub f,
          hf.filter_mono (ae_mono (domainMeasure_le hsub))] with x hx hb
        change ‖restrictDerivLp hsub f x‖ ≤ M
        rwa [hx]
      have hrep : (wkpBaseCoordinateCLM v : ℝ^n → ℝ)
          =ᵐ[volume.restrict (ball z (s * 2))] wkpBaseCoordinateCLM u :=
        restrictCLM_apply_ae isOpen_ball.measurableSet hsub u (baseIndex n 1)
      have hvBound : ∀ᵐ x ∂volume.restrict (ball z (s * 2)),
          |wkpBaseCoordinateCLM v x - d| ≤ θ ^ j * T := by
        have hd' : ∀ᵐ x ∂volume.restrict (ball z (s * 2)),
            |wkpBaseCoordinateCLM u x - d| ≤ θ ^ j * T := by rwa [hs2]
        filter_upwards [hrep, hd'] with x hx hb
        rwa [hx]
      obtain ⟨e, he⟩ := hdrop z s hs B hBΛ (hA.restrict hsub) g v hv M hM hg
        d (θ ^ j * T) (mul_pos (pow_pos hθ _) hT) hvBound
      have hp : ((1 / 4 : ℝ) ^ j) ^ 2 ≤ θ ^ j := by
        rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
        apply pow_le_pow_left₀ (by positivity)
        dsimp only [θ]
        nlinarith only [hρ]
      have hradius : (s * 2) ^ 2 ≤ θ ^ j * R ^ 2 := by
        rw [hs2, mul_pow]
        exact mul_le_mul_of_nonneg_right hp (sq_nonneg R)
      have herr : K * (s * 2) ^ 2 * M ≤ θ ^ j * ((θ - ρ) * T) := by
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hradius hK.le) hM
        have hb := mul_le_mul_of_nonneg_left hamp (pow_nonneg hθ.le j)
        linear_combination hh + hb
      have hsm : volume.restrict (ball z (s * (1 / 2))) ≤
          volume.restrict (ball z (s * 2)) :=
        domainMeasure_le (ball_subset_ball (mul_le_mul_of_nonneg_left (by norm_num) hs.le))
      refine ⟨e, ?_⟩
      rw [← hsHalf]
      filter_upwards [he, hrep.filter_mono (ae_mono hsm)] with x hx hr
      rw [hr] at hx
      refine hx.trans ?_
      change ρ * (θ ^ j * T) + K * (s * 2) ^ 2 * M ≤ θ ^ (j + 1) * T
      rw [pow_succ]
      linear_combination herr

end SobolevSpace.GraphSpace
