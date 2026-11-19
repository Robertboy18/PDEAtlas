/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.BallChain.TimeSteps
public import Mathlib.Analysis.Normed.Affine.AddTorsor
import CAS.ExactTactic

/-!
# Forward comparison along a spatial segment

Equal subdivisions of a segment fit any prescribed positive elapsed time:
the spatial steps decrease like `N⁻¹`, while their parabolic radius decreases
like `N⁻¹ᐟ²`. Multiplicative local comparisons then compose with a constant
selected before the field or the endpoints of the segment.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform comparison along every segment of length at most `R` whose
enlarged ball is interior. No regularity or equation is used beyond the
given local forward comparison. -/
theorem exists_forward_comparison_on_segment
    {U : Set E} {ℓ T L ρ κ A R s t : ℝ}
    (hL : 0 ≤ L) (hκ : 0 < κ) (hA : 0 < A)
    (hR : 0 < R) (hRρ : R ≤ ρ) (hs : ℓ < s) (hst : s < t) (ht : t ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ → ℝ,
      (∀ (x y : E) (r a : ℝ), 0 < r → r ≤ ρ →
        closedBall x (L * r) ⊆ U → dist x y ≤ r → ℓ < a - 2 * r ^ 2 →
        a + κ * r ^ 2 ≤ T → u x a ≤ A * u y (a + κ * r ^ 2)) →
      ∀ x y : E, dist x y ≤ R → closedBall x ((L + 1) * R) ⊆ U →
        u x s ≤ C * u y t := by
  obtain ⟨N, hN, r, hr, hrR, hstep, hmargin, htotal⟩ :=
    exists_parabolic_equal_time_steps hκ (sub_pos.mpr hst) hR (sub_pos.mpr hs)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hδ : 0 < κ * r ^ 2 := mul_pos hκ (sq_pos_of_pos hr)
  refine ⟨A ^ N, pow_pos hA N, ?_⟩
  intro u hlocal x y hxy hball
  let γ : ℕ → E := fun i ↦ AffineMap.lineMap x y ((i : ℝ) / (N : ℝ))
  have hγzero : γ 0 = x := by simp [γ]
  have hγlast : γ N = y := by simp [γ, hNreal.ne']
  have hγdist (i : ℕ) (hi : i ≤ N) : dist (γ i) x ≤ R := by
    dsimp only [γ]
    rw [dist_lineMap_left, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNreal.le)]
    have hfrac : (i : ℝ) / (N : ℝ) ≤ 1 :=
      (div_le_one hNreal).mpr (by exact_mod_cast hi)
    exact (mul_le_mul_of_nonneg_left hxy
      (div_nonneg (Nat.cast_nonneg _) hNreal.le)).trans
      (mul_le_of_le_one_left hR.le hfrac)
  have hγstep (i : ℕ) : dist (γ i) (γ (i + 1)) ≤ r := by
    have hdiff : (i : ℝ) / (N : ℝ) - ((i + 1 : ℕ) : ℝ) / (N : ℝ) =
        -(1 / (N : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_one]
      cas
    dsimp only [γ]
    rw [dist_lineMap_lineMap, dist_eq_norm, Real.norm_eq_abs, hdiff, abs_neg,
      abs_of_pos (div_pos zero_lt_one hNreal)]
    calc
      (1 / (N : ℝ)) * dist x y ≤ (1 / (N : ℝ)) * R :=
        mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = R / (N : ℝ) := by cas
      _ ≤ r := hstep
  have hγball (i : ℕ) (hi : i ≤ N) : closedBall (γ i) (L * r) ⊆ U := by
    intro z hz
    apply hball
    change dist z x ≤ (L + 1) * R
    have hzγ : dist z (γ i) ≤ L * r := hz
    have hγx := hγdist i hi
    have htriangle := dist_triangle z (γ i) x
    have hscale := mul_le_mul_of_nonneg_left hrR hL
    nlinarith
  have hclock (i : ℕ) :
      s + (i : ℝ) * (κ * r ^ 2) + κ * r ^ 2 =
        s + ((i + 1 : ℕ) : ℝ) * (κ * r ^ 2) := by
    rw [Nat.cast_add, Nat.cast_one]
    cas
  have hcompare (i : ℕ) (hi : i < N) :
      u (γ i) (s + (i : ℝ) * (κ * r ^ 2)) ≤
        A * u (γ (i + 1)) (s + ((i + 1 : ℕ) : ℝ) * (κ * r ^ 2)) := by
    rw [← hclock]
    apply hlocal _ _ r _ hr (hrR.trans hRρ) (hγball i hi.le) (hγstep i)
    · have hnonneg := mul_nonneg (Nat.cast_nonneg i) hδ.le
      linarith
    · rw [hclock]
      have hiN : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      have htime := mul_le_mul_of_nonneg_right hiN hδ.le
      linarith
  have hchain (i : ℕ) (hi : i ≤ N) :
      u x s ≤ A ^ i * u (γ i) (s + (i : ℝ) * (κ * r ^ 2)) := by
    induction i with
    | zero =>
        simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, hγzero, one_mul, le_refl]
    | succ i ih =>
        have hiN : i < N := Nat.lt_of_succ_le hi
        calc
          u x s ≤ A ^ i * u (γ i) (s + (i : ℝ) * (κ * r ^ 2)) := ih hiN.le
          _ ≤ A ^ i *
              (A * u (γ (i + 1)) (s + ((i + 1 : ℕ) : ℝ) * (κ * r ^ 2))) :=
            mul_le_mul_of_nonneg_left (hcompare i hiN) (pow_nonneg hA.le i)
          _ = A ^ (i + 1) * u (γ (i + 1))
              (s + ((i + 1 : ℕ) : ℝ) * (κ * r ^ 2)) := by rw [pow_succ A i, mul_assoc]
  have htime : s + (N : ℝ) * (κ * r ^ 2) = t := by linarith
  simpa only [hγlast, htime] using hchain N le_rfl

end PDE.Analysis
