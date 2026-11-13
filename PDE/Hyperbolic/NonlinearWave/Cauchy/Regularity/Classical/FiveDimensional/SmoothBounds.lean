/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.Interpolation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothBounds
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Affine H³ control of second-order composition in dimension five

The quadratic first-derivative term is controlled by interpolation. On an H²
ball this gives an affine H³ bound, using only global bounds for f' and f''.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GagliardoNirenberg SobolevSpace.Composition
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Bounds on the first two reaction derivatives control positive-order
composition in H² by an affine function of the H³ norm on every H² ball. -/
theorem exists_smooth_h2_composition_derivative_affine_h3_bound_five {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ y l, 0 < l → l ≤ 2 → ‖iteratedFDeriv ℝ l f y‖ ≤ D) {j : ℕ} (hj : 0 < j) (hj2 : j ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^5 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
      MemLp (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ∧
        lpNorm (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ≤
          C * (1 + ‖mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) u hu hc‖) := by
  have hlow (u : ℝ^5 → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
      (hur : ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R)
      {l : ℕ} (hl : l ≤ 2) : lpNorm (iteratedFDeriv ℝ l u) 2 volume ≤ (5 : ℝ) ^ l * R :=
    lpNorm_iteratedFDeriv_le_of_coordinate_bounds l hu hc (by norm_num) fun α hα ↦
      (lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc α (hα.trans_le hl)).trans hur
  interval_cases j
  · refine ⟨5 * D * R, by positivity, fun u hu hc hur ↦ ?_⟩
    have he := lpNorm_iteratedFDeriv_comp_le_of_derivative_bounds (by decide : 0 < 1) hf hu hc hD
      (fun y l hl hlj ↦ hb y l hl (hlj.trans (by decide))) (fun _ ↦ 5 * R) (by
        intro i
        fin_cases i
        simpa using hlow u hu hc hur (by decide : 1 ≤ 2))
    refine ⟨he.1, he.2.trans ?_⟩
    simp only [Fin.sum_univ_one]
    norm_num
    calc
      D * (5 * R) = 5 * D * R := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (norm_nonneg _))
  · obtain ⟨A, hA, hfirst⟩ := Inequalities.exists_lpNorm_firstDerivative_l4_sq_le_h2_h3_five
    let B := A * R ^ (3 / 2 : ℝ)
    have hB : 0 ≤ B := mul_nonneg hA (Real.rpow_nonneg hR _)
    refine ⟨100 * D * (B + R), by positivity, fun u hu hc hur ↦ ?_⟩
    let N := ‖mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) u hu hc‖
    have hN : 0 ≤ N := norm_nonneg _
    have hhalf : N ^ (1 / 2 : ℝ) ≤ 1 + N :=
      (Real.rpow_le_rpow hN (by linarith) (by norm_num)).trans
        (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))
    have hfd : lpNorm (iteratedFDeriv ℝ 1 u) 4 volume ≤ 5 * Real.sqrt (B * (1 + N)) := by
      have he := lpNorm_iteratedFDeriv_le_of_coordinate_bounds 1 hu hc
        (by norm_num : (1 : ℝ≥0∞) ≤ 4) (M := Real.sqrt (B * (1 + N)))
      simp only [pow_one] at he
      refine he fun α hα ↦ ?_
      obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hα
      exact Real.le_sqrt_of_sq_le <| (hfirst u hu hc i).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hur (by norm_num)) hA)
        hhalf (by positivity) hB)
    let S := 5 * Real.sqrt (B * (1 + N))
    let T := Real.sqrt (25 * R)
    have hS : S ^ 2 = 25 * B * (1 + N) := by
      dsimp only [S]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hT : T ^ 2 = 25 * R := Real.sq_sqrt (by positivity)
    let V (i : Fin 2) : ℝ := if i.val = 0 then S else 25 * R
    have he := lpNorm_iteratedFDeriv_comp_le_of_derivative_bounds
      (by decide : 0 < 2) hf hu hc hD hb V (by
      intro i
      fin_cases i
      · simpa [V, S, derivativeExponent_eq_of_pos, show (2 : ℝ≥0∞) * 2 = 4 by norm_num] using hfd
      · simpa [V, derivativeExponent_self, show (5 : ℝ) ^ 2 = 25 by norm_num]
          using hlow u hu hc hur (by decide : 2 ≤ 2))
    refine ⟨he.1, he.2.trans ?_⟩
    have hst : (S + T) ^ 2 ≤ 2 * (25 * B * (1 + N) + 25 * R) := by
      nlinarith [sq_nonneg (S - T)]
    have hmul := mul_le_mul_of_nonneg_left hst (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
    simp only [Fin.sum_univ_two, V]
    norm_num only [Fin.val_zero, Fin.val_one, zero_add, one_add_one_eq_two, ite_true,
      Nat.cast_one, inv_one, Real.rpow_one, Nat.cast_ofNat, Nat.factorial, mul_one,
      one_ne_zero, ite_false]
    rw [← Real.sqrt_eq_rpow]
    change 2 * D * (S + T) ^ 2 ≤ 100 * D * (B + R) * (1 + N)
    nlinarith [mul_nonneg (mul_nonneg hD hR) hN]

/-- A globally Lipschitz smooth reaction with bounded second derivative has an
affine H³ composition bound on H² balls in dimension five. -/
theorem exists_smooth_h2_composition_affine_h3_bound_five {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hl : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^5 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
      ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ)
        (f ∘ u) (hf.comp hu) (hc.comp_left hf0)‖ ≤
        C * (1 + ‖mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) u hu hc‖) := by
  classical
  have hb (y : ℝ) (l : ℕ) (hl0 : 0 < l) (hl2 : l ≤ 2) :
      ‖iteratedFDeriv ℝ l f y‖ ≤ (K : ℝ) + D := by
    interval_cases l
    · rw [norm_iteratedFDeriv_one]
      exact (norm_fderiv_le_of_lipschitz ℝ hl).trans (le_add_of_nonneg_right hD)
    · exact (hsecond y).trans (le_add_of_nonneg_left K.coe_nonneg)
  have hcoord (a : DerivIndex 5 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^5 → ℝ)
        (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
        ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
        ‖(mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ)
          (f ∘ u) (hf.comp hu) (hc.comp_left hf0)).val a‖ ≤
          C * (1 + ‖mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) u hu hc‖) := by
    by_cases ha : a.toList.length = 0
    · refine ⟨K * R, mul_nonneg K.2 hR, fun u hu hc hur ↦ ?_⟩
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [List.length_eq_zero_iff.mp ha, iteratedPartialDeriv,
        domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      have hum : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hc
      have hp (x : ℝ^5) : ‖(f ∘ u) x‖ ≤ (K : ℝ) * ‖u x‖ := by
        simpa only [Function.comp_apply, hf0, dist_zero_right] using hl.dist_le_mul (u x) 0
      have hm := lpNorm_mono_real (hum.norm.const_mul (K : ℝ)) hp
      have he :
          lpNorm (fun x ↦ (K : ℝ) * ‖u x‖) 2 volume = K * lpNorm u 2 volume := by
        change lpNorm ((K : ℝ) • fun x ↦ ‖u x‖) 2 volume = _
        rw [lpNorm_const_smul, coe_nnnorm]
        erw [Real.norm_of_nonneg K.2, lpNorm_norm hum.aestronglyMeasurable]
        rfl
      rw [he] at hm
      exact (hm.trans (mul_le_mul_of_nonneg_left
        ((lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc [] (by simp)).trans hur) K.2)).trans
        (le_mul_of_one_le_right (mul_nonneg K.2 hR) (le_add_of_nonneg_right (norm_nonneg _)))
    · obtain ⟨C, hC, hest⟩ := exists_smooth_h2_composition_derivative_affine_h3_bound_five hf
        (add_nonneg K.2 hD) hb (Nat.pos_of_ne_zero ha) a.toList_length_le hR
      refine ⟨C, hC, fun u hu hc hur ↦ ?_⟩
      obtain ⟨hm, he⟩ := hest u hu hc hur
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      exact (lpNorm_mono_real hm.norm (fun x ↦
        norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
          ((hf.comp hu).of_le (by simp)).contDiffAt)).trans
        ((lpNorm_norm hm.aestronglyMeasurable 2).le.trans he)
  choose C hC hest using hcoord
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ ↦ hC a), fun u hu hc hur ↦ ?_⟩
  rw [Finset.sum_mul]
  exact (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun a _ ↦ hest a u hu hc hur)

end PDE.Hyperbolic.NonlinearWave.Cauchy
