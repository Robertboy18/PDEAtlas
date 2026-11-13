/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothBounds
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Second-order reaction bounds in four spatial dimensions

The embedding H¹ → L⁴ bounds the quadratic product of first derivatives by
the H² norm of the input. A global bound on the second reaction derivative
is a separate hypothesis. Global Lipschitzness bounds the first derivative
and the order-zero composition; it does not bound higher derivatives.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GagliardoNirenberg SobolevSpace.Composition
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- In four dimensions the L⁴ norms of the first spatial derivatives of a
smooth compact input are bounded by a constant times its H² graph norm. -/
theorem exists_lpNorm_firstDerivative_four_le_h2 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : ℝ^4 → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
      (i : Fin 4), lpNorm (iteratedPartialDeriv [i] u) 4 volume ≤
      A * ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ := by
  let : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  have hmem (U : W^{1,2}(ℝ^4)) :
      MemLp (baseRepresentative U) 4 (domainMeasure 4 univ) := by
    have hh := Inequalities.memLp_of_inv_eq (p := 2) (q := 4)
      (by norm_num) (by norm_num : 0 < 4) (by norm_num) (by norm_num) U
    change MemLp (baseRepresentative U) 4 volume at hh
    simpa only [domainMeasure, Measure.restrict_univ] using hh
  obtain ⟨A, hA, hbound⟩ := Inequalities.exists_pos_eLpNorm_bound_of_memLp hmem
  refine ⟨A, hA.le, ?_⟩
  intro u hu hc i
  let U := mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc
  let V : W^{1,2}(ℝ^4) := derivativeWordCLM [i] (by simp) U
  have he : baseRepresentative V =ᵐ[volume] iteratedPartialDeriv [i] u := by
    rw [show baseRepresentative V = _ from baseRepresentative_derivativeWordCLM [i]
      (by simp : [i].length + 1 ≤ 2) U]
    have hh := mkWkpSpaceOnOfContDiff_apply_ae (k := 2) (p := 2) (Ω := univ)
      u hu hc (derivIndexOfList [i] (by simp))
    rw [iteratedPartialDeriv_congr_perm_smooth hu
      (derivIndexOfList_toList_perm [i] (by simp))] at hh
    simpa only [domainMeasure, Measure.restrict_univ] using hh
  have hb := hbound V
  simp only [domainMeasure, Measure.restrict_univ] at hb
  rw [eLpNorm_congr_ae he] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hA.le (norm_nonneg _))] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_left
    (norm_derivativeWordCLM_apply_le [i] (by simp) U) hA.le)

/-- A bound on the first two reaction derivatives controls the positive-order
composition derivatives on every H² ball in dimension four. -/
theorem exists_smooth_h2_composition_derivative_bound {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ y l, 0 < l → l ≤ 2 → ‖iteratedFDeriv ℝ l f y‖ ≤ D) {j : ℕ}
    (hj : 0 < j) (hj2 : j ≤ 2) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^4 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
      MemLp (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ∧
        lpNorm (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ≤ C := by
  obtain ⟨A, hA, hfirst⟩ := exists_lpNorm_firstDerivative_four_le_h2
  let M := (A + 1) * R
  let T (i : Fin j) : ℝ := (4 : ℝ) ^ (i.val + 1) * M
  refine ⟨(j.factorial : ℝ) * D *
    (∑ i : Fin j, T i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ j, by positivity, ?_⟩
  intro u hu hc hur
  have hcoord (α : List (Fin 4)) (hα0 : 0 < α.length) (hαj : α.length ≤ j) :
      lpNorm (iteratedPartialDeriv α u) (derivativeExponent j α.length) volume ≤ M := by
    by_cases heq : α.length = j
    · rw [heq, derivativeExponent_self hj]
      exact ((lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc α
        (hαj.trans hj2)).trans hur).trans (by dsimp [M]; nlinarith)
    · have hj' : j = 2 := by omega
      have hα' : α.length = 1 := by omega
      obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hα'
      have he : derivativeExponent j [i].length = 4 := by
        rw [hj', derivativeExponent_eq_of_pos (by decide) (by simp)]
        norm_num
      rw [he]
      exact ((hfirst u hu hc i).trans (mul_le_mul_of_nonneg_left hur hA)).trans
        (by dsimp [M]; nlinarith)
  apply lpNorm_iteratedFDeriv_comp_le_of_derivative_bounds hj hf hu hc hD
    (fun y l hl hlj ↦ hb y l hl (hlj.trans hj2))
  intro i
  apply lpNorm_iteratedFDeriv_le_of_coordinate_bounds (i.val + 1) hu hc
    ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans (two_le_derivativeExponent (by omega)))
  intro α hα
  simpa only [hα] using hcoord α (by omega) (by omega)

/-- Smooth globally Lipschitz reactions with bounded second derivative map
H² norm balls of smooth compact functions in ℝ⁴ to bounded H² sets. -/
theorem exists_smooth_h2_composition_bound {f : ℝ → ℝ} {K : ℝ≥0} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hl : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^4 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
      ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ)
        (f ∘ u) (hf.comp hu) (hc.comp_left hf0)‖ ≤ C := by
  classical
  have hb (y : ℝ) (l : ℕ) (hl0 : 0 < l) (hl2 : l ≤ 2) :
      ‖iteratedFDeriv ℝ l f y‖ ≤ (K : ℝ) + D := by
    interval_cases l
    · rw [norm_iteratedFDeriv_one]
      exact (norm_fderiv_le_of_lipschitz ℝ hl).trans (le_add_of_nonneg_right hD)
    · exact (hsecond y).trans (le_add_of_nonneg_left K.coe_nonneg)
  have hcoord (a : DerivIndex 4 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^4 → ℝ)
        (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
        ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
        ‖(mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ)
          (f ∘ u) (hf.comp hu) (hc.comp_left hf0)).val a‖ ≤ C := by
    by_cases ha : a.toList.length = 0
    · refine ⟨K * R, mul_nonneg K.2 hR, fun u hu hc hur ↦ ?_⟩
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [List.length_eq_zero_iff.mp ha, iteratedPartialDeriv,
        domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      have hum : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hc
      have hp (x : ℝ^4) : ‖(f ∘ u) x‖ ≤ (K : ℝ) * ‖u x‖ := by
        simpa only [Function.comp_apply, hf0, dist_zero_right] using hl.dist_le_mul (u x) 0
      have hm := lpNorm_mono_real (hum.norm.const_mul (K : ℝ)) hp
      have he :
          lpNorm (fun x ↦ (K : ℝ) * ‖u x‖) 2 volume = K * lpNorm u 2 volume := by
        change lpNorm ((K : ℝ) • fun x ↦ ‖u x‖) 2 volume = _
        rw [lpNorm_const_smul, coe_nnnorm]
        erw [Real.norm_of_nonneg K.2, lpNorm_norm hum.aestronglyMeasurable]
        rfl
      rw [he] at hm
      exact hm.trans (mul_le_mul_of_nonneg_left
        ((lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc [] (by simp)).trans hur) K.2)
    · obtain ⟨C, hC, hest⟩ := exists_smooth_h2_composition_derivative_bound hf
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
  exact (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun a _ ↦ hest a u hu hc hur)

end PDE.Hyperbolic.NonlinearWave.Cauchy
