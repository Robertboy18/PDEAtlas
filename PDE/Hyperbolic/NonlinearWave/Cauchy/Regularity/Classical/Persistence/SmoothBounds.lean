/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Interpolation
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Tame composition bounds for smooth compact inputs

A fixed bound on the values of the input controls the scalar reaction
derivatives. Scaled interpolation makes the resulting Sobolev composition
bound affine in the input graph norm, with no bound on that norm as an input.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GagliardoNirenberg SobolevSpace.Composition
open scoped ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- A bounded value range gives a composition derivative bound linear in
one plus the full input Sobolev norm. -/
theorem exists_tame_smooth_composition_derivative_bound {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      (∀ x, ‖u x‖ ≤ B) →
      MemLp (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ∧
        lpNorm (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ≤
          C * (1 + ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖) := by
  obtain ⟨A, hA, hest⟩ := exists_constant_scaled_derivative n j
  obtain ⟨D, hD, hreact⟩ := exists_iteratedFDeriv_bound_on_Icc hf j B
  let M := A * (B + 1)
  let T (i : Fin j) : ℝ := (n : ℝ) ^ (i.val + 1) * M
  let C := (j.factorial : ℝ) * D * (∑ i : Fin j, T i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ j
  have hM : 0 ≤ M := mul_nonneg (by linarith) (by linarith)
  have hT (i : Fin j) : 0 ≤ T i := mul_nonneg (by positivity) hM
  refine ⟨C, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD)
    (pow_nonneg (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hT i) _) _), ?_⟩
  intro u hu hc hub
  let U := mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc
  let r : ℝ := (1 + ‖U‖) ^ ((j : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hrj : r ^ j = 1 + ‖U‖ :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hbase : lpNorm u ∞ volume ≤ B := by
    have he : eLpNorm u ∞ volume ≤ ENNReal.ofReal B := by
      rw [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound (.of_forall hub)
    simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have htop : maxDerivativeLpNorm j j u ≤ ‖U‖ := by
    apply Finset.sup'_le
    intro α _
    rw [derivativeExponent_self hj]
    exact lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc (List.ofFn α)
      (by simpa using hjk)
  have hratio : maxDerivativeLpNorm j j u / r ^ j ≤ 1 := by
    rw [hrj]
    exact (div_le_one (by positivity)).mpr (htop.trans (by linarith))
  have hcoord (α : List (Fin n)) (hα : α.length ≤ j) :
      lpNorm (iteratedPartialDeriv α u) (derivativeExponent j α.length) volume ≤
        M * r ^ α.length := by
    exact (hest u (hu.of_le (by simp)) hc r hr α hα).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hbase hratio) (by linarith)) (pow_nonneg hr.le _))
  have htensor (i : Fin j) :
      lpNorm (iteratedFDeriv ℝ (i.val + 1) u) (derivativeExponent j (i.val + 1)) volume ≤
        T i * r ^ (i.val + 1) := by
    have he := lpNorm_iteratedFDeriv_le_of_coordinate_bounds (i.val + 1) hu hc
      (p := derivativeExponent j (i.val + 1))
      ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans (two_le_derivativeExponent (by omega)))
      (fun α hα ↦ by simpa only [hα] using hcoord α (by omega))
    simpa only [T, mul_assoc] using he
  obtain ⟨hm, hb⟩ := memLp_and_lpNorm_iteratedFDeriv_comp_le hj hf hu hc hD (fun x l hl ↦
      hreact (u x) (abs_le.mp (by simpa only [Real.norm_eq_abs] using hub x)) l hl)
    (fun i ↦ T i * r ^ (i.val + 1)) htensor
  refine ⟨hm, ?_⟩
  rw [sum_root_mul_pow T hT hr.le, ← mul_assoc, hrj] at hb
  exact hb

/-- Smooth compact inputs with bounded amplitude have composition graph norm
at most a constant times one plus their input graph norm. -/
theorem exists_tame_smooth_composition_bound {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      (∀ x, ‖u x‖ ≤ B) →
      ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
        (f ∘ u) (hf.comp hu) (hc.comp_left hf0)‖ ≤
          C * (1 + ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖) := by
  classical
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨K, hK⟩ := hf1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-B) B) isCompact_Icc
  have hcoord (a : DerivIndex n k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
        (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u), (∀ x, ‖u x‖ ≤ B) →
        ‖(mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
          (f ∘ u) (hf.comp hu) (hc.comp_left hf0)).val a‖ ≤
            C * (1 + ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖) := by
    by_cases ha : a.toList.length = 0
    · refine ⟨K, K.2, ?_⟩
      intro u hu hc hub
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [List.length_eq_zero_iff.mp ha, iteratedPartialDeriv,
        domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      have hum : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hc
      have hp : ∀ x, ‖(f ∘ u) x‖ ≤ (K : ℝ) * ‖u x‖ := by
        intro x
        have hx : u x ∈ Icc (-B) B :=
          abs_le.mp (by simpa only [Real.norm_eq_abs] using hub x)
        simpa only [Function.comp_apply, hf0, dist_zero_right] using
          hK.dist_le_mul (u x) hx 0 ⟨neg_nonpos.mpr hB, hB⟩
      have hm := lpNorm_mono_real (hum.norm.const_mul (K : ℝ)) hp
      have he :
          lpNorm (fun x ↦ (K : ℝ) * ‖u x‖) 2 volume = K * lpNorm u 2 volume := by
        change lpNorm ((K : ℝ) • fun x ↦ ‖u x‖) 2 volume = _
        rw [lpNorm_const_smul, coe_nnnorm]
        erw [Real.norm_of_nonneg K.2, lpNorm_norm hum.aestronglyMeasurable]
        rfl
      rw [he] at hm
      exact hm.trans (mul_le_mul_of_nonneg_left
        ((lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc [] (by simp)).trans
          (by linarith)) K.2)
    · obtain ⟨C, hC, hest⟩ := exists_tame_smooth_composition_derivative_bound (n := n)
        hf (Nat.pos_of_ne_zero ha) a.toList_length_le hB
      refine ⟨C, hC, ?_⟩
      intro u hu hc hub
      obtain ⟨hm, hb⟩ := hest u hu hc hub
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      exact (lpNorm_mono_real hm.norm (fun x ↦
        norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
          ((hf.comp hu).of_le (by simp)).contDiffAt)).trans
        ((lpNorm_norm hm.aestronglyMeasurable 2).le.trans hb)
  choose C hC hest using hcoord
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ ↦ hC a), ?_⟩
  intro u hu hc hub
  rw [Finset.sum_mul]
  exact (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun a _ ↦ hest a u hu hc hub)

end PDE.Hyperbolic.NonlinearWave.Cauchy
