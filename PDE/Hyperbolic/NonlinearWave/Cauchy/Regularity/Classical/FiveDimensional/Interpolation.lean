/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding

/-!
# Interpolation for the quadratic chain term in dimension five

Sobolev embedding of first derivatives into L^(10/3) and L^10, followed
by Hölder, bounds their squared L⁴ norms by H²^(3/2) H³^(1/2).
This is sublinear in H³ on every H² ball.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev Topology

namespace SobolevSpace.Inequalities

private theorem lpNorm_l4_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (hlo : MemLp w (10 / 3) μ) (hhi : MemLp w 10 μ) :
    lpNorm w 4 μ ^ 2 ≤ lpNorm w (10 / 3) μ ^ (3 / 2 : ℝ) * lpNorm w 10 μ ^ (1 / 2 : ℝ) := by
  let : ENNReal.HolderTriple (20 / 9) 20 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  have h := eLpNorm_smul_le_mul_eLpNorm_of_pos (φ := fun x ↦ ‖w x‖ ^ (3 / 2 : ℝ))
    (f := fun x ↦ ‖w x‖ ^ (1 / 2 : ℝ)) (μ := μ)
    (p := 20 / 9) (q := 20) (r := 2) (by norm_num)
  have heq : (fun x ↦ ‖w x‖ ^ (3 / 2 : ℝ)) •
      (fun x ↦ ‖w x‖ ^ (1 / 2 : ℝ)) = fun x ↦ ‖w x‖ ^ (2 : ℝ) := by
    ext x
    change ‖w x‖ ^ (3 / 2 : ℝ) * ‖w x‖ ^ (1 / 2 : ℝ) = _
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
    norm_num
  rw [heq, eLpNorm_norm_rpow w hw (by norm_num),
    eLpNorm_norm_rpow w hw (by norm_num), eLpNorm_norm_rpow w hw (by norm_num)] at h
  have hloexp : (20 / 9 : ℝ≥0∞) * ENNReal.ofReal (3 / 2) = 10 / 3 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  have hhiexp : (20 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 10 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  norm_num only [hloexp, hhiexp, ENNReal.ofReal_ofNat, ENNReal.rpow_ofNat,
    show (2 : ℝ≥0∞) * 2 = 4 by norm_num] at h
  have hh := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_pow,
    toReal_eLpNorm] using hh

private theorem exists_firstDerivative_lpNorm_bound {r : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hmem : ∀ U : W^{r,2}(ℝ^5), MemLp (baseRepresentative U) q (domainMeasure 5 univ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : ℝ^5 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) (i : Fin 5),
      MemLp (iteratedPartialDeriv [i] u) q volume ∧
      lpNorm (iteratedPartialDeriv [i] u) q volume ≤
        A * ‖mkWkpSpaceOnOfContDiff (k := r + 1) (p := 2) (Ω := univ) u hu hc‖ := by
  obtain ⟨A, hA, hbound⟩ := Inequalities.exists_pos_eLpNorm_bound_of_memLp hmem
  refine ⟨A, hA.le, fun u hu hc i ↦ ?_⟩
  let U := mkWkpSpaceOnOfContDiff (k := r + 1) (p := 2) (Ω := univ) u hu hc
  let V : W^{r,2}(ℝ^5) := derivativeWordCLM [i] (by simp; omega) U
  have he : baseRepresentative V =ᵐ[volume] iteratedPartialDeriv [i] u := by
    rw [show baseRepresentative V = _ from baseRepresentative_derivativeWordCLM [i]
      (by simp; omega : [i].length + r ≤ r + 1) U]
    have hh := mkWkpSpaceOnOfContDiff_apply_ae (k := r + 1) (p := 2) (Ω := univ)
      u hu hc (derivIndexOfList [i] (by simp))
    rw [iteratedPartialDeriv_congr_perm_smooth hu
      (derivIndexOfList_toList_perm [i] (by simp))] at hh
    simpa only [domainMeasure, Measure.restrict_univ] using hh
  have hm := hmem V
  simp only [domainMeasure, Measure.restrict_univ] at hm
  refine ⟨hm.ae_eq he, ?_⟩
  have hb := hbound V
  simp only [domainMeasure, Measure.restrict_univ] at hb
  rw [eLpNorm_congr_ae he] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hA.le (norm_nonneg _))] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_left
    (norm_derivativeWordCLM_apply_le [i] (by simp; omega) U) hA.le)

/-- The five-dimensional interpolation estimate for each first derivative.
The H³ exponent is one half after squaring the L⁴ norm. -/
theorem exists_lpNorm_firstDerivative_l4_sq_le_h2_h3_five :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^5 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) (i : Fin 5),
      lpNorm (iteratedPartialDeriv [i] u) 4 volume ^ 2 ≤
        C * ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ ^ (3 / 2 : ℝ) *
          ‖mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) u hu hc‖ ^ (1 / 2 : ℝ) := by
  let : Fact ((1 : ℝ≥0∞) ≤ 10 / 3) := ⟨by
    exact (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr (by norm_num)⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 10) := ⟨by norm_num⟩
  have hlo (U : W^{1,2}(ℝ^5)) :
      MemLp (baseRepresentative U) (10 / 3) (domainMeasure 5 univ) := by
    have hh := Inequalities.memLp_of_inv_eq (p := 2) (q := 10 / 3)
      (by norm_num) (by norm_num : 0 < 5) (by norm_num) (by norm_num) U
    change MemLp (baseRepresentative U) ((10 / 3 : ℝ≥0) : ℝ≥0∞) volume at hh
    simpa only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
      domainMeasure, Measure.restrict_univ] using hh
  have hhi (U : W^{2,2}(ℝ^5)) :
      MemLp (baseRepresentative U) 10 (domainMeasure 5 univ) := by
    have hh := Inequalities.memLp_of_inv_eq (p := 2) (q := 10)
      (by norm_num) (by norm_num : 0 < 5) (by norm_num) (by norm_num) U
    change MemLp (baseRepresentative U) 10 volume at hh
    simpa only [domainMeasure, Measure.restrict_univ] using hh
  obtain ⟨A, hA, ha⟩ := exists_firstDerivative_lpNorm_bound hlo
  obtain ⟨B, hB, hb⟩ := exists_firstDerivative_lpNorm_bound hhi
  refine ⟨A ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ), by positivity, fun u hu hc i ↦ ?_⟩
  obtain ⟨hma, hea⟩ := ha u hu hc i
  obtain ⟨hmb, heb⟩ := hb u hu hc i
  calc
    _ ≤ _ := lpNorm_l4_sq_le hma.aestronglyMeasurable hma hmb
    _ ≤ (A * ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖) ^ (3 / 2 : ℝ) *
        (B * ‖mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) u hu hc‖) ^ (1 / 2 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow lpNorm_nonneg hea (by norm_num))
        (Real.rpow_le_rpow lpNorm_nonneg heb (by norm_num))
        (Real.rpow_nonneg lpNorm_nonneg _) (by positivity)
    _ = _ := by rw [Real.mul_rpow hA (norm_nonneg _), Real.mul_rpow hB (norm_nonneg _)]; ring

end SobolevSpace.Inequalities
