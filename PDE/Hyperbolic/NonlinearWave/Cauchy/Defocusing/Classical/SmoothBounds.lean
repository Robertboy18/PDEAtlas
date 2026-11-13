/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Cubic
public import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
import PDE.Analysis.Normed.PiLp.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The cubic H¹ estimate in three dimensions

H¹ embeds in L⁶, also for each first derivative of an H² input. Hölder
therefore bounds the H¹ norm of the cube by the square of the H¹ norm
times the H² norm. This estimate is linear in the higher norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

private theorem lpNorm_mul_le {f g : ℝ^3 → ℝ} {q r s : ℝ≥0∞} [ENNReal.HolderTriple q r s]
    (hf : MemLp f q volume) (hg : MemLp g r volume) :
    lpNorm (fun x ↦ f x * g x) s volume ≤ lpNorm f q volume * lpNorm g r volume := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := q) (q := r) (r := s)
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm, Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h

private theorem lpNorm_sq_mul_le_six {u v : ℝ^3 → ℝ} (hu : MemLp u 6 volume)
    (hv : MemLp v 6 volume) :
    lpNorm (fun x ↦ u x ^ 2 * v x) 2 volume ≤ lpNorm u 6 volume ^ 2 * lpNorm v 6 volume := by
  let : ENNReal.HolderTriple 6 6 3 := ⟨by
    change ((6 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((6 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((3 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0), ← ENNReal.coe_add, ENNReal.coe_inj]
    norm_num⟩
  let : ENNReal.HolderTriple 3 6 2 := ⟨by
    change ((3 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((6 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add, ENNReal.coe_inj]
    norm_num⟩
  have h := (lpNorm_mul_le (s := 2) (hu.mul (r := 3) hu) hv).trans
    (mul_le_mul_of_nonneg_right (lpNorm_mul_le (s := 3) hu hu) lpNorm_nonneg)
  simpa only [sq, Pi.mul_apply, mul_assoc] using h

/-- A single H¹ → L⁶ constant controls a smooth input and the L⁶ norms of its
first derivatives using, respectively, its H¹ and H² graph norms. -/
theorem exists_smooth_six_bounds :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : ℝ^3 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      lpNorm u 6 volume ≤
        A * ‖mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ) u hu hc‖ ∧
      ∀ i : Fin 3, lpNorm (iteratedPartialDeriv [i] u) 6 volume ≤
        A * ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ := by
  let : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
  have hm (U : H¹(ℝ^3)) : MemLp (baseRepresentative U) 6 (domainMeasure 3 univ) := by
    convert Power.memLp_twice_power (p := 3) (by norm_num) le_rfl U using 1
    norm_num
  obtain ⟨A, hA, hb⟩ := Inequalities.exists_pos_eLpNorm_bound_of_memLp hm
  have hreal (U : H¹(ℝ^3)) {v : ℝ^3 → ℝ} (he : baseRepresentative U =ᵐ[volume] v) :
      lpNorm v 6 volume ≤ A * ‖U‖ := by
    have h := hb U
    simp only [domainMeasure, Measure.restrict_univ] at h
    rw [eLpNorm_congr_ae he] at h
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (mul_nonneg hA.le (norm_nonneg _))] at ht
  refine ⟨A, hA.le, ?_⟩
  intro u hu hc
  constructor
  · apply hreal (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ) u hu hc)
    simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ,
      baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := 2) (Ω := univ) u hu hc (baseIndex 3 1)
  · intro i
    let U := mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc
    let V : H¹(ℝ^3) := derivativeWordCLM [i] (by simp) U
    have he : baseRepresentative V =ᵐ[volume] iteratedPartialDeriv [i] u := by
      rw [show baseRepresentative V = _ from baseRepresentative_derivativeWordCLM [i]
        (by simp : [i].length + 1 ≤ 2) U]
      have hh := mkWkpSpaceOnOfContDiff_apply_ae (k := 2) (p := 2) (Ω := univ)
        u hu hc (derivIndexOfList [i] (by simp))
      rw [iteratedPartialDeriv_congr_perm_smooth hu
        (derivIndexOfList_toList_perm [i] (by simp))] at hh
      simpa only [domainMeasure, Measure.restrict_univ] using hh
    exact (hreal V he).trans (mul_le_mul_of_nonneg_left
      (norm_derivativeWordCLM_apply_le [i] (by simp) U) hA.le)

/-- On ℝ³ the H¹ norm of a smooth compact cube grows linearly in the
H² norm, with coefficient controlled by the square of the H¹ norm. -/
theorem exists_smooth_cubic_h1_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^3 → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      ‖mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ)
        (fun x ↦ u x ^ 3) (hu.pow 3) (hc.comp_left (g := fun s : ℝ ↦ s ^ 3) (by simp))‖ ≤
      C * ‖mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ) u hu hc‖ ^ 2 *
        ‖mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc‖ := by
  classical
  obtain ⟨A, hA, hest⟩ := exists_smooth_six_bounds
  refine ⟨(Fintype.card (DerivIndex 3 1) : ℝ) * (3 * A ^ 3), by positivity, ?_⟩
  intro u hu hc
  let U₁ := mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ) u hu hc
  let U₂ := mkWkpSpaceOnOfContDiff (k := 2) (p := 2) (Ω := univ) u hu hc
  have h12 : ‖U₁‖ ≤ ‖U₂‖ := by
    have h := norm_lowerOrderCLM_apply_le (by decide : 1 ≤ 2) U₂
    rwa [lowerOrderCLM_mkWkpSpaceOnOfContDiff] at h
  have hm : MemLp u 6 volume := hu.continuous.memLp_of_hasCompactSupport hc
  have htriple {v : ℝ^3 → ℝ} (hv : MemLp v 6 volume) (hb : lpNorm v 6 volume ≤ A * ‖U₂‖) :
      lpNorm (fun x ↦ u x ^ 2 * v x) 2 volume ≤ A ^ 3 * ‖U₁‖ ^ 2 * ‖U₂‖ := by
    calc
      _ ≤ lpNorm u 6 volume ^ 2 * lpNorm v 6 volume := lpNorm_sq_mul_le_six hm hv
      _ ≤ (A * ‖U₁‖) ^ 2 * (A * ‖U₂‖) :=
        mul_le_mul (pow_le_pow_left₀ lpNorm_nonneg (hest u hu hc).1 2) hb
          lpNorm_nonneg (by positivity)
      _ = _ := by ring
  have hcoord (a : DerivIndex 3 1) : ‖(mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ)
        (fun x ↦ u x ^ 3) (hu.pow 3) (hc.comp_left (g := fun s : ℝ ↦ s ^ 3) (by simp))).val a‖ ≤
        3 * A ^ 3 * ‖U₁‖ ^ 2 * ‖U₂‖ := by
    rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
    simp only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
    by_cases ha : a.toList.length = 0
    · rw [List.length_eq_zero_iff.mp ha]
      change lpNorm (fun x ↦ u x ^ 3) 2 volume ≤ _
      have he := htriple hm ((hest u hu hc).1.trans (mul_le_mul_of_nonneg_left h12 hA))
      have hcub : (fun x ↦ u x ^ 3) = fun x ↦ u x ^ 2 * u x := by
        funext x
        ring
      rw [hcub]
      exact he.trans (by
        have hp : 0 ≤ A ^ 3 * ‖U₁‖ ^ 2 * ‖U₂‖ := by positivity
        nlinarith)
    · obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp
        (show a.toList.length = 1 by have ht := a.toList_length_le; omega)
      rw [hi]
      have hd (x : ℝ^3) : iteratedPartialDeriv [i] (fun y ↦ u y ^ 3) x =
            3 * (u x ^ 2 * iteratedPartialDeriv [i] u x) := by
        change ∂[i] (fun y ↦ u y ^ 3) x = 3 * (u x ^ 2 * ∂[i] u x)
        have he : (fun y ↦ u y ^ 3) = fun y ↦ u y ^ 2 * u y := by
          funext y
          ring
        rw [he, partialDeriv_mul (i := i) (f := fun y ↦ u y ^ 2)
          (hu.differentiable (by simp) x |>.pow 2)
          (hu.differentiable (by simp) x),
          partialDeriv_sq i (hu.differentiable (by simp) x)]
        ring
      have hdm : MemLp (iteratedPartialDeriv [i] u) 6 volume :=
        (contDiff_top_iteratedPartialDeriv hu [i]).continuous.memLp_of_hasCompactSupport
          (hasCompactSupport_iteratedPartialDeriv hc [i])
      simp_rw [hd]
      change lpNorm ((3 : ℝ) • fun x ↦ u x ^ 2 * iteratedPartialDeriv [i] u x) 2 volume ≤ _
      rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact (mul_le_mul_of_nonneg_left (htriple hdm ((hest u hu hc).2 i))
        (by norm_num)).trans_eq (by ring)
  calc
    _ ≤ ∑ a : DerivIndex 3 1, 3 * A ^ 3 * ‖U₁‖ ^ 2 * ‖U₂‖ :=
      (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun a _ ↦ hcoord a)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
