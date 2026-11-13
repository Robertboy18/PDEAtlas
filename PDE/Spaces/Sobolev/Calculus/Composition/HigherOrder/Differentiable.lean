/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.Derivative
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteLipschitz

/-!
# Differentiating Sobolev composition

Normalize the increment and compare the averaged derivative at two triples.
Local Lipschitz continuity bounds their difference by the increment norm.
Restoring the normalization gives a quadratic remainder, hence the derivative
in the Sobolev norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Topology

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

variable [DecidableEq ι]

/-- The derivative is the averaged derivative reaction with coincident endpoints. -/
theorem finiteCompositionDerivative_eq_differenceReaction
    (hk : (n : ℝ) < 2 * (k : ℝ)) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (U H : ι → W^{k,2}(ℝ^n)) :
    finiteCompositionDerivative hk hf U H =
      finiteComposition hk (contDiff_differenceReaction hf)
        (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0)
        (fun ji ↦ ![U, U, H] ji.1 ji.2) := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (finiteCompositionDerivative hk hf U H) =ᵐ[domainMeasure n univ]
    baseRepresentative (finiteComposition hk (contDiff_differenceReaction hf)
      (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0)
      (fun ji ↦ ![U, U, H] ji.1 ji.2))
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [finiteCompositionDerivative_ae hk hf U H,
    finiteComposition_ae hk (contDiff_differenceReaction hf)
      (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0)
      (fun ji ↦ ![U, U, H] ji.1 ji.2)] with x hd ha
  rw [hd, ha]
  exact (averagedDerivative_self f _ _).symm

omit [DecidableEq ι] in
private theorem norm_triple_family_le {E : Type*} [NormedAddCommGroup E]
    (U V W : ι → E) {R : ℝ} (hR : 0 ≤ R)
    (hU : ‖U‖ ≤ R) (hV : ‖V‖ ≤ R) (hW : ‖W‖ ≤ R) :
    ‖(fun ji : Fin 3 × ι ↦ ![U, V, W] ji.1 ji.2)‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  rintro ⟨j, i⟩
  fin_cases j
  · exact (norm_le_pi_norm U i).trans hU
  · exact (norm_le_pi_norm V i).trans hV
  · exact (norm_le_pi_norm W i).trans hW

omit [DecidableEq ι] in
private theorem dist_triple_family_le {E : Type*} [NormedAddCommGroup E]
    (U H W : ι → E) :
    dist (fun ji : Fin 3 × ι ↦ ![U + H, U, W] ji.1 ji.2)
      (fun ji : Fin 3 × ι ↦ ![U, U, W] ji.1 ji.2) ≤ ‖H‖ := by
  apply (dist_pi_le_iff (norm_nonneg H)).mpr
  rintro ⟨j, i⟩
  fin_cases j
  · change dist (U i + H i) (U i) ≤ ‖H‖
    simpa only [dist_eq_norm, add_sub_cancel_left] using norm_le_pi_norm H i
  · change dist (U i) (U i) ≤ ‖H‖
    simpa only [dist_self] using norm_nonneg H
  · change dist (W i) (W i) ≤ ‖H‖
    simpa only [dist_self] using norm_nonneg H

omit [DecidableEq ι] in
private theorem normalized_triples_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U H : ι → E) (hH : ‖H‖ ≤ 1) (hzero : H ≠ 0) :
    let W := ‖H‖⁻¹ • H
    let R := max (‖U‖ + 1) 1
    (fun ji : Fin 3 × ι ↦ ![U + H, U, W] ji.1 ji.2) ∈ Metric.closedBall 0 R ∧
      (fun ji : Fin 3 × ι ↦ ![U, U, W] ji.1 ji.2) ∈ Metric.closedBall 0 R := by
  dsimp only
  have hc : 0 < ‖H‖ := norm_pos_iff.mpr hzero
  have hW : ‖‖H‖⁻¹ • H‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hc.ne']
  have hR : 0 ≤ max (‖U‖ + 1) 1 := zero_le_one.trans (le_max_right _ _)
  have hU : ‖U‖ ≤ max (‖U‖ + 1) 1 :=
    (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)
  have hW' : ‖‖H‖⁻¹ • H‖ ≤ max (‖U‖ + 1) 1 := hW.le.trans (le_max_right _ _)
  simp only [Metric.mem_closedBall, dist_zero_right]
  refine ⟨norm_triple_family_le (E := E) (U + H) U (‖H‖⁻¹ • H) hR ?_ hU hW',
    norm_triple_family_le U U (‖H‖⁻¹ • H) hR hU hU hW'⟩
  exact ((norm_add_le U H).trans (add_le_add le_rfl hH)).trans (le_max_left _ _)

private theorem finiteCompositionDerivative_eq_smul_differenceReaction
    (hk : (n : ℝ) < 2 * (k : ℝ)) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (U H : ι → W^{k,2}(ℝ^n))
    {c : ℝ} (hc : c ≠ 0) :
    finiteCompositionDerivative hk hf U H =
      c • finiteComposition hk (contDiff_differenceReaction hf)
        (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0)
        (fun ji ↦ ![U, U, c⁻¹ • H] ji.1 ji.2) := by
  rw [← finiteCompositionDerivative_eq_differenceReaction, map_smul,
    smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The remainder after the Sobolev derivative is quadratic on a unit neighborhood. -/
theorem exists_finiteComposition_remainder_bound
    (hk : (n : ℝ) < 2 * (k : ℝ)) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U : ι → W^{k,2}(ℝ^n)) :
    ∃ K : ℝ, ∀ H : ι → W^{k,2}(ℝ^n), ‖H‖ ≤ 1 →
      ‖finiteComposition hk hf hf0 (U + H) - finiteComposition hk hf hf0 U -
        finiteCompositionDerivative hk hf U H‖ ≤ K * ‖H‖ ^ 2 := by
  let R := max (‖U‖ + 1) 1
  let G := finiteComposition hk (contDiff_differenceReaction hf)
    (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0)
  obtain ⟨K, hK⟩ := exists_lipschitzOn_finiteComposition hk
    (contDiff_differenceReaction hf)
    (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0) R
  refine ⟨K, fun H hH ↦ ?_⟩
  by_cases hzero : H = 0
  · simp [hzero]
  have hc : 0 < ‖H‖ := norm_pos_iff.mpr hzero
  let W := ‖H‖⁻¹ • H
  let A : Fin 3 × ι → W^{k,2}(ℝ^n) := fun ji ↦ ![U + H, U, W] ji.1 ji.2
  let B : Fin 3 × ι → W^{k,2}(ℝ^n) := fun ji ↦ ![U, U, W] ji.1 ji.2
  obtain ⟨hA, hB⟩ := normalized_triples_mem (E := W^{k,2}(ℝ^n)) U H hH hzero
  have hdist : dist A B ≤ ‖H‖ := dist_triple_family_le (E := W^{k,2}(ℝ^n)) U H W
  have hdiff : finiteComposition hk hf hf0 (U + H) - finiteComposition hk hf hf0 U =
      ‖H‖ • G A := by
    simpa only [add_sub_cancel_left] using
      finiteComposition_sub_eq_smul hk hf hf0 (U + H) U hc.ne'
  have hderiv : finiteCompositionDerivative hk hf U H = ‖H‖ • G B :=
    finiteCompositionDerivative_eq_smul_differenceReaction hk hf U H hc.ne'
  rw [hdiff, hderiv, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_norm]
  have hg : ‖G A - G B‖ ≤ (K : ℝ) * ‖H‖ := by
    simpa only [dist_eq_norm] using (hK.dist_le_mul A hA B hB).trans
      (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)
  exact (mul_le_mul_of_nonneg_left hg hc.le).trans_eq (by ring)

/-- A smooth reaction fixing zero is differentiable on the Sobolev algebra. -/
theorem hasFDerivAt_finiteComposition
    (hk : (n : ℝ) < 2 * (k : ℝ)) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U : ι → W^{k,2}(ℝ^n)) :
    HasFDerivAt (finiteComposition hk hf hf0) (finiteCompositionDerivative hk hf U) U := by
  obtain ⟨K, hK⟩ := exists_finiteComposition_remainder_bound hk hf hf0 U
  apply (hasFDerivAt_iff_isLittleO_nhds_zero
    (𝕜 := ℝ) (E := ι → W^{k,2}(ℝ^n)) (F := W^{k,2}(ℝ^n))
    (f := finiteComposition hk hf hf0) (f' := finiteCompositionDerivative hk hf U) (x := U)).2
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun H : ι → W^{k,2}(ℝ^n) ↦ ‖H‖ ^ 2)
    (Asymptotics.IsBigO.of_bound K ?_) (Asymptotics.isLittleO_norm_pow_id (by decide))
  filter_upwards [Metric.closedBall_mem_nhds (0 : ι → W^{k,2}(ℝ^n)) zero_lt_one] with H hH
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖H‖ : ℝ))] using
    hK H (by simpa only [Metric.mem_closedBall, dist_zero_right] using hH)

end SobolevSpace.Composition
