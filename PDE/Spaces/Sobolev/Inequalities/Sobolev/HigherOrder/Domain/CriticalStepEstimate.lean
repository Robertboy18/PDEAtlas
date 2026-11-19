/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.IterationEstimate
import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.OneDimensionalCritical

/-!
# Quantitative critical first-order estimates on domains

For `n ≥ 2` and finite `q > n`, lower the source exponent to `s = nq/(n+q)` and
apply the quantitative first-order GNS estimate, since `s* = q`. For `q ≤ n`,
finite-volume exponent restriction suffices. In dimension one the bounded
representative theorem supplies the estimate. The endpoint inclusion `W^{1,n} → L∞`
fails in dimensions greater than one and is not used.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace
open scoped ENNReal Sobolev

variable {n : ℕ} {q : NNReal} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The critical finite-exponent constant, expressed using finite-volume restriction
and operational first-order extension estimates. -/
def criticalFirstOrderConstant (q : NNReal) : ℝ :=
  if hn : n = 1 then
    ((domainMeasure n Ω) Set.univ ^ (q : ℝ)⁻¹).toReal *
      ‖Extension.C1.extensionCLM (n := n) (p := (1 : ℝ≥0∞)) (Ω := Ω)‖
  else if hnq : (n : ℝ) < q then
    have hn2 : 2 ≤ n := by have := Fact.out (p := 0 < n); omega
    have : Fact (1 ≤ (pStarPreimage n q : ℝ≥0∞)) :=
      ⟨by exact_mod_cast one_le_pStarPreimage hn2 hnq⟩
    firstOrderDomainConstant (p := pStarPreimage n q) (Ω := Ω) *
      finiteMeasureExponentRestrictionNormBound n 1 (n : ℝ≥0∞)
        (pStarPreimage n q : ℝ≥0∞) Ω
  else
    finiteMeasureExponentRestrictionNormBound n 1 (n : ℝ≥0∞) (q : ℝ≥0∞) Ω

/-- Every factor in the critical constant is nonnegative. -/
theorem criticalFirstOrderConstant_nonneg :
    0 ≤ criticalFirstOrderConstant (Ω := Ω) q := by
  unfold criticalFirstOrderConstant
  split
  · positivity
  · split
    · rename_i hn hnq
      have hn2 : 2 ≤ n := by have := Fact.out (p := 0 < n); omega
      have : Fact (1 ≤ (pStarPreimage n q : ℝ≥0∞)) :=
        ⟨by exact_mod_cast one_le_pStarPreimage hn2 hnq⟩
      exact mul_nonneg firstOrderDomainConstant_nonneg
        finiteMeasureExponentRestrictionNormBound_nonneg
    · exact finiteMeasureExponentRestrictionNormBound_nonneg

/-- Quantitative critical first-order domain estimate for every finite `q ≥ 1`.
Positive dimension and an operational bounded C¹ extension atlas are assumed. -/
theorem eLpNorm_critical_firstOrder_le
    [Fact (1 ≤ (n : ℝ≥0∞))] (hq : 1 ≤ q)
    (U : W^{1,(n : ℝ≥0∞)}(Ω)) :
    eLpNorm (baseRepresentative U) (q : ℝ≥0∞) (domainMeasure n Ω) ≤
      ENNReal.ofReal (criticalFirstOrderConstant (Ω := Ω) q * ‖U‖) := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hq)
  by_cases hn : n = 1
  · subst n
    let V := WkpSpaceOn.congrExponent (Nat.cast_one (R := ℝ≥0∞)) 1 1 Ω U
    have hVU : baseRepresentative V = baseRepresentative U :=
      WkpSpaceOn.coordinate_congrExponent (Nat.cast_one (R := ℝ≥0∞)) U (baseIndex 1 1)
    have hnorm : ‖V‖ = ‖U‖ := WkpSpaceOn.norm_congrExponent _ U
    let E := Extension.C1.extensionCLM (n := 1) (p := (1 : ℝ≥0∞)) (Ω := Ω)
    let F := CriticalOneDimensional.criticalEmbedding (E V)
    have hFU : (fun x ↦ F x) =ᵐ[domainMeasure 1 Ω] baseRepresentative U :=
      (CriticalOneDimensional.criticalEmbeddingOn_ae V).trans (Filter.EventuallyEq.of_eq hVU)
    have hbound : ∀ᵐ x ∂domainMeasure 1 Ω, ‖baseRepresentative U x‖ ≤ ‖E‖ * ‖U‖ := by
      filter_upwards [hFU] with x hx
      rw [← hx]
      exact (F.norm_coe_le_norm x).trans
        ((CriticalOneDimensional.norm_boundedContinuousRepresentative_le (E V)).trans
          ((E.le_opNorm V).trans_eq (by rw [hnorm])))
    have h := eLpNorm_le_of_ae_bound
      (Lp.aestronglyMeasurable (U.val (baseIndex 1 1))) hbound (p := (q : ℝ≥0∞))
    have hvol : (domainMeasure 1 Ω) Set.univ ^ (q : ℝ)⁻¹ ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
    calc
      eLpNorm (baseRepresentative U) _ _ ≤
          (domainMeasure 1 Ω) Set.univ ^ (q : ℝ)⁻¹ * ENNReal.ofReal (‖E‖ * ‖U‖) := h
      _ = ENNReal.ofReal
          (((domainMeasure 1 Ω) Set.univ ^ (q : ℝ)⁻¹).toReal * (‖E‖ * ‖U‖)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol]
      _ = _ := by simp [criticalFirstOrderConstant, E, mul_assoc]
  · by_cases hnq : (n : ℝ) < q
    · have hn2 : 2 ≤ n := by have := Fact.out (p := 0 < n); omega
      let s := pStarPreimage n q
      have hs1 : 1 ≤ s := one_le_pStarPreimage hn2 hnq
      have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
      have hsn : (s : ℝ) < n := pStarPreimage_lt_dimension Fact.out hq0
      have hsn' : (s : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hsn.le
      let V := lowerExponentOfFiniteMeasure hsn' U
      have hVU : baseRepresentative V =ᵐ[domainMeasure n Ω] baseRepresentative U :=
        lowerExponentOfFiniteMeasure_apply_ae hsn' U (baseIndex n 1)
      have hexp : higherOrderExponent n 1 s = q := by
        simpa [higherOrderExponent, pStar] using pStar_pStarPreimage Fact.out hq0
      have h := eLpNorm_firstOrder_le_of_extension hs1 Fact.out hsn
        (Extension.C1.operator (n := n) (p := (s : ℝ≥0∞)) (Ω := Ω)) V
      rw [hexp, eLpNorm_congr_ae hVU] at h
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have hnorm := mul_le_mul_of_nonneg_left
        (norm_lowerExponentOfFiniteMeasure_le hsn' U)
        (firstOrderDomainConstant_nonneg (p := s) (Ω := Ω))
      simpa [criticalFirstOrderConstant, hn, hnq, firstOrderDomainConstant, s, V,
        mul_assoc] using hnorm
    · have hqn : (q : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast le_of_not_gt hnq
      let V := lowerExponentOfFiniteMeasure hqn U
      have hVU : baseRepresentative V =ᵐ[domainMeasure n Ω] baseRepresentative U :=
        lowerExponentOfFiniteMeasure_apply_ae hqn U (baseIndex n 1)
      have h := ENNReal.ofReal_le_ofReal
        ((wkpBaseCoordinateCLM_norm_le V).trans (norm_lowerExponentOfFiniteMeasure_le hqn U))
      change ENNReal.ofReal (eLpNorm (baseRepresentative V) _ _).toReal ≤ _ at h
      have hfinite : eLpNorm (baseRepresentative V) (q : ℝ≥0∞) (domainMeasure n Ω) ≠ ∞ :=
        Lp.eLpNorm_ne_top (V.val (baseIndex n 1))
      rw [ENNReal.ofReal_toReal hfinite, eLpNorm_congr_ae hVU] at h
      simpa [criticalFirstOrderConstant, hn, hnq] using h

end SobolevSpace.Inequalities
