/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PDE.Spaces.Sobolev.Compactness.Rellich.FiniteExponentTranslation
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.FiniteExponentCompactness

/-!
# Compact cutoff observations of whole-space Sobolev functions

Multiplying a whole-space W¹,p function by a smooth compactly supported cutoff is a
compact map into Lp for finite p. The cutoff gives a common bounded support; its
bounded W¹,p operator norm and the Sobolev translation estimate give a common
translation modulus. The finite-exponent Rellich criterion then gives compactness.

Composed with a continuous W¹,p recovery map, this gives local compactness in
space for a bounded energy family. Without the cutoff the inclusion on the whole
space is not compact.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

open MeasureTheory Set
open scoped ENNReal Topology Distributions Sobolev

namespace SobolevSpace.GraphSpace.RellichKondrachov

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compactly supported observation of a whole-space first-order Sobolev function
is compact in finite Lp. -/
theorem cutoffBaseCoordinate_isCompactOperator (hp : p ≠ ∞)
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ)) :
    IsCompactOperator
      ((wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := univ)).comp
        (cutoffCLM (n := n) (p := p) (Ω := univ) ψ)) := by
  let A := cutoffCLM (n := n) (p := p) (Ω := univ) ψ
  let F : W^{1,p}(ℝ^n) →L[ℝ] DerivLp n p univ := wkpBaseCoordinateCLM.comp A
  let S := F '' Metric.closedBall (0 : W^{1,p}(ℝ^n)) 1
  obtain ⟨R, hR⟩ := ψ.hasCompactSupport.isBounded.subset_ball (0 : ℝ^n)
  have htot : TotallyBounded S := by
    apply totallyBounded_Lp_of_bounded_support_translation hp
      S (Metric.isBounded_closedBall.image F) R ((n : ℝ) * ‖A‖) (by positivity)
    · rintro f ⟨U, _, rfl⟩
      have hbase := cutoffCLM_base_apply_ae (n := n) (p := p) (Ω := univ) ψ U
      simp only [domainMeasure, Measure.restrict_univ] at hbase
      filter_upwards [hbase] with x hx hxBall
      have hzero : ψ.toFun x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxK ↦ hxBall (hR hxK))
      calc
        (F U) x = ψ.toFun x * (wkpBaseCoordinateCLM U) x := hx
        _ = 0 := by rw [hzero, zero_mul]
    · rintro f ⟨U, hU, rfl⟩ h
      have hUnorm : ‖U‖ ≤ 1 := mem_closedBall_zero_iff.mp hU
      have hA : ‖A U‖ ≤ ‖A‖ := by
        simpa only [mul_one] using (A.le_opNorm U).trans
          (mul_le_mul_of_nonneg_left hUnorm (norm_nonneg A))
      calc
        ‖Rellich.translateLp p h (F U) - F U‖ ≤ (n : ℝ) * ‖h‖ * ‖A U‖ :=
          Rellich.norm_translateLp_base_sub_le hp h (A U)
        _ ≤ (n : ℝ) * ‖h‖ * ‖A‖ :=
          mul_le_mul_of_nonneg_left hA (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        _ = ‖h‖ * ((n : ℝ) * ‖A‖) := by ring
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image F).mpr
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 (by norm_num), ?_⟩
  exact htot.closure.isCompact_of_isClosed isClosed_closure

end SobolevSpace.GraphSpace.RellichKondrachov
