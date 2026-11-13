/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Lp

/-!
# Codomain naturality of weighted half-space reflection

The physical reflection formula is a finite sum of scalar multiples of dilated
values. Every dilation is nonsingular between the restricted measures, so a
continuous linear map of values commutes with the extension. This holds
for every reflection row and both exponent endpoints; completeness is not needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.VectorValued

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace HigherOrderReflection

open GraphSpace.HigherOrderReflection

variable (n k : ℕ) [Fact (0 < n)]

/-- Weighted reflection commutes with any continuous linear map of normed codomains. -/
theorem weightedExtendLp_compLpL (r : ℕ) (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n ℝ^n₊)) :
    weightedExtendLp n k p r (L.compLpL p (domainMeasure n ℝ^n₊) u) =
      L.compLpL p (domainMeasure n univ) (weightedExtendLp n k p r u) := by
  apply Lp.ext
  have hcomp : ∀ j : Fin (k + 1), ∀ᵐ x ∂domainMeasure n ℝ^n₋,
      (L.compLpL p (domainMeasure n ℝ^n₊) u)
          (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) x) =
        L (u (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) x)) := by
    intro j
    have hq : QuasiMeasurePreserving
        (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j))
        (domainMeasure n ℝ^n₋) (domainMeasure n ℝ^n₊) :=
      ⟨(normalDilation _ _).continuous.measurable, by
        rw [map_lower_normalDilation n _ (reflectionNode_neg k j)]
        exact Measure.smul_absolutelyContinuous⟩
    exact hq.ae_eq_comp (L.coeFn_compLpL u)
  have hu := (ae_restrict_iff' (HalfSpace.measurableSet_upper (n := n))).mp
    (L.coeFn_compLpL u)
  have hl := (ae_restrict_iff' (HalfSpace.measurableSet_lower (n := n))).mp
    (ae_all_iff.mpr hcomp)
  have hL := L.coeFn_compLpL (weightedExtendLp n k p r u)
  have hv := weightedExtendLp_apply_ae n k p r u
  have hw := weightedExtendLp_apply_ae n k p r
    (L.compLpL p (domainMeasure n ℝ^n₊) u)
  simp only [domainMeasure, Measure.restrict_univ] at hL ⊢
  filter_upwards [hL, hv, hw, hu, hl] with x hL hv hw hu hl
  rw [hL, hv, hw, map_add]
  congr 1
  · by_cases hx : x ∈ ℝ^n₊
    · simp only [indicator_of_mem hx, hu hx]
    · simp only [indicator_of_notMem hx, map_zero]
  · by_cases hx : x ∈ ℝ^n₋
    · simp only [indicator_of_mem hx, map_sum, map_smul]
      exact Finset.sum_congr rfl (fun j _ ↦ congrArg
        ((reflectionCoeff k j * reflectionNode k j ^ r) • ·) (hl hx j))
    · simp only [indicator_of_notMem hx, map_zero]

end HigherOrderReflection

end SobolevSpace.VectorValued
