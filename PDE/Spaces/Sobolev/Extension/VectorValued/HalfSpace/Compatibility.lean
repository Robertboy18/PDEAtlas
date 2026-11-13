/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedLp
public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Lp

/-!
# Scalar testing of weighted reflection

Applying a continuous real functional after normed-valued weighted reflection
agrees with the scalar reflection of the tested function. This identity
allows the scalar boundary gluing argument to be used through separating duals.
-/

@[expose] public noncomputable section

namespace SobolevSpace.VectorValued.HigherOrderReflection

open Set MeasureTheory
open SobolevSpace.GraphSpace.HigherOrderReflection
open scoped ENNReal

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Testing the extended row by a continuous functional gives precisely the old scalar row. -/
theorem compLpL_weightedExtendLp (r : ℕ) (L : F →L[ℝ] ℝ) :
    (L.compLpL p (domainMeasure n univ)).comp (weightedExtendLp n k p r) =
      (SobolevSpace.GraphSpace.HigherOrderReflection.weightedExtendLp n k p r).comp
        (L.compLpL p (domainMeasure n ℝ^n₊)) := by
  ext1 u
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
  have hs := SobolevSpace.GraphSpace.HigherOrderReflection.weightedExtendLp_apply_ae
    n k p r (L.compLpL p (domainMeasure n ℝ^n₊) u)
  simp only [domainMeasure, Measure.restrict_univ] at hL ⊢
  filter_upwards [hL, hv, hs, hu, hl] with x hL hv hs hu hl
  change (L.compLpL p (domainMeasure n univ) (weightedExtendLp n k p r u)) x =
    (SobolevSpace.GraphSpace.HigherOrderReflection.weightedExtendLp n k p r
      (L.compLpL p (domainMeasure n ℝ^n₊) u)) x
  rw [hL, hv, hs, map_add]
  congr 1
  · by_cases hx : x ∈ ℝ^n₊
    · simp only [Set.indicator_of_mem hx, hu hx]
    · simp only [Set.indicator_of_notMem hx, map_zero]
  · by_cases hx : x ∈ ℝ^n₋
    · simp only [Set.indicator_of_mem hx, map_sum, map_smul, smul_eq_mul, reflectedJet]
      exact Finset.sum_congr rfl (fun j _ ↦ congrArg
        ((reflectionCoeff k j * reflectionNode k j ^ r) * ·) (hl hx j).symm)
    · simp only [Set.indicator_of_notMem hx, map_zero]

end SobolevSpace.VectorValued.HigherOrderReflection
