/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Coefficients
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.DilationLp

/-!
# Weighted reflection of normed-valued Lp functions

Negative normal dilations carry the lower half-space to the upper half-space.
Their inverse Jacobians give bounded pullbacks on every `1 ≤ p ≤ ∞`. Taking a
finite linear combination and extending both branches by zero constructs each
row of higher-order reflection for any real normed codomain.

The coefficients and geometry are the scalar ones. Completeness of the codomain
is unnecessary at the Lp level; relations between weak derivatives belong to
the subsequent Sobolev extension construction.
-/

@[expose] public noncomputable section

namespace SobolevSpace.VectorValued.HigherOrderReflection

open Set MeasureTheory
open SobolevSpace.GraphSpace.HigherOrderReflection
open scoped ENNReal

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback from the upper to the lower half-space by a negative normal dilation. -/
def dilationPullbackLp (a : ℝ) (ha : a < 0) :
    Lp F p (domainMeasure n ℝ^n₊) →L[ℝ] Lp F p (domainMeasure n ℝ^n₋) :=
  Lp.compMeasureLeSMul (normalDilation (PDE.Common.lastIndex (n := n)) a)
    (normalDilation _ a).continuous.measurable ENNReal.ofReal_ne_top
    (le_of_eq (map_lower_normalDilation n a ha))

/-- The pullback represents ordinary composition almost everywhere. -/
theorem dilationPullbackLp_apply_ae (a : ℝ) (ha : a < 0)
    (u : Lp F p (domainMeasure n ℝ^n₊)) :
    (dilationPullbackLp n p a ha u : ℝ^n → F) =ᵐ[domainMeasure n ℝ^n₋]
      fun x ↦ u (normalDilation (PDE.Common.lastIndex (n := n)) a x) :=
  Lp.coeFn_compMeasureLeSMul _ _ _ _ u

/-- The exact dilation norm includes the inverse Jacobian, also at `p = ∞`. -/
theorem norm_dilationPullbackLp (a : ℝ) (ha : a < 0)
    (u : Lp F p (domainMeasure n ℝ^n₊)) :
    ‖dilationPullbackLp n p a ha u‖ = |a⁻¹| ^ (1 / p).toReal * ‖u‖ := by
  simpa only [dilationPullbackLp, ENNReal.toReal_ofReal (abs_nonneg _)] using
    Lp.norm_compMeasureLeSMul_apply_eq
      (normalDilation (PDE.Common.lastIndex (n := n)) a)
      (normalDilation _ a).continuous.measurable ENNReal.ofReal_ne_top
      (le_of_eq (map_lower_normalDilation n a ha))
      (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero ha.ne)))
      (map_lower_normalDilation n a ha) u


/-- The lower branch for a row containing `r` normal derivatives. -/
def weightedPullbackLp (r : ℕ) :
    Lp F p (domainMeasure n ℝ^n₊) →L[ℝ] Lp F p (domainMeasure n ℝ^n₋) :=
  ∑ j : Fin (k + 1), (reflectionCoeff k j * reflectionNode k j ^ r) •
    dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j)

/-- Weighted reflection, retaining the source on the upper half-space. -/
def weightedExtendLp (r : ℕ) :
    Lp F p (domainMeasure n ℝ^n₊) →L[ℝ] Lp F p (domainMeasure n univ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ id
    (SobolevSpace.Extension.Lp.measurePreserving_id_univ (n := n))).toContinuousLinearMap.comp
      ((Lp.extendByZeroₗᵢ (𝕜 := ℝ)
        (HalfSpace.measurableSet_upper (n := n))).toContinuousLinearMap +
      (Lp.extendByZeroₗᵢ (𝕜 := ℝ)
        (HalfSpace.measurableSet_lower (n := n))).toContinuousLinearMap.comp
          (weightedPullbackLp n k p r))

/-- The lower branch is the literal finite sum of scalar multiples of dilated values. -/
theorem weightedPullbackLp_apply_ae (r : ℕ) (u : Lp F p (domainMeasure n ℝ^n₊)) :
    (weightedPullbackLp n k p r u : ℝ^n → F) =ᵐ[domainMeasure n ℝ^n₋]
      fun x ↦ ∑ j : Fin (k + 1), (reflectionCoeff k j * reflectionNode k j ^ r) •
        u (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) x) := by
  have hsum := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin (k + 1)))
    (fun j ↦ (reflectionCoeff k j * reflectionNode k j ^ r) •
      dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u)
  have hterm : ∀ j : Fin (k + 1), ∀ᵐ x ∂domainMeasure n ℝ^n₋,
      (((reflectionCoeff k j * reflectionNode k j ^ r) •
        dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u :
        Lp F p (domainMeasure n ℝ^n₋)) : ℝ^n → F) x =
      (reflectionCoeff k j * reflectionNode k j ^ r) •
        u (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) x) := by
    intro j
    filter_upwards [Lp.coeFn_smul (reflectionCoeff k j * reflectionNode k j ^ r)
      (dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u),
      dilationPullbackLp_apply_ae n p (reflectionNode k j) (reflectionNode_neg k j) u]
      with x hx hy
    simp only [hx, Pi.smul_apply, hy]
  simp only [weightedPullbackLp, sum_apply, smul_apply]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with x hx hy
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ ↦ hy j)

/-- The lower-branch bound keeps each inverse Jacobian separately. -/
theorem norm_weightedPullbackLp_le (r : ℕ) (u : Lp F p (domainMeasure n ℝ^n₊)) :
    ‖weightedPullbackLp n k p r u‖ ≤
      (∑ j, ‖reflectionCoeff k j * reflectionNode k j ^ r‖ *
        |(reflectionNode k j)⁻¹| ^ (1 / p).toReal) * ‖u‖ := by
  simp only [weightedPullbackLp, sum_apply, smul_apply]
  calc
    ‖∑ j : Fin (k + 1), (reflectionCoeff k j * reflectionNode k j ^ r) •
        dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u‖ ≤
        ∑ j, ‖(reflectionCoeff k j * reflectionNode k j ^ r) •
          dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_smul, norm_dilationPullbackLp, Finset.sum_mul, mul_assoc]

/-- A finite bound for the extension, uniform over the normed codomain. -/
theorem norm_weightedExtendLp_le (r : ℕ) (u : Lp F p (domainMeasure n ℝ^n₊)) :
    ‖weightedExtendLp n k p r u‖ ≤
      (1 + ∑ j, ‖reflectionCoeff k j * reflectionNode k j ^ r‖ *
        |(reflectionNode k j)⁻¹| ^ (1 / p).toReal) * ‖u‖ := by
  change ‖Lp.compMeasurePreservingₗᵢ ℝ id _
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) (HalfSpace.measurableSet_upper (n := n)) u +
      Lp.extendByZeroₗᵢ (𝕜 := ℝ) (HalfSpace.measurableSet_lower (n := n))
        (weightedPullbackLp n k p r u))‖ ≤ _
  rw [LinearIsometry.norm_map]
  refine (norm_add_le _ _).trans ?_
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map, add_mul, one_mul]
  exact add_le_add le_rfl (norm_weightedPullbackLp_le n k p r u)

/-- The global representative is the original upper branch plus the finite reflected sum. -/
theorem weightedExtendLp_apply_ae (r : ℕ) (u : Lp F p (domainMeasure n ℝ^n₊)) :
    (weightedExtendLp n k p r u : ℝ^n → F) =ᵐ[volume]
      fun x ↦ ℝ^n₊.indicator (u : ℝ^n → F) x +
        ℝ^n₋.indicator (fun y ↦ ∑ j : Fin (k + 1),
          (reflectionCoeff k j * reflectionNode k j ^ r) •
            u (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) y)) x := by
  let U := Lp.extendByZeroₗᵢ (𝕜 := ℝ) (HalfSpace.measurableSet_upper (n := n)) u
  let V := Lp.extendByZeroₗᵢ (𝕜 := ℝ) (HalfSpace.measurableSet_lower (n := n))
    (weightedPullbackLp n k p r u)
  have ht := Lp.coeFn_compMeasurePreserving (U + V)
    (SobolevSpace.Extension.Lp.measurePreserving_id_univ (n := n))
  have hu := Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ)
    (HalfSpace.measurableSet_upper (n := n)) u
  have hv := Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ)
    (HalfSpace.measurableSet_lower (n := n)) (weightedPullbackLp n k p r u)
  have hp := (ae_restrict_iff' (HalfSpace.measurableSet_lower (n := n))).mp
    (weightedPullbackLp_apply_ae n k p r u)
  simp only [Measure.restrict_univ, Function.comp_id] at ht
  filter_upwards [ht, Lp.coeFn_add U V, hu, hv, hp] with x ht ha hu hv hp
  change (Lp.compMeasurePreserving id _ (U + V) : ℝ^n → F) x = _
  rw [ht, ha]
  change U x + V x = _
  rw [hu, hv]
  by_cases hx : x ∈ ℝ^n₋
  · simp only [Set.indicator_of_mem hx, hp hx]
  · simp only [Set.indicator_of_notMem hx]

/-- Upper-half-space restriction is a left inverse for every weighted row. -/
@[simp] theorem restrict_weightedExtendLp (r : ℕ)
    (u : Lp F p (domainMeasure n ℝ^n₊)) :
    Lp.restrictionCLMOfLE
      (Measure.restrict_mono (subset_univ ℝ^n₊) le_rfl)
      (weightedExtendLp n k p r u) = u := by
  apply Lp.ext
  refine (Lp.restrictionCLMOfLE_apply_ae _ _).trans ?_
  have he := ae_restrict_of_ae (s := ℝ^n₊) (weightedExtendLp_apply_ae n k p r u)
  filter_upwards [he, ae_restrict_mem (HalfSpace.measurableSet_upper (n := n))]
    with x hx hxupper
  have hxlower : x ∉ ℝ^n₋ := by
    change 0 < x (PDE.Common.lastIndex (n := n)) at hxupper
    change ¬x (PDE.Common.lastIndex (n := n)) < 0
    exact not_lt_of_ge hxupper.le
  simpa only [Set.indicator_of_mem hxupper, Set.indicator_of_notMem hxlower, add_zero]
    using hx

end SobolevSpace.VectorValued.HigherOrderReflection
