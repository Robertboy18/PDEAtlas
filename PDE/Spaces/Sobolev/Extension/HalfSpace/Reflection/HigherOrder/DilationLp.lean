/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.NormalDilation
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Lp
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import PDE.Analysis.MeasureTheory.Lp.Composition.MeasureBound

/-!
# Bounded pullback by reflected normal dilations

A negative normal dilation carries the lower half-space to the upper half-space.
Its Jacobian has absolute value `|a|`, so pullback is bounded on every `L^p`,
including `p = 1` and `p = ∞`. The construction uses Mathlib's change of measure
map followed by its measure-preserving `L^p` pullback.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-- A normal dilation has determinant equal to its normal factor. -/
theorem det_normalDilation (i : Fin n) (a : ℝ) :
    LinearMap.det (normalDilation i a).toLinearMap = a := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmatrix : LinearMap.toMatrix b b (normalDilation i a).toLinearMap =
      Matrix.diagonal (fun j ↦ if j = i then a else 1) := by
    ext j l
    simp only [LinearMap.toMatrix_apply, b,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, Matrix.diagonal_apply]
    by_cases hjl : j = l
    · subst j
      simp
    · simp [hjl]
  rw [← LinearMap.det_toMatrix b, hmatrix, Matrix.det_diagonal]
  simp

/-- Lebesgue measure transforms by the inverse absolute normal factor. -/
theorem map_volume_normalDilation (i : Fin n) (a : ℝ) (ha : a ≠ 0) :
    Measure.map (normalDilation i a) volume = ENNReal.ofReal |a⁻¹| • volume := by
  simpa only [det_normalDilation, ContinuousLinearMap.coe_coe] using
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ^n))
      (f := (normalDilation i a).toLinearMap) (by rwa [det_normalDilation])

variable (n) [Fact (0 < n)]

/-- A negative normal dilation takes precisely the lower half-space into the upper one. -/
theorem preimage_upper_normalDilation (a : ℝ) (ha : a < 0) :
    normalDilation (PDE.Common.lastIndex (n := n)) a ⁻¹' ℝ^n₊ = ℝ^n₋ := by
  ext x
  simp only [Set.mem_preimage, HalfSpace.upper, HalfSpace.lower, Set.mem_ofPred_eq,
    normalDilation_apply, ite_eq_left]
  simpa only [smul_eq_mul] using (smul_pos_iff_of_neg_left (b := x
    (PDE.Common.lastIndex (n := n))) ha)

/-- Change of variables on the two open half-spaces. -/
theorem map_lower_normalDilation (a : ℝ) (ha : a < 0) :
    Measure.map (normalDilation (PDE.Common.lastIndex (n := n)) a)
      (domainMeasure n ℝ^n₋) = ENNReal.ofReal |a⁻¹| • domainMeasure n ℝ^n₊ := by
  rw [domainMeasure, ← preimage_upper_normalDilation n a ha,
    ← Measure.restrict_map (normalDilation _ a).continuous.measurable
      (HalfSpace.measurableSet_upper (n := n)),
    map_volume_normalDilation _ a ha.ne, Measure.restrict_smul, domainMeasure]

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pullback of an upper-half-space `L^p` class by a reflected normal dilation. -/
def dilationPullbackLp (a : ℝ) (ha : a < 0) :
    DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p ℝ^n₋ :=
  MeasureTheory.Lp.compMeasureLeSMul
    (normalDilation (PDE.Common.lastIndex (n := n)) a)
    (normalDilation _ a).continuous.measurable ENNReal.ofReal_ne_top
    (le_of_eq (map_lower_normalDilation n a ha))

/-- The `L^p` pullback is represented by the literal normal dilation. -/
theorem dilationPullbackLp_apply_ae (a : ℝ) (ha : a < 0) (u : DerivLp n p ℝ^n₊) :
    (dilationPullbackLp n p a ha u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₋]
      fun x ↦ u (normalDilation (PDE.Common.lastIndex (n := n)) a x) := by
  exact MeasureTheory.Lp.coeFn_compMeasureLeSMul _ _ _ _ u

/-- The pullback bound uses the inverse Jacobian to the power `1/p`; at `p = ∞`
this power is zero. -/
theorem norm_dilationPullbackLp_le (a : ℝ) (ha : a < 0) (u : DerivLp n p ℝ^n₊) :
    ‖dilationPullbackLp n p a ha u‖ ≤ |a⁻¹| ^ (1 / p).toReal * ‖u‖ := by
  simpa only [dilationPullbackLp, ENNReal.toReal_ofReal (abs_nonneg _)] using
    MeasureTheory.Lp.norm_compMeasureLeSMul_apply_le
      (normalDilation (PDE.Common.lastIndex (n := n)) a)
      (normalDilation _ a).continuous.measurable ENNReal.ofReal_ne_top
      (le_of_eq (map_lower_normalDilation n a ha)) u

/-- The exact Jacobian gives equality in the normal-dilation norm bound. -/
theorem norm_dilationPullbackLp (a : ℝ) (ha : a < 0) (u : DerivLp n p ℝ^n₊) :
    ‖dilationPullbackLp n p a ha u‖ = |a⁻¹| ^ (1 / p).toReal * ‖u‖ := by
  simpa only [dilationPullbackLp, ENNReal.toReal_ofReal (abs_nonneg _)] using
    MeasureTheory.Lp.norm_compMeasureLeSMul_apply_eq
      (normalDilation (PDE.Common.lastIndex (n := n)) a)
      (normalDilation _ a).continuous.measurable ENNReal.ofReal_ne_top
      (le_of_eq (map_lower_normalDilation n a ha))
      (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero ha.ne)))
      (map_lower_normalDilation n a ha) u

end SobolevSpace.GraphSpace.HigherOrderReflection
