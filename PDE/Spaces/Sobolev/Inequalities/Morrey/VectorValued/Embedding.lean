/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Representative

/-!
# The Banach-valued Morrey embedding

The continuous representative is unique because Lebesgue measure has full support.
Consequently the representative constructed by mollification is linear, injective, and
commutes with continuous linear maps of codomains. Its sup norm and Hölder constant are
bounded by the Sobolev graph norm, with no finite-dimensional assumption on the target.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Any continuous representative of the Sobolev class equals the Morrey representative
at every point. In particular, the construction preserves classical functions. -/
theorem morreyRepresentative_eq (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) {f : ℝ^n → F} (hf : Continuous f)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f) :
    (morreyRepresentative hp hfinite U : ℝ^n → F) = f :=
  Measure.eq_of_ae_eq ((morreyRepresentative_ae hp hfinite U).trans hbase)
    (morreyRepresentative hp hfinite U).continuous hf

/-- Uniqueness of continuous representatives gives additivity. -/
theorem morreyRepresentative_add (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U V : W^{1,p}(ℝ^n; F)) :
    morreyRepresentative hp hfinite (U + V) =
      morreyRepresentative hp hfinite U + morreyRepresentative hp hfinite V := by
  apply DFunLike.coe_injective
  apply morreyRepresentative_eq hp hfinite (U + V)
    ((morreyRepresentative hp hfinite U).continuous.add
      (morreyRepresentative hp hfinite V).continuous)
  have h := Lp.coeFn_add (U.val (baseIndex n 1)) (V.val (baseIndex n 1))
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h, morreyRepresentative_ae hp hfinite U,
    morreyRepresentative_ae hp hfinite V] with x hx hU hV
  exact hx.trans (congrArg₂ (· + ·) hU.symm hV.symm)

/-- Uniqueness of continuous representatives gives real linearity. -/
theorem morreyRepresentative_smul (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (c : ℝ) (U : W^{1,p}(ℝ^n; F)) :
    morreyRepresentative hp hfinite (c • U) = c • morreyRepresentative hp hfinite U := by
  apply DFunLike.coe_injective
  apply morreyRepresentative_eq hp hfinite (c • U)
    ((morreyRepresentative hp hfinite U).continuous.const_smul c)
  have h := Lp.coeFn_smul c (U.val (baseIndex n 1))
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h, morreyRepresentative_ae hp hfinite U] with x hx hU
  exact hx.trans (congrArg (c • ·) hU.symm)

/-- The bounded linear Morrey embedding into bounded continuous Banach-valued functions,
for every finite exponent `p > n`. Its values are Hölder with exponent `1 - n/p`. -/
def morreyEmbedding (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞) :
    W^{1,p}(ℝ^n; F) →L[ℝ] (ℝ^n →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := morreyRepresentative hp hfinite
      map_add' := morreyRepresentative_add hp hfinite
      map_smul' := morreyRepresentative_smul hp hfinite }
    (morreyConstant n p hp) (norm_morreyRepresentative_le hp hfinite)

/-- The embedding uses the continuous representative constructed above. -/
@[simp] theorem morreyEmbedding_apply (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    morreyEmbedding hp hfinite U = morreyRepresentative hp hfinite U := rfl

/-- The embedding preserves the physical base function almost everywhere. -/
theorem morreyEmbedding_ae (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    (morreyEmbedding hp hfinite U : ℝ^n → F) =ᵐ[volume]
      (U.val (baseIndex n 1) : ℝ^n → F) :=
  morreyRepresentative_ae hp hfinite U

/-- The Morrey operator norm bound is uniform in the Banach target. -/
theorem norm_morreyEmbedding_le (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞) :
    ‖morreyEmbedding (F := F) hp hfinite‖ ≤ morreyConstant n p hp :=
  ContinuousLinearMap.opNorm_le_bound _ (morreyConstant_nonneg hp)
    (norm_morreyRepresentative_le hp hfinite)

/-- The embedding's values satisfy the global Morrey Hölder bound. -/
theorem holderWith_morreyEmbedding (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    HolderWith (morreyConstant n p hp * ‖U‖).toNNReal (morreyExponent n p).toNNReal
      (morreyEmbedding hp hfinite U) :=
  holderWith_morreyRepresentative hp hfinite U

/-- The Morrey embedding is injective on the Sobolev graph. -/
theorem morreyEmbedding_injective (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞) :
    Function.Injective (morreyEmbedding (F := F) hp hfinite) := by
  intro U V h
  apply WkpSpaceOn.ext_of_base_ae
  have hbase := (morreyEmbedding_ae hp hfinite U).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg DFunLike.coe h)).trans
      (morreyEmbedding_ae hp hfinite V))
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using hbase

/-- The representative commutes pointwise with any continuous linear codomain map. -/
theorem morreyEmbedding_mapCLM (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (L : F →L[ℝ] G) (U : W^{1,p}(ℝ^n; F)) (x : ℝ^n) :
    morreyEmbedding hp hfinite (mapCLM L U) x = L (morreyEmbedding hp hfinite U x) := by
  apply congrFun (morreyRepresentative_eq hp hfinite (mapCLM L U)
    (L.continuous.comp (morreyEmbedding hp hfinite U).continuous) ?_) x
  have h := mapCLM_apply_ae L U (baseIndex n 1)
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
  exact h.trans ((morreyEmbedding_ae hp hfinite U).symm.fun_comp L)

end SobolevSpace.VectorValued
