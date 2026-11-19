/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Operators
public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Infinity.Representative

/-!
# The Banach-valued endpoint embedding

The continuous representative is unique because Lebesgue measure has full support.
Consequently the Lipschitz representative is linear, injective, and
commutes with continuous linear maps of codomains. Its sup norm is
bounded by the norm of the base coordinate, for an arbitrary Banach codomain.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ}
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Uniqueness of continuous representatives gives additivity. -/
theorem lipschitzRepresentative_add (U V : W^{1,∞}(ℝ^n; F)) :
    lipschitzRepresentative (U + V) =
      lipschitzRepresentative U + lipschitzRepresentative V := by
  apply DFunLike.coe_injective
  apply lipschitzRepresentative_eq (U + V)
    ((lipschitzRepresentative U).continuous.add
      (lipschitzRepresentative V).continuous)
  have h := Lp.coeFn_add (U.val (baseIndex n 1)) (V.val (baseIndex n 1))
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h, lipschitzRepresentative_ae U,
    lipschitzRepresentative_ae V] with x hx hU hV
  exact hx.trans (congrArg₂ (· + ·) hU.symm hV.symm)

/-- Uniqueness of continuous representatives gives real linearity. -/
theorem lipschitzRepresentative_smul (c : ℝ) (U : W^{1,∞}(ℝ^n; F)) :
    lipschitzRepresentative (c • U) = c • lipschitzRepresentative U := by
  apply DFunLike.coe_injective
  apply lipschitzRepresentative_eq (c • U)
    ((lipschitzRepresentative U).continuous.const_smul c)
  have h := Lp.coeFn_smul c (U.val (baseIndex n 1))
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h, lipschitzRepresentative_ae U] with x hx hU
  exact hx.trans (congrArg (c • ·) hU.symm)

/-- The bounded linear endpoint embedding into bounded continuous Banach-valued functions.
Its values are globally Lipschitz, including in dimension zero. -/
def lipschitzEmbedding :
    W^{1,∞}(ℝ^n; F) →L[ℝ] (ℝ^n →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := lipschitzRepresentative
      map_add' := lipschitzRepresentative_add
      map_smul' := lipschitzRepresentative_smul }
    1 (fun U ↦ by
      change ‖lipschitzRepresentative U‖ ≤ 1 * ‖U‖
      simpa only [one_mul] using norm_lipschitzRepresentative_le U)

/-- The embedding uses the continuous representative constructed above. -/
@[simp] theorem lipschitzEmbedding_apply (U : W^{1,∞}(ℝ^n; F)) :
    lipschitzEmbedding U = lipschitzRepresentative U := rfl

/-- The embedding preserves the physical base function almost everywhere. -/
theorem lipschitzEmbedding_ae (U : W^{1,∞}(ℝ^n; F)) :
    (lipschitzEmbedding U : ℝ^n → F) =ᵐ[volume]
      (U.val (baseIndex n 1) : ℝ^n → F) :=
  lipschitzRepresentative_ae U

/-- The endpoint embedding into the uniform norm is a contraction. -/
theorem norm_lipschitzEmbedding_le :
    ‖lipschitzEmbedding (n := n) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun U ↦ by
      simpa only [lipschitzEmbedding_apply, one_mul] using norm_lipschitzRepresentative_le U)

/-- The image has a Lipschitz constant given by the derivative-row norms. -/
theorem lipschitzWith_lipschitzEmbedding (U : W^{1,∞}(ℝ^n; F)) :
    LipschitzWith (∑ j : Fin n, ‖U.val (singleDerivIndex n j)‖₊) (lipschitzEmbedding U) :=
  lipschitzWith_lipschitzRepresentative U

/-- The endpoint embedding is injective on the Sobolev graph. -/
theorem lipschitzEmbedding_injective :
    Function.Injective (lipschitzEmbedding (n := n) (F := F)) := by
  intro U V h
  apply WkpSpaceOn.ext_of_base_ae
  have hbase := (lipschitzEmbedding_ae U).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg DFunLike.coe h)).trans
      (lipschitzEmbedding_ae V))
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using hbase

/-- The representative commutes pointwise with any continuous linear codomain map. -/
theorem lipschitzEmbedding_mapCLM (L : F →L[ℝ] G) (U : W^{1,∞}(ℝ^n; F)) (x : ℝ^n) :
    lipschitzEmbedding (mapCLM L U) x = L (lipschitzEmbedding U x) := by
  apply congrFun (lipschitzRepresentative_eq (mapCLM L U)
    (L.continuous.comp (lipschitzEmbedding U).continuous) ?_) x
  have h := mapCLM_apply_ae L U (baseIndex n 1)
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
  exact h.trans ((lipschitzEmbedding_ae U).symm.fun_comp L)

end SobolevSpace.VectorValued
