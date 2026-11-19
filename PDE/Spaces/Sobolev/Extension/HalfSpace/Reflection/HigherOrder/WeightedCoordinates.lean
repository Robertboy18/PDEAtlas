/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedLp

/-!
# Bounded weighted reflection of derivative bundles

The row indexed by a symmetric multi-index `a` uses the normal multiplicity of `a`
in the reflected coefficients. This gives a continuous linear map of the ambient
`L^p` bundles for every finite order and every `1 ≤ p ≤ ∞`. Restriction is a left
inverse.

The codomain here is `WkpAmbientOn`, not `WkpSpaceOn`: preserving the Sobolev
weak-derivative constraints requires a further boundary gluing proof.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set
open scoped ENNReal

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Weighted reflection on the full finite bundle of derivative coordinates. -/
def weightedReflectAmbient :
    WkpAmbientOn n k p ℝ^n₊ →L[ℝ] WkpAmbientOn n k p univ :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ DerivLp n p univ)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.pi fun a : DerivIndex n k ↦
        (weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n)))).comp
          (ContinuousLinearMap.proj a)).comp
        (PiLp.continuousLinearEquiv p ℝ
          (fun _ : DerivIndex n k ↦ DerivLp n p ℝ^n₊)).toContinuousLinearMap)

/-- Each coordinate uses the weight dictated by its number of normal derivatives. -/
@[simp] theorem weightedReflectAmbient_apply
    (U : WkpAmbientOn n k p ℝ^n₊) (a : DerivIndex n k) :
    weightedReflectAmbient n k p U a =
      weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n))) (U a) := by
  simp [weightedReflectAmbient]

/-- Restriction recovers every source coordinate. -/
@[simp] theorem restrict_weightedReflectAmbient (U : WkpAmbientOn n k p ℝ^n₊) :
    restrictAmbient (subset_univ ℝ^n₊) (weightedReflectAmbient n k p U) = U := by
  apply PiLp.ext
  intro a
  simp only [restrictAmbient_apply, weightedReflectAmbient_apply, restrict_weightedExtendLp]

/-- The ambient weighted reflection is injective because restriction is a left inverse. -/
theorem weightedReflectAmbient_injective :
    Function.Injective (weightedReflectAmbient n k p) :=
  Function.LeftInverse.injective (restrict_weightedReflectAmbient n k p)

/-- A concrete derivative word selects the corresponding normal multiplicity. -/
theorem weightedReflectAmbient_apply_derivIndexOfList
    (U : WkpAmbientOn n k p ℝ^n₊) (α : List (Fin n)) (hα : α.length ≤ k) :
    weightedReflectAmbient n k p U (derivIndexOfList α hα) =
      weightedExtendLp n k p (α.count (PDE.Common.lastIndex (n := n)))
        (U (derivIndexOfList α hα)) := by
  simp [weightedReflectAmbient_apply, DerivIndex.multiplicity, derivIndexOfList]

end SobolevSpace.GraphSpace.HigherOrderReflection
