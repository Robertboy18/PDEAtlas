/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.GlobalWeakDerivatives
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedCoordinates
import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Operator
import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar

/-!
# Bounded higher-order extension from a half-space

Weighted normal reflection extends `W^{k,p}(ℝ^n₊)` boundedly and linearly to
`W^{k,p}(ℝ^n)` for every finite order `k` and every `1 ≤ p ≤ ∞`.
Restriction recovers the source, including all derivative coordinates.

The Banach-valued reflection theorem supplies the Sobolev constraints through
the real scalar equivalence. Its coordinates agree with the scalar weighted
reflection, so the bounded coordinate maps restrict to the
Sobolev spaces, with no boundary compatibility hypothesis on the source.

Evans, *Partial Differential Equations*, §5.4, extends `W^{1,p}` (and `W^{2,p}` for a `C²`
boundary) with a two-term reflection, and remarks that `k > 2` needs a more complicated
higher-order reflection; the weighted reflection with `k + 1` terms is one. The boundary
passage uses moment-cancelled tests and cutoffs, so it applies at both exponent endpoints.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof extends `C¹`
  functions by the two-term reflection (3), p. 269, and Remarks (i) and (ii), p. 271: the same
  operator is bounded on `W^{2,p}` when the boundary is `C²`, and `k > 2` needs a more complicated
  higher-order reflection.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory
open scoped ENNReal

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Weighted reflection preserves every weak derivative constraint through order `k`.
The source is an arbitrary Sobolev bundle on the upper half-space. -/
theorem weightedReflectAmbient_isWkpOn (U : WkpAmbientOn n k p ℝ^n₊)
    (hU : IsWkpOn U) :
    IsWkpOn (weightedReflectAmbient n k p U) := by
  let V := VectorValued.scalarEquiv (Ω := ⊤)
    (VectorValued.HigherOrderReflection.weightedReflection n k p
      ((VectorValued.scalarEquiv (Ω := ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩)).symm ⟨U, hU⟩))
  have hV : V.val = weightedReflectAmbient n k p U := by
    apply PiLp.ext
    intro a
    change VectorValued.HigherOrderReflection.weightedExtendLp n k p
      (a.multiplicity (PDE.Common.lastIndex (n := n))) (U a) =
        weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n))) (U a)
    apply Lp.ext
    simp only [domainMeasure, Measure.restrict_univ]
    have hv := VectorValued.HigherOrderReflection.weightedExtendLp_apply_ae n k p
      (a.multiplicity (PDE.Common.lastIndex (n := n))) (U a)
    have hs := weightedExtendLp_apply_ae n k p
      (a.multiplicity (PDE.Common.lastIndex (n := n))) (U a)
    simp only [smul_eq_mul] at hv hs
    exact hv.trans hs.symm
  exact hV ▸ V.property

/-- The weighted normal reflection as a bounded linear extension
`W^{k,p}(ℝ^n₊) → W^{k,p}(ℝ^n)`, for every finite order `k` and every exponent `1 ≤ p ≤ ∞`. -/
def weightedReflection : W^{k,p}(ℝ^n₊) →L[ℝ] W^{k,p}((univ : Set (ℝ^n))) :=
  ContinuousLinearMap.codRestrict
    ((weightedReflectAmbient n k p).comp
      (Submodule.subtypeL (wkpSubmoduleOn n k p ℝ^n₊)))
    (wkpSubmoduleOn n k p univ)
    (fun U ↦ weightedReflectAmbient_isWkpOn n k p U U.property)

/-- The Sobolev extension has precisely the weighted coordinates. -/
@[simp] theorem weightedReflection_apply_coe (U : W^{k,p}(ℝ^n₊)) :
    (weightedReflection n k p U : WkpAmbientOn n k p univ) =
      weightedReflectAmbient n k p U :=
  rfl

/-- Restriction of the extension recovers the original Sobolev function and all its derivatives. -/
@[simp] theorem restrict_weightedReflection (U : W^{k,p}(ℝ^n₊)) :
    restrictCLM (HalfSpace.measurableSet_upper (n := n)) (subset_univ ℝ^n₊)
      (weightedReflection n k p U) = U := by
  apply Subtype.ext
  simp only [restrictCLM_apply_coe, weightedReflection_apply_coe,
    restrict_weightedReflectAmbient]

/-- The extension is injective because upper-half-space restriction is a left inverse. -/
theorem weightedReflection_injective : Function.Injective (weightedReflection n k p) :=
  Function.LeftInverse.injective (restrict_weightedReflection n k p)

/-- The base coordinate is the literal piecewise weighted reflection almost everywhere. -/
theorem weightedReflection_base_apply_ae (U : W^{k,p}(ℝ^n₊)) :
    ((weightedReflection n k p U : WkpAmbientOn n k p univ) (baseIndex n k) :
      ℝ^n → ℝ) =ᵐ[volume]
      weightedReflectionFun (PDE.Common.lastIndex (n := n)) k
        ((U : WkpAmbientOn n k p ℝ^n₊) (baseIndex n k)) := by
  simp only [weightedReflection_apply_coe, weightedReflectAmbient_apply, baseIndex_multiplicity]
  exact weightedExtendLp_zero_apply_ae n k p _

end SobolevSpace.GraphSpace.HigherOrderReflection
