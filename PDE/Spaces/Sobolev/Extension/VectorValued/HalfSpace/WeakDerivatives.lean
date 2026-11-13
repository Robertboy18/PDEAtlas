/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Compatibility
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.GlobalWeakDerivatives

/-!
# Weak derivatives of Banach-valued weighted reflection

Continuous linear functionals commute with the weighted `Lp` extension. The scalar
moment-cancellation theorem therefore proves the weak derivative across the boundary
for every complete real normed codomain. Both reflected rows are Bochner locally
integrable because they are `Lp` classes with `1 ≤ p ≤ ∞`.

There is no trace or boundary compatibility hypothesis. In particular, the proof at
`p = ∞` uses the same scalar boundary cancellation, not smooth density.
-/

@[expose] public noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SobolevSpace.VectorValued.HigherOrderReflection

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A matched reflection moment cancels the boundary contribution in the Banach-valued
weak derivative. A normal derivative increases the normal multiplicity by one. -/
theorem hasWeakDerivativeOn_weightedExtendLp (r : ℕ) (hr : r ≤ k)
    (i : Fin n) (u du : Lp F p (domainMeasure n ℝ^n₊))
    (hweak : HasWeakDerivativeOn ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ [i]
      (u : ℝ^n → F) (du : ℝ^n → F)) :
    HasWeakDerivativeOn ⊤ [i] (weightedExtendLp n k p r u : ℝ^n → F)
      (weightedExtendLp n k p
        (r + if i = PDE.Common.lastIndex (n := n) then 1 else 0) du : ℝ^n → F) := by
  have hloc (s : ℕ) (v : Lp F p (domainMeasure n ℝ^n₊)) :
      LocallyIntegrableOn (weightedExtendLp n k p s v) univ volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (weightedExtendLp n k p s v)).locallyIntegrable Fact.out)
  apply (hasWeakDerivativeOn_iff_forall_dual (hloc _ _) (hloc _ _)).mpr
  intro L
  have hsource := (hasWeakDerivativeOn_real_iff.mp (hweak.map L)).congr_ae
    (L.coeFn_compLpL u).symm (L.coeFn_compLpL du).symm
  have hscalar :=
    GraphSpace.HigherOrderReflection.hasWeakDerivativeOn_weightedExtendLp
      n k p r hr i _ _ hsource
  have hrow (s : ℕ) (v : Lp F p (domainMeasure n ℝ^n₊)) :
      (GraphSpace.HigherOrderReflection.weightedExtendLp n k p s
        (L.compLpL p (domainMeasure n ℝ^n₊) v) : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
        L ∘ (weightedExtendLp n k p s v : ℝ^n → F) := by
    have h := L.coeFn_compLpL (weightedExtendLp n k p s v)
    change (((L.compLpL p (domainMeasure n univ)).comp
      (weightedExtendLp n k p s)) v : ℝ^n → ℝ) =ᵐ[_] _ at h
    rw [compLpL_weightedExtendLp] at h
    exact h
  exact hscalar.congr_ae (hrow _ _) (hrow _ _)

end SobolevSpace.VectorValued.HigherOrderReflection
