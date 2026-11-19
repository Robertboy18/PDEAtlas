/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.BoundaryCutoff
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedTestFunctions

/-!
# Global weak derivatives of weighted reflection

The inverse-dilated test converts the two half-space integrals into a single upper
half-space integral. In the normal direction its boundary value cancels by the
moment equation. Removing the boundary cutoff therefore proves the weak derivative
identity on the whole space, including across the boundary.

For row `r` the cancellation uses moment `r`, so `r ≤ k` suffices. Iterating to
Sobolev order `k` only requires this result at normal multiplicities less than `k`.
All results retain the full range `1 ≤ p ≤ ∞`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Distributions

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A matched moment removes the boundary contribution in the global one-step
weak derivative of weighted reflection. No trace or gluing hypothesis is imposed. -/
theorem hasWeakDerivativeOn_weightedExtendLp (r : ℕ) (hr : r ≤ k)
    (i : Fin n) (u du : DerivLp n p ℝ^n₊)
    (hweak : HasWeakDerivativeOn ℝ^n₊ [i] (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn univ [i] (weightedExtendLp n k p r u : ℝ^n → ℝ)
      (weightedExtendLp n k p
        (r + if i = PDE.Common.lastIndex (n := n) then 1 else 0) du : ℝ^n → ℝ) := by
  refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out,
    memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out, ?_⟩
  intro φ _
  let φi : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ
  let s := r + if i = PDE.Common.lastIndex (n := n) then 1 else 0
  let ψ := weightedTest n k s φ
  have hφi : iteratedPartialDeriv [i] φ.toFun = (φi : ℝ^n → ℝ) := by
    funext x
    exact (testFunction_lineDerivCLM_apply φ _ x).symm
  have hψder : ∂[i] ψ.toFun = (weightedTest n k r φi : ℝ^n → ℝ) := by
    funext x
    exact (testFunction_lineDerivCLM_apply ψ _ x).symm.trans
      (congrArg (fun θ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) ↦ θ x)
        (lineDerivCLM_weightedTest n k i r φ))
  have hboundary : i = PDE.Common.lastIndex (n := n) →
      ∀ x : ℝ^n, x (PDE.Common.lastIndex (n := n)) = 0 → ψ x = 0 := by
    intro hi x hx
    simpa only [ψ, s, hi, ↓reduceIte] using
      weightedTest_succ_zero_on_boundary n k r hr φ x hx
  have hu := integral_mul_partialDeriv_eq_neg_of_boundary n p i u du hweak ψ hboundary
  rw [hψder] at hu
  rw [hφi]
  change (∫ x, weightedExtendLp n k p r u x * φi x ∂domainMeasure n univ) =
    (-1) ^ [i].length *
      ∫ x, weightedExtendLp n k p s du x * φ x ∂domainMeasure n univ
  rw [integral_weightedExtendLp_mul, integral_weightedExtendLp_mul]
  simpa only [List.length_singleton, pow_one, neg_one_mul] using hu

end SobolevSpace.GraphSpace.HigherOrderReflection
