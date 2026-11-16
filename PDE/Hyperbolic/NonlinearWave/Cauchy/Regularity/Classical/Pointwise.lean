/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.TimeDerivatives
public import PDE.Spaces.Sobolev.Fractional.Integer.ClassicalRepresentation
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Pointwise derivatives of Sobolev wave curves

Evaluation of the canonical continuous representative carries a strong Sobolev time derivative
to a derivative at every spatial point: if `r ↦ u r`, read at a lower Sobolev order `k`, has the
derivative `v`, then `r ↦ (u r) x` has the derivative `v x` for every `x`
(`hasDerivWithinAt_classicalRepresentative_lowerOrder` within a set,
`hasDerivAt_classicalRepresentative_lowerOrder` at an interior time). Both orders lie above the
classical Sobolev threshold `n < 2 (k - 1)`.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k j : ℕ}

/-- Evaluation of a lower-order Sobolev time derivative differentiates the
canonical higher-order representative at every spatial point. -/
theorem hasDerivWithinAt_classicalRepresentative_lowerOrder (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hj : (n : ℝ) < 2 * ((j : ℝ) - 1)) (hkj : k ≤ j) {u : ℝ → W^{j,2}(ℝ^n)} {v : W^{k,2}(ℝ^n)}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt (fun r ↦ lowerOrderCLM hkj (u r)) v s t) (x : ℝ^n) :
    HasDerivWithinAt (fun r ↦ classicalRepresentativeCLM hj (u r) x)
      (classicalRepresentativeCLM hk v x) s t := by
  have hd := ((BoundedContinuousFunction.evalCLM ℝ x).comp
    (classicalRepresentativeCLM hk)).hasFDerivAt.comp_hasDerivWithinAt t h
  change HasDerivWithinAt (fun r ↦ classicalRepresentativeCLM hk (lowerOrderCLM hkj (u r)) x)
    (classicalRepresentativeCLM hk v x) s t at hd
  simpa only [classicalRepresentativeCLM_lowerOrderCLM hk hj hkj] using hd

/-- The interior version evaluates a Sobolev time derivative. -/
theorem hasDerivAt_classicalRepresentative_lowerOrder (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hj : (n : ℝ) < 2 * ((j : ℝ) - 1)) (hkj : k ≤ j) {u : ℝ → W^{j,2}(ℝ^n)} {v : W^{k,2}(ℝ^n)}
    {t : ℝ} (h : HasDerivAt (fun r ↦ lowerOrderCLM hkj (u r)) v t) (x : ℝ^n) :
    HasDerivAt (fun r ↦ classicalRepresentativeCLM hj (u r) x)
      (classicalRepresentativeCLM hk v x) t :=
  (hasDerivWithinAt_classicalRepresentative_lowerOrder hk hj hkj
    (s := univ) h.hasDerivWithinAt x).hasDerivAt Filter.univ_mem

end PDE.Hyperbolic.NonlinearWave.Cauchy
