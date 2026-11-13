/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.TimeDerivatives

/-!
# Pointwise derivatives of Sobolev wave curves

Evaluation of the canonical representative carries strong Sobolev time
derivatives to derivatives at every spatial point. For the saturating
reaction, the represented acceleration is the classical Laplacian minus the
pointwise reaction. The joint regularity and existence arguments use these
identifications in the subsequent modules.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

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

variable [NeZero n]

/-- The higher acceleration is the classical Laplacian minus the
pointwise reaction, with no exceptional spatial set. -/
theorem classicalRepresentative_higherSaturatingAcceleration (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (q : W^{k + 2,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherSaturatingAcceleration hk q) x =
      Δ (classicalRepresentativeCLM hq q : ℝ^n → ℝ) x -
        saturatingReaction (classicalRepresentativeCLM hq q x) := by
  rw [higherSaturatingAcceleration, map_sub, BoundedContinuousFunction.sub_apply,
    classicalRepresentative_higherComposition, classicalRepresentativeCLM_lowerOrderCLM hk hq,
    laplacian_classicalRepresentative hq hk le_rfl]

end PDE.Hyperbolic.NonlinearWave.Cauchy
