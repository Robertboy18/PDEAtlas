/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.ContinuousEmbedding
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Classical representatives of integer whole-space Sobolev functions

The integer-to-Bessel equivalence and Fourier reconstruction give a bounded
linear representative map into bounded continuous functions. These representatives
are unique, agree under restriction of Sobolev order, and have every classical
derivative allowed by the higher Sobolev threshold.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open scoped Sobolev BoundedContinuousFunction

namespace SobolevSpace.GraphSpace

variable {n k : ℕ}

/-- The canonical bounded continuous representative of an integer Sobolev datum. -/
def classicalRepresentativeCLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    W^{k,2}(ℝ^n) →L[ℝ] (ℝ^n →ᵇ ℝ) :=
  (Fractional.HsSpaceReal.c1RepresentativeCLM hk).comp
    (Fractional.ofWkpSpaceRealCLM n k)

/-- The canonical integer representative realizes the base weak-derivative row. -/
theorem classicalRepresentativeCLM_ae (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) :
    (classicalRepresentativeCLM hk u : ℝ^n → ℝ) =ᵐ[volume] baseRepresentative u := by
  have hrep := Fractional.c1Representative_ae_eq_toL2Fun
    hk (Nat.cast_nonneg k) (Fractional.ofWkpSpace u)
  have hbase := Fractional.reOfL2_toL2Fun_ofWkpSpace u
  filter_upwards [hrep, hbase] with x hx hy
  exact (congrArg Complex.re hx).trans hy

/-- Above the higher threshold, the canonical representative is classically Cʳ. -/
theorem contDiff_classicalRepresentativeCLM {r : ℕ}
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hr : (n : ℝ) < 2 * ((k : ℝ) - r)) (u : W^{k,2}(ℝ^n)) :
    ContDiff ℝ r (classicalRepresentativeCLM hk u : ℝ^n → ℝ) :=
  Fractional.HsSpaceReal.contDiff_c1RepresentativeCLM_of_order hk hr
    (Fractional.ofWkpSpaceRealCLM n k u)

/-- Any continuous representative of the base row agrees everywhere with the
canonical one. -/
theorem eq_classicalRepresentativeCLM_of_ae_eq
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u : W^{k,2}(ℝ^n))
    {v : ℝ^n → ℝ} (hv : Continuous v) (h : v =ᵐ[volume] baseRepresentative u) :
    v = classicalRepresentativeCLM hk u :=
  Measure.eq_of_ae_eq (h.trans (classicalRepresentativeCLM_ae hk u).symm)
    hv (classicalRepresentativeCLM hk u).continuous

/-- Restricting Sobolev order leaves the actual representative unchanged. -/
theorem classicalRepresentativeCLM_lowerOrderCLM {j : ℕ}
    (hj : (n : ℝ) < 2 * ((j : ℝ) - 1))
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hjk : j ≤ k) (u : W^{k,2}(ℝ^n)) :
    classicalRepresentativeCLM hj (lowerOrderCLM hjk u) =
      classicalRepresentativeCLM hk u := by
  apply DFunLike.coe_injective
  symm
  apply eq_classicalRepresentativeCLM_of_ae_eq hj _
    (classicalRepresentativeCLM hk u).continuous
  simpa only [baseRepresentative_lowerOrderCLM] using classicalRepresentativeCLM_ae hk u

/-- A continuous Sobolev trajectory has jointly continuous point values. -/
theorem continuous_classicalRepresentativeCLM
    {T : Type*} [TopologicalSpace T] (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    {u : T → W^{k,2}(ℝ^n)} (hu : Continuous u) :
    Continuous (fun p : T × ℝ^n ↦ classicalRepresentativeCLM hk (u p.1) p.2) :=
  continuous_eval.comp
    (((classicalRepresentativeCLM hk).continuous.comp hu).comp continuous_fst |>.prodMk
      continuous_snd)

end SobolevSpace.GraphSpace
