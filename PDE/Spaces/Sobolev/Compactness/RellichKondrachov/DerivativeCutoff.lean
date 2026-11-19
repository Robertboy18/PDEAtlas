/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.ClassicalDerivative
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Cutoff

/-!
# Compact observations of Sobolev derivative words

A derivative word leaving at least one Sobolev derivative can be localized by
a smooth compactly supported cutoff and observed in Lp. This map is compact for
finite p. Its representative is the cutoff times the weak derivative, or the
classical derivative when a sufficiently smooth base representative is known.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory TopologicalSpace
open scoped ENNReal Distributions Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Lp observation of a derivative word multiplied by a test function.
One remaining Sobolev derivative supplies compactness after localization. -/
def cutoffDerivativeCLM (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{m,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
  (wkpBaseCoordinateCLM.comp (cutoffCLM (Ω := Set.univ) χ)).comp
    (derivativeWordCLM α hα)

/-- The cutoff observation represents the cutoff times the extracted weak derivative. -/
theorem cutoffDerivativeCLM_ae
    (U : W^{m,p}(ℝ^n)) (α : List (Fin n))
    (hα : α.length + 1 ≤ m) (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (cutoffDerivativeCLM α hα χ U : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ χ x * baseRepresentative (derivativeWordCLM α hα U) x := by
  simpa only [cutoffDerivativeCLM, ContinuousLinearMap.comp_apply,
    wkpBaseCoordinateCLM_apply, baseRepresentative, TestFunction.toFun_eq_coe,
    domainMeasure, Measure.restrict_univ] using
      cutoffCLM_base_apply_ae χ (derivativeWordCLM α hα U)

/-- For a base representative smooth through the word length, the cutoff
observation agrees almost everywhere with its localized classical derivative. -/
theorem cutoffDerivativeCLM_ae_of_contDiff
    (U : W^{m,p}(ℝ^n)) (f : ℝ^n → ℝ)
    (hrep : f =ᵐ[volume] baseRepresentative U)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (hf : ContDiff ℝ (α.length : ℕ∞) f) (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (cutoffDerivativeCLM α hα χ U : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ χ x * iteratedPartialDeriv α f x := by
  have hbase : baseRepresentative U =ᵐ[domainMeasure n Set.univ] f := by
    simpa only [domainMeasure, Measure.restrict_univ] using hrep.symm
  have hderiv : baseRepresentative (derivativeWordCLM α hα U) =ᵐ[volume]
      iteratedPartialDeriv α f := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      baseRepresentative_derivativeWordCLM_ae isOpen_univ U f α hα hf hbase
  filter_upwards [cutoffDerivativeCLM_ae U α hα χ, hderiv] with x hx hfx
  exact hx.trans (congrArg (χ x * ·) hfx)

/-- A cutoff derivative observation is compact whenever the spatial exponent is finite. -/
theorem cutoffDerivativeCLM_isCompactOperator (hp : p ≠ ∞)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    IsCompactOperator (cutoffDerivativeCLM (p := p) α hα χ) :=
  (RellichKondrachov.cutoffBaseCoordinate_isCompactOperator hp χ).comp_clm
    (derivativeWordCLM α hα)

end SobolevSpace.GraphSpace
