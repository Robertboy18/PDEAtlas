/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.ZeroOrder

/-!
# The physical Lp action of relative cutoff multiplication

The Banach-valued relative multiplier extends a localized Sobolev
function across the artificial edge of a chart. Its order-zero instance defines
the bounded `Lp` companion. The physical base action is the same at every order,
including when the cutoff meets the boundary of the physical domain.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {V Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The `Lp` companion of the relative cutoff multiplier. -/
def interMultiplierLp (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    Lp F p (domainMeasure n (V ⊓ Ω)) →L[ℝ] Lp F p (domainMeasure n Ω) :=
  let source := (lpEquivZeroOrder (Ω := V ⊓ Ω) (F := F) (p := p)).toContinuousLinearEquiv
  let target := (lpEquivZeroOrder (Ω := Ω) (F := F) (p := p)).symm.toContinuousLinearEquiv
  target.toContinuousLinearMap.comp
    ((interMultiplier (Ω := Ω) (V := V) (F := F) (p := p) (k := 0) ψ hψ).comp
      source.toContinuousLinearMap)

/-- Relative cutoff multiplication retains its physical formula for every supplied
representative on the chart intersection. -/
theorem interMultiplierLp_apply_ae
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (u : Lp F p (domainMeasure n (V ⊓ Ω))) {f : ℝ^n → F}
    (hu : (u : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] f) :
    (interMultiplierLp ψ hψ u : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ ψ.toFun x • f x :=
  interMultiplier_base_ae ψ hψ (lpEquivZeroOrder u) hu

/-- Every order of the relative Sobolev multiplier uses the same bounded `Lp` base map. -/
theorem interMultiplier_base_eq
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) :
    coordinateCLM (baseIndex n k) (interMultiplier ψ hψ U) =
      interMultiplierLp ψ hψ (coordinateCLM (baseIndex n k) U) := by
  apply Lp.ext
  exact (interMultiplier_base_ae ψ hψ U Filter.EventuallyEq.rfl).trans
    (interMultiplierLp_apply_ae ψ hψ (U.val (baseIndex n k))
      Filter.EventuallyEq.rfl).symm

end SobolevSpace.VectorValued.GeometricExtension
