/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Bounded assembly of local Sobolev errors

Multiplication by a fixed smooth cutoff supported in a patch sends
`W^{k,p}(V ∩ Ω)` continuously into `W^{k,p}(Ω)`, for every finite order and `p ≥ 1`.
The scalar identification specializes the Banach-valued relative multiplier,
preserving its derivative coordinates and Sobolev norm. This is the local
assembly operator used in Evans §5.3.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268, for approximation by
  functions smooth up to a C¹ boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped Distributions ENNReal NNReal Topology Sobolev

namespace SobolevSpace.Approximation.UpToBoundary

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Boundary-relative cutoff multiplication is bounded on every Sobolev order. -/
def interMultiplier {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    W^{k,p}((V ∩ Ω)) →L[ℝ] W^{k,p}(Ω) :=
  let I := VectorValued.scalarEquiv (k := k) (p := p)
    (Ω := (⟨V, hV⟩ : Opens ℝ^n) ⊓ ⟨Ω, hΩ⟩)
  (VectorValued.scalarEquiv (Ω := ⟨Ω, hΩ⟩)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((VectorValued.interMultiplier (V := ⟨V, hV⟩) (Ω := ⟨Ω, hΩ⟩) ψ hψ).comp
      I.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Representative formula for bounded assembly. -/
theorem interMultiplier_base_ae {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) {f : ℝ^n → ℝ}
    (hU : baseRepresentative U =ᵐ[domainMeasure n (V ∩ Ω)] f) :
    baseRepresentative (interMultiplier hV hΩ ψ hψ U) =ᵐ[domainMeasure n Ω]
      fun x ↦ ψ.toFun x * f x := by
  exact VectorValued.interMultiplier_base_ae
    (V := ⟨V, hV⟩) (Ω := ⟨Ω, hΩ⟩) ψ hψ (VectorValued.scalarEquiv.symm U) hU

end SobolevSpace.Approximation.UpToBoundary
