/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder

/-!
# Sobolev representatives from interior classical regularity

A function which is `C^k` only on the open domain defines a Sobolev element
as soon as its classical derivative rows belong to `Lᵖ`. This is useful for boundary
singularities: no differentiability on, or extension through, the boundary is required.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set ℝ^n}

/-- Interior classical derivatives with finite `Lᵖ` norms reconstruct all
Sobolev coordinates simultaneously. -/
theorem exists_of_contDiffOn_memLp (hΩ : IsOpen Ω)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f Ω)
    (hmem : ∀ a : DerivIndex n k,
      MemLp (iteratedPartialDeriv a.toList f) p (domainMeasure n Ω)) :
    ∃ U : W^{k,p}(Ω), ∀ a : DerivIndex n k,
      (U.val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] iteratedPartialDeriv a.toList f := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦ iteratedPartialDeriv a.toList f
  have hbase : d (baseIndex n k) = f := by
    simp only [d, baseIndex_toList, iteratedPartialDeriv]
  have hweak (a : DerivIndex n k) : HasWeakDerivativeOn Ω a.toList f (d a) :=
    hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn hΩ hf a.toList a.toList_length_le
  exact ⟨mkWkpSpaceOnOfWeakDerivatives f d hbase hmem hweak,
    mkWkpSpaceOnOfWeakDerivatives_apply_ae f d hbase hmem hweak⟩

end SobolevSpace.GraphSpace
