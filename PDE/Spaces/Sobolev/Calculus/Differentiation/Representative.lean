/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Classical representatives of Sobolev derivative coordinates

If the base coordinate of a Sobolev graph has a classical representative
on an open set, uniqueness of weak derivatives identifies every graph
coordinate with the corresponding classical derivative. Regularity
outside the domain is unnecessary.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- A `C^k` representative of the base coordinate identifies every weak derivative
through order `k` almost everywhere with its classical derivative. -/
theorem wkpCoordinate_ae_eq_iteratedPartialDeriv_of_contDiffOn
    (hΩ : IsOpen Ω) (U : W^{k,p}(Ω)) {f : ℝ^n → ℝ}
    (hf : ContDiffOn ℝ k f Ω)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n Ω] f) (a : DerivIndex n k) :
    wkpCoordinateCLM a U =ᵐ[domainMeasure n Ω] iteratedPartialDeriv a.toList f := by
  exact ((U.property a).congr_ae hbase (Filter.EventuallyEq.refl _ _)).unique_ae hΩ
    (hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn hΩ hf a.toList a.toList_length_le)

/-- The first weak coordinate equals the partial derivative of a `C¹`
representative, independently of the representatives chosen for the `Lᵖ` classes. -/
theorem wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn
    (hΩ : IsOpen Ω) (U : W^{1,p}(Ω)) {f : ℝ^n → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n Ω] f) (i : Fin n) :
    wkpCoordinateCLM (singleDerivIndex n i) U =ᵐ[domainMeasure n Ω] ∂[i] f := by
  simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using
    wkpCoordinate_ae_eq_iteratedPartialDeriv_of_contDiffOn hΩ U hf hbase (singleDerivIndex n i)

end SobolevSpace.GraphSpace
