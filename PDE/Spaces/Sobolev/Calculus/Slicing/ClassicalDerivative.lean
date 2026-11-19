/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Classical representatives of extracted Sobolev derivatives

If the base of a Sobolev graph agrees almost everywhere with a sufficiently smooth
function, weak-derivative uniqueness identifies each extracted derivative word
with its classical derivative on an open domain.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Distributions Sobolev

/-- Extracting a derivative word from a Sobolev graph agrees almost everywhere
with the classical derivative of any representative smooth through that order.
The remaining graph order and the exponent are arbitrary. -/
theorem baseRepresentative_derivativeWordCLM_ae
    {n k m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (U : W^{m,p}(Ω)) (f : ℝ^n → ℝ)
    (α : List (Fin n)) (hα : α.length + k ≤ m)
    (hf : ContDiff ℝ (α.length : ℕ∞) f)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n Ω] f) :
    baseRepresentative (derivativeWordCLM α hα U)
      =ᵐ[domainMeasure n Ω] iteratedPartialDeriv α f := by
  have hw : HasWeakDerivativeOn Ω α (baseRepresentative U)
      (baseRepresentative (derivativeWordCLM α hα U)) := by
    rw [baseRepresentative_derivativeWordCLM]
    exact U.property.hasWeakDerivativeOn_list α (by omega)
  have hc := (hasWeakDerivativeOn_congr_ae hbase.symm Filter.EventuallyEq.rfl).mp
    (hasWeakDerivativeOn_iteratedPartialDeriv_finite (Ω := Ω) α hf)
  exact hw.unique_ae hΩ hc

end SobolevSpace.GraphSpace
