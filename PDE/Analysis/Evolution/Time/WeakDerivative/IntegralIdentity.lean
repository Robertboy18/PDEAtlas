/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative

/-!
# Integral identities for continuous weakly differentiable curves

Continuity identifies a prescribed curve with the representative supplied by
its weak derivative. The fundamental theorem therefore holds for the prescribed
values at both endpoints, without choosing a second time representative.
-/

@[expose] public section

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

open MeasureTheory Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A continuous curve satisfies the fundamental theorem with its integrable
weak derivative at every pair of times in the closed interval. -/
theorem integral_eq_sub_of_continuousOn
    {a b : ℝ} (hab : a < b) {u g : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g)
    (hu : ContinuousOn u (Icc a b)) (hg : IntegrableOn g (Ioo a b))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ r in s..t, g r) = u t - u s := by
  obtain ⟨v, hv, hae, hFTC⟩ := hweak.exists_continuous_representative_Icc hab hg
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne
    ((ae_restrict_congr_set Ioo_ae_eq_Icc).mp hae) hu hv.continuousOn
  rw [heq ht, heq hs]
  exact (hFTC s hs t ht).symm

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
