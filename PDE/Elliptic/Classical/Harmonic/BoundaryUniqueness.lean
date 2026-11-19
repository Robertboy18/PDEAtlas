/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple.BoundedDomain

/-!
# Uniqueness from continuous harmonic boundary values

The proof applies bounded-domain harmonic comparison to both differences. No
connectedness, boundary smoothness or Sobolev membership is needed.
-/

@[expose] public section

namespace LaplacianEquation

open Set

/-- Harmonic functions continuous on the closure of a bounded open domain agree
on that closure whenever they have the same boundary values. -/
theorem IsHarmonicPDE.eqOn_closure_of_boundary_eq
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} {u v : ℝ^n → ℝ}
    (hu : IsHarmonicPDE n u Ω) (hv : IsHarmonicPDE n v Ω)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hb : EqOn u v (frontier Ω)) :
    EqOn u v (closure Ω) := by
  have huv := (hu.sub hv hΩ).le_on_closure_of_boundary_le hΩ hbounded
    (huc.sub hvc) (M := 0) (fun x hx ↦ by
      change u x - v x ≤ 0
      exact sub_nonpos.mpr (hb hx).le)
  have hvu := (hv.sub hu hΩ).le_on_closure_of_boundary_le hΩ hbounded
    (hvc.sub huc) (M := 0) (fun x hx ↦ by
      change v x - u x ≤ 0
      exact sub_nonpos.mpr (hb hx).ge)
  intro x hx
  exact le_antisymm (sub_nonpos.mp (huv x hx)) (sub_nonpos.mp (hvu x hx))

end LaplacianEquation
