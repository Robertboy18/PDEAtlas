/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability -- shake: keep

/-!
# The canonical fundamental-solution distribution

The locally integrable Euclidean Laplace kernel defines a regular distribution
in every dimension.  Distributional pole identities are proved in
dimension-specific modules and use this common construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace PotentialTheory

/-- The regular distribution induced by the canonical Laplace fundamental
solution on `ℝ^n`. Local integrability gives the integral formula in
`fundamentalSolutionDistribution_apply`. -/
noncomputable def fundamentalSolutionDistribution
    (n : ℕ) :
    𝓓'((⊤ : Opens (ℝ^n)), ℝ) :=
  Distribution.ofFun ⊤ (fundamentalSolution n) volume ⊤

/-- The canonical kernel distribution acts by integration against its
density. -/
@[simp]
theorem fundamentalSolutionDistribution_apply
    (n : ℕ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    fundamentalSolutionDistribution n φ =
      ∫ x : ℝ^n, φ x * fundamentalSolution n x := by
  rw [fundamentalSolutionDistribution,
    Distribution.ofFun_apply
      ((locallyIntegrable_fundamentalSolution n).locallyIntegrableOn univ)]
  simp only [smul_eq_mul]

end PotentialTheory
