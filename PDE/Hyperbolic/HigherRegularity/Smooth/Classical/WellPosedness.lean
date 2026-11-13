/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Existence
public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Uniqueness
public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Values

/-!
# Smooth Dirichlet wave well-posedness from compatible smooth data

Smooth data satisfying every recursively computed compatibility condition admit one classical
solution on the closed cylinder, as in Evans, §7.2.3, Theorem 7. Uniqueness is equality on that
cylinder, established by converting every classical competitor into the original weak class. The
autonomous operator keeps its full signed drift and potential; only its principal matrix is
symmetric and uniformly elliptic.

## How it works

For existence (`exists_classicalSolution`), we solve the weak problem for the canonical forcing and
initial data with `exists_uniform_energy_bound_of_classical_autonomous_coefficients`, and
`exists_classicalSolution_of_weakWave` shows that this weak wave has a classical representative.
For uniqueness (`IsClassicalSolution.eqOn`), `IsClassicalSolution.exists_weakWave` turns each
classical solution into a wave in the original weak class with the same initial data. Then
`weakWave_eq_of_classical_autonomous_coefficients` identifies the two weak waves, and since both
classical functions are continuous, they agree on the whole closed cylinder.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Smooth compatible data admit a unique joint smooth classical wave
on the closed cylinder, without a supplied solution or regularity family. -/
theorem exists_unique_classicalSolution (P : SmoothFullCoefficients n Ω) (hn : 0 < n)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) {f : SpaceTime n → ℝ}
    {g h : ℝ^n → ℝ} (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
    (hg : ∀ k, ContDiffUpToBoundary k g Ω) (hh : ∀ k, ContDiffUpToBoundary k h Ω)
    (hcompat : HasCompatibleBoundaryValues P hopen hbounded hab hf hg hh) :
    ∃ U : SpaceTime n → ℝ, IsClassicalSolution P hopen hf hg hh U ∧
      ∀ V : SpaceTime n → ℝ, IsClassicalSolution P hopen hf hg hh V →
        EqOn U V (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  obtain ⟨U, hU⟩ := exists_classicalSolution P hn hopen hbounded hgraph hab
    hsymm halpha hell hf hg hh hcompat
  exact ⟨U, hU, fun _ hV ↦ hU.eqOn hn hbounded
    ((hgraph 1).hasC1GraphBoundary le_rfl) hab hsymm halpha hell hV⟩

end Hyperbolic.HigherRegularity.SmoothWave
