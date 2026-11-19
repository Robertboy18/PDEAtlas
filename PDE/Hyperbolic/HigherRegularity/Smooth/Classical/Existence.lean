/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Regularity

/-!
# Existence of a smooth Dirichlet wave from compatible smooth data

The energy existence theorem supplies a weak wave for the canonical forcing
and initial data. Infinite regularity of that same wave supplies a single
classical solution of the original full equation.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Smooth compatible data admit a joint classical wave for arbitrary
signed lower-order coefficients and symmetric uniformly elliptic principal part. -/
theorem exists_classicalSolution (P : SmoothFullCoefficients n Ω) (hn : 0 < n) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    (hab : a < b) (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i) {alpha : ℝ}
    (halpha : 0 < alpha) (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    {f : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
    (hg : ∀ k, ContDiffUpToBoundary k g Ω) (hh : ∀ k, ContDiffUpToBoundary k h Ω)
    (hcompat : HasCompatibleBoundaryValues P hopen hbounded hab hf hg hh) :
    ∃ U : SpaceTime n → ℝ, IsClassicalSolution P hopen hf hg hh U := by
  have he : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, P.principal x i j * ξ j * ξ i := by
    intro x hx ξ
    simpa only [principalEnergy, dotProduct, mul_right_comm] using hell x hx ξ
  obtain ⟨_, _, henergy⟩ := exists_uniform_energy_bound_of_classical_autonomous_coefficients
    hn hopen hbounded hab (P.principal_smooth 1) (P.drift_smooth 1)
    (P.potential_smooth 0) hsymm halpha he
  let hD := problemData_hasCompatibleBoundaryTraces P hopen hbounded hab hf hg hh
    hn ((hgraph 1).hasC1GraphBoundary le_rfl) hcompat 0 0
  obtain ⟨u, v, w, hweak⟩ :=
    (henergy (baseCoordinateTimeLp (forcingJet hopen hbounded hab hf 0 0).head)
      (WaveProblemData.initialPosition hD)
      (wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 0 1))).1
  obtain ⟨U, hU, _⟩ := exists_classicalSolution_of_weakWave P hn hopen hbounded hgraph
    hab hsymm halpha hell hf hg hh hcompat u v w hweak
  exact ⟨U, hU⟩

end Hyperbolic.HigherRegularity.SmoothWave
