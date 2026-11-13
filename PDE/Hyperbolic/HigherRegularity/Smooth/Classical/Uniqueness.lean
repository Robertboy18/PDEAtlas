/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.WeakSolution.Construction
public import PDE.Hyperbolic.WeakWave.Autonomous.ClassicalCoefficients
public import PDE.Analysis.Evolution.Classical.Uniqueness

/-!
# Uniqueness on the entire closed wave cylinder

Every classical competitor determines a wave in the original weak class with
the prescribed initial data. Energy uniqueness identifies those weak waves;
continuity identifies the two classical functions on the whole closed cylinder.
Values outside that cylinder are immaterial.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Two smooth classical waves with the same data agree on the closed
cylinder, for the full signed operator with symmetric elliptic principal part. -/
theorem IsClassicalSolution.eqOn {P : SmoothFullCoefficients n Ω} (hn : 0 < n) {hopen : IsOpen Ω}
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) {f U V : SpaceTime n → ℝ}
    {g h : ℝ^n → ℝ} {hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))}
    {hg : ∀ k, ContDiffUpToBoundary k g Ω} {hh : ∀ k, ContDiffUpToBoundary k h Ω}
    (hU : IsClassicalSolution P hopen hf hg hh U) (hV : IsClassicalSolution P hopen hf hg hh V) :
    EqOn U V (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  obtain ⟨u, v, w, q₀, p₀, hw, hu, hq, hp⟩ := hU.exists_weakWave hn hbounded hgraph hab
  obtain ⟨u', v', w', q₀', p₀', hw', hu', hq', hp'⟩ := hV.exists_weakWave hn hbounded hgraph hab
  have hqeq : q₀ = q₀' := baseCoordCLM_injective hopen (Lp.ext (hq.trans hq'.symm))
  have hpeq : p₀ = p₀' := Lp.ext (hp.trans hp'.symm)
  subst q₀'
  subst p₀'
  have he : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, P.principal x i j * ξ j * ξ i := by
    intro x hx ξ
    simpa only [principalEnergy, dotProduct, mul_right_comm] using hell x hx ξ
  have heq := weakWave_eq_of_classical_autonomous_coefficients hn hopen hbounded
    (P.principal_smooth 1) (P.drift_smooth 1) (P.potential_smooth 0) hsymm halpha he hw hw'
  apply PDE.Analysis.Evolution.eqOn_closed_spaceTime_cylinder_of_ae_eq hopen hab
    hU.continuous hV.continuous
  filter_upwards [hu, hu'] with t ht ht'
  rw [heq.1] at ht
  exact ht.trans ht'.symm

end Hyperbolic.HigherRegularity.SmoothWave
