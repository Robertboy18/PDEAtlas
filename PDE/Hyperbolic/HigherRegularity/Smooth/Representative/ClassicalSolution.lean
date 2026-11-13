/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Definition
public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.ClassicalEquation
public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.InitialTraces
public import PDE.Spaces.Sobolev.Evolution.Classical.Boundary

/-!
# Recovering the classical wave problem from the original weak solution

The scalar equation, closed lateral boundary values and initial traces
all belong to the same joint representative. This identifies the complete
classical problem once smoothness of that representative has been established.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- A joint smooth representative of an original weak wave satisfies the
classical PDE and all prescribed data, with no extra endpoint assumptions. -/
theorem isClassicalSolution_of_weakWave (P : SmoothFullCoefficients n Ω) (hn : 0 < n)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hab : a < b) {f U : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
    (hg : ∀ k, ContDiffUpToBoundary k g Ω) (hh : ∀ k, ContDiffUpToBoundary k h Ω)
    (hU : ∀ k, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
    (hcont : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))} {q₀ : H¹₀(Ω)}
    {p₀ : DerivLp n 2 Ω}
    (hweak : Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      (dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 0).head) u v w q₀ p₀)
    (hq₀ : baseCoordCLM q₀ =
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 1 0))
    (hp₀ : p₀ = wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 0 1))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b), (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
      baseRepresentative (h10SubtypeL (u t))) :
    IsClassicalSolution P hopen hf hg hh U := by
  let : Fact (0 < n) := ⟨hn⟩
  refine ⟨hcont, hU, ?_, ?_, ?_, ?_⟩
  · exact fun t ht x hx ↦ classical_equation P hopen hbounded hab hf hU hcont hweak hae ht hx
  · exact eq_zero_on_lateral_boundary hopen hbounded hgraph hab (fun t ↦ u t) hcont hae
  · intro x hx
    rw [← derivativeSlice_nil hopen hab hU hcont ⟨le_rfl, hab.le⟩ hx]
    exact initial_derivativeSlice_eq P hopen hbounded hab hf hg hh hU hcont hweak hq₀ hp₀ hae 0 hx
  · exact fun x hx ↦ initial_derivativeSlice_eq P hopen hbounded hab hf hg hh hU hcont
      hweak hq₀ hp₀ hae 1 hx

end Hyperbolic.HigherRegularity.SmoothWave
