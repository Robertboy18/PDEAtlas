/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Elliptic.GreenFunction.Corrector.AnnulusGeometry
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Reciprocity
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Uniqueness

/-!
# Choice-independent correctors on the annulus

The uniqueness theorem `exists_unique_harmonic_corrector_of_local_graph` gives the
corrector at `pole` and shows that every continuous classical corrector equals it on
the closed annulus (`constructed_corrector_independent`). The classical corrector need
not come from a Sobolev representative. Any two classical correctors at `pole` and
`otherPole` satisfy Green reciprocity (`classical_corrector_reciprocity`).
-/

@[expose] public section

namespace PDE.Examples.GreenCorrectorAnnulus

open Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open PotentialTheory.GreenFunction.Domain
open scoped ENNReal Sobolev

/-- The corrector at `pole` exists, and every continuous classical corrector with the same
boundary values equals it on the closed annulus. -/
theorem constructed_corrector_independent :
    ∃ U : H¹(domain), ∃ φ : ℝ^2 → ℝ,
      baseRepresentative U =ᵐ[domainMeasure 2 domain] φ ∧
      LaplacianEquation.IsHarmonicPDE 2 φ domain ∧
      ContinuousOn φ (closure domain) ∧
      EqOn φ (fun y ↦ PotentialTheory.fundamentalSolution 2 (y - pole)) (frontier domain) ∧
      ∀ ψ : ℝ^2 → ℝ,
        LaplacianEquation.IsHarmonicPDE 2 ψ domain →
        ContinuousOn ψ (closure domain) →
        EqOn ψ (fun y ↦ PotentialTheory.fundamentalSolution 2 (y - pole)) (frontier domain) →
        EqOn ψ φ (closure domain) :=
  exists_unique_harmonic_corrector_of_local_graph (by norm_num : 2 ≤ 1 + 1)
    isOpen_domain isBounded_domain
    (hasContDiffGraphBoundary_domain.hasC1GraphBoundary le_top) pole_mem

/-- Classical correctors at `pole` and `otherPole` satisfy Green reciprocity. -/
theorem classical_corrector_reciprocity {φ ψ : ℝ^2 → ℝ}
    (hφ : LaplacianEquation.IsHarmonicPDE 2 φ domain)
    (hψ : LaplacianEquation.IsHarmonicPDE 2 ψ domain)
    (hcφ : ContinuousOn φ (closure domain)) (hcψ : ContinuousOn ψ (closure domain))
    (hbφ : EqOn φ (fun z ↦ PotentialTheory.fundamentalSolution 2 (z - pole))
      (frontier domain))
    (hbψ : EqOn ψ (fun z ↦ PotentialTheory.fundamentalSolution 2 (z - otherPole))
      (frontier domain)) :
    PotentialTheory.fundamentalSolution 2 (otherPole - pole) - φ otherPole =
      PotentialTheory.fundamentalSolution 2 (pole - otherPole) - ψ pole :=
  green_eq_swap_of_classical_correctors (by norm_num : 2 ≤ 1 + 1)
    isOpen_domain isBounded_domain
    (hasContDiffGraphBoundary_domain.hasC1GraphBoundary le_top)
    pole_mem otherPole_mem hφ hψ hcφ hcψ hbφ hbψ

end PDE.Examples.GreenCorrectorAnnulus
