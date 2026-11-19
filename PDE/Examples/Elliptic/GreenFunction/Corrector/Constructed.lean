/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Elliptic.GreenFunction.Corrector.AnnulusGeometry
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Reciprocity
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Representation
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Constructed Green kernels on a nonconvex annulus

The correctors of the logarithmic fundamental solution on the annulus are the
Dirichlet solutions of `exists_reciprocal_harmonic_correctors_of_local_graph`. At the
poles `pole` and `otherPole` they satisfy Green reciprocity
(`constructed_weak_reciprocity`). For the polynomial `profile`, with `Δ profile = 4` and
nonzero boundary values, the Green representation formula
`exists_corrector_dirichlet_representation_of_higher_graph` recovers the value
`profile pole = 27/4` (`constructed_classical_representation`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.GreenCorrectorAnnulus

open Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 Geometry.SurfaceMeasure PotentialTheory.GreenFunction.Domain
open scoped ENNReal Sobolev Gradient

/-- The harmonic correctors at `pole` and `otherPole` give a Green function with
`G(pole, otherPole) = G(otherPole, pole)`. -/
theorem constructed_weak_reciprocity :
    ∃ U V : H¹(domain), ∃ φ ψ : ℝ^2 → ℝ,
      baseRepresentative U =ᵐ[domainMeasure 2 domain] φ ∧
      baseRepresentative V =ᵐ[domainMeasure 2 domain] ψ ∧
      LaplacianEquation.IsHarmonicPDE 2 φ domain ∧
      LaplacianEquation.IsHarmonicPDE 2 ψ domain ∧
      ContinuousOn φ (closure domain) ∧ ContinuousOn ψ (closure domain) ∧
      EqOn φ (fun y ↦ PotentialTheory.fundamentalSolution 2 (y - pole)) (frontier domain) ∧
      EqOn ψ (fun y ↦ PotentialTheory.fundamentalSolution 2 (y - otherPole))
        (frontier domain) ∧
      PotentialTheory.fundamentalSolution 2 (otherPole - pole) - φ otherPole =
        PotentialTheory.fundamentalSolution 2 (pole - otherPole) - ψ pole := by
  obtain ⟨U, φ, hφ, hsym⟩ := exists_reciprocal_harmonic_correctors_of_local_graph
    (by norm_num : 2 ≤ 1 + 1) isOpen_domain isBounded_domain
    (hasContDiffGraphBoundary_domain.hasC1GraphBoundary le_top)
  let x : domain := ⟨pole, pole_mem⟩
  let y : domain := ⟨otherPole, otherPole_mem⟩
  exact ⟨U x, U y, φ x, φ y, (hφ x).1, (hφ y).1, (hφ x).2.1, (hφ y).2.1,
    (hφ x).2.2.1, (hφ y).2.2.1, (hφ x).2.2.2.1, (hφ y).2.2.2.1, hsym x y⟩

/-- The polynomial `3 + z₀ + z₀² + z₁²`, with source `-Δ profile = -4`. -/
def profile (z : ℝ^2) : ℝ := 3 + z 0 + z 0 ^ 2 + z 1 ^ 2

/-- `Δ profile = 4`. -/
theorem laplacian_profile (z : ℝ^2) : laplacian profile z = 4 := by
  unfold profile
  cas

/-- `profile` equals `27/4` at `pole` and `21/4` at `otherPole`. -/
theorem profile_poles :
    profile pole = 27 / 4 ∧ profile otherPole = 21 / 4 := by
  norm_num [profile, pole, otherPole, PiLp.single_apply]

/-- The Green representation formula for `profile` at `pole`: the boundary term plus the
volume term equal `profile pole = 27/4`. -/
theorem constructed_classical_representation :
    let hgraph : HasContDiffGraphBoundary 5 domain :=
      hasContDiffGraphBoundary_domain.of_le le_top
    ∃ φ : ℝ^2 → ℝ, ∃ hφ : ContDiffUpToBoundary 2 φ domain,
      ContinuousOn φ (closure domain) ∧ LaplacianEquation.IsHarmonicPDE 2 φ domain ∧
      EqOn φ (fun y ↦ PotentialTheory.fundamentalSolution 2 (y - pole)) (frontier domain) ∧
      letI := (hgraph.hasC1GraphBoundary (by norm_num)).c1ExtensionAtlas
        isOpen_domain isBounded_domain
      let G := fun y ↦ PotentialTheory.fundamentalSolution 2 (y - pole) - φ y
      let DG := fun y ↦ ∇
          (fun z ↦ PotentialTheory.fundamentalSolution 2 (z - pole)) y -
        (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient y
      IntegrableOn (fun y ↦ (-4) * G y) domain ∧
        Integrable (fun y ↦ profile y * normalFlux (Ω := domain) DG y)
          (surfaceMeasure domain) ∧
        (27 / 4 : ℝ) =
          -(∫ y, profile y * normalFlux (Ω := domain) DG y ∂surfaceMeasure domain) +
            ∫ y in domain, (-4) * G y := by
  dsimp only
  have hu : ContDiff ℝ 2 profile := by unfold profile; fun_prop
  have h := exists_corrector_dirichlet_representation_of_higher_graph
    (by norm_num : 2 ≤ 1 + 1) isOpen_domain isBounded_domain
    (hasContDiffGraphBoundary_domain.of_le (k := 5) le_top)
    (ContDiffUpToBoundary.of_contDiff hu isBounded_domain) hu.continuous.continuousOn
    pole_mem (f := fun _ ↦ -4) (g := profile)
    (fun y _ ↦ by rw [laplacian_profile]) (fun _ _ ↦ rfl)
  unfold greenKernel greenKernelGradient at h
  simpa only [profile_poles.1] using h

end PDE.Examples.GreenCorrectorAnnulus
