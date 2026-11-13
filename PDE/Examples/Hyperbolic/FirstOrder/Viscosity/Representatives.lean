/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.Coupled
import PDE.Spaces.Sobolev.Approximation.Mollification.Congruence
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Closed trace and physical PDE of the concrete coupled solution

For a strong solution of the coupled viscous problem, the initial trace is the
mollification of the initial profiles (`coupled_initial_convolution`). By
`exists_spacetimeRepresentatives`, the weak derivatives of the solution and of its time
derivative have measurable spacetime representatives, and the coupled equation
`∂ₜu - ε ∂ₓ²u + A(t, x) ∂ₓu = F` holds for them almost everywhere in spacetime
(`coupled_physical_spacetime`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity

open MeasureTheory Set PDE.Common
open PDE.Hyperbolic.FirstOrder PDE.Parabolic.Systems
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

variable {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
  {U : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{3,2}(ℝ^1))) 2
    (volume.restrict (Ioc 0 T))}
  {G : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))) 2
    (volume.restrict (Ioc 0 T))}
  {z : ℝ → PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))}
  (h : IsStrongTransportDiffusionSolution ε 0 T
    (fun j y p q ↦ coupledMatrix j (timeSpaceCons y.1 y.2) p q)
    (fun p y ↦ wkpBaseCoordinateCLM (forcingData hT p) (timeSpaceCons y.1 y.2))
    (ContinuousLinearMap.piLpMap 2
      (fun _ : Fin 2 ↦ mollifierHkCLM (standardMollifier 1) hε) initialData) U G z)

include h

/-- The initial trace is the mollification of the initial profiles at scale `ε`. -/
theorem coupled_initial_convolution :
    ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (z 0 p) x =
        mollify (standardMollifier 1) ε (initialTest p) x := by
  rw [h.initial_eq]
  filter_upwards [piLpMap_mollifierHkCLM_base_ae (standardMollifier 1) hε initialData]
    with x hx
  intro p
  rw [hx p, mollify_congr_ae (standardMollifier 1) ε (initialData_base_ae p)]

/-- The weak derivatives of the solution and of its time derivative have measurable
spacetime representatives, and the coupled equation holds for them almost everywhere. -/
theorem coupled_physical_spacetime :
    ∃ (r : Fin 2 → DerivIndex 1 3 → SpaceTime 1 → ℝ)
      (v : Fin 2 → DerivIndex 1 1 → SpaceTime 1 → ℝ),
      (∀ p d, StronglyMeasurable (r p d) ∧
        MemLp (r p d) 2 (volume.restrict {y | y 0 ∈ Ioc 0 T})) ∧
      (∀ p d, StronglyMeasurable (v p d) ∧
        MemLp (v p d) 2 (volume.restrict {y | y 0 ∈ Ioc 0 T})) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p d,
        r p d (timeSpaceCons t x) = wkpCoordinateCLM d (U t p) x) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p d,
        v p d (timeSpaceCons t x) = wkpCoordinateCLM d (G t p) x) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ p d, HasWeakDerivativeOn univ d.toList
        (fun x ↦ r p (baseIndex 1 3) (timeSpaceCons t x))
        (fun x ↦ r p d (timeSpaceCons t x))) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ p d, HasWeakDerivativeOn univ d.toList
        (fun x ↦ v p (baseIndex 1 1) (timeSpaceCons t x))
        (fun x ↦ v p d (timeSpaceCons t x))) ∧
      (∀ᵐ y ∂volume.restrict {y : SpaceTime 1 | y 0 ∈ Ioc 0 T}, ∀ p,
        v p (baseIndex 1 1) y -
          ε * (∑ j, r p ((pairDerivIndex 1 j j).castOrder (by decide : 2 ≤ 3)) y) +
          (∑ j, ∑ q, coupledMatrix j y p q *
            r q ((singleDerivIndex 1 j).castOrder (by decide : 1 ≤ 3)) y) =
          wkpBaseCoordinateCLM (forcingData hT p) y) := by
  apply h.exists_spacetimeRepresentatives
  · exact aestronglyMeasurable_matrix_timeSpace coupledMatrix
      (fun j p q ↦ (coupledMatrix_contDiff j p q).continuous.continuousOn)
  · intro p
    exact ((Lp.stronglyMeasurable (wkpBaseCoordinateCLM (forcingData hT p))).comp_measurable
      (timeSpaceContinuousLinearEquiv 1).symm.continuous.measurable).aestronglyMeasurable

end PDE.Examples.Hyperbolic.Viscosity
