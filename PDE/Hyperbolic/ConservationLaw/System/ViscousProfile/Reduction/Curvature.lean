/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Coordinates
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.CenterCoordinates
public import PDE.Analysis.Spectral.FiniteDimensional.JacobianCurvature
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Characteristic curvature of the reduced profile field

The graph is tangent to the two-dimensional center space. At zero speed
displacement, its state curve is tangent to the selected right eigenvector.
The zero first jet of the flux remainder removes the graph's second derivative
from the reduced curvature. What remains is exactly the directional derivative
of the characteristic speed.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis PDE.Analysis.Evolution

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A center-tangent C² graph has the characteristic curvature in its
reduced scalar equation. The hypotheses here are graph properties proved by the invariant-graph
construction. -/
theorem iteratedDeriv_two_augmentedProfileRemainder_graph (b : Module.Basis ι ℝ E) {flux : E → E}
    (hflux : ContDiff ℝ 2 flux) (q : E) (eig : ι → ℝ) (k : ι)
    (hdiag : ∀ j, fderiv ℝ flux q (b j) = eig j • b j) {r : E → E} {a : E → ℝ}
    (hr : DifferentiableAt ℝ r q) (ha : DifferentiableAt ℝ a q) (hrq : r q = b k)
    (haq : a q = eig k) (heigen : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y (r y) = a y • r y)
    {φ : (Option ι → ℝ) → (Option ι → ℝ)} (hφ : ContDiffAt ℝ 2 φ 0) (hφ0 : φ 0 = 0)
    (hDφ : HasFDerivAt φ (diagonalCenterProjection (augmentedProfileRate eig k)) 0)
    (hparameter : ∀ s : ℝ, φ (profileCenterCoordinates k (s, 0)) none = 0) :
    iteratedDeriv 2 (fun s ↦ augmentedProfileRemainder flux q b.equivFunL
      (φ (profileCenterCoordinates k (s, 0))) (some k)) 0 = fderiv ℝ a q (b k) := by
  classical
  let C := profileCenterCoordinates k
  let B : (Option ι → ℝ) →L[ℝ] E := b.equivFunL.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (some i))
  let γ : ℝ → E := fun s ↦ B (φ (C (s, 0)))
  have hC0 : C ((0 : ℝ), (0 : ℝ)) = 0 := C.map_zero
  have hcenter : diagonalCenterProjection (augmentedProfileRate eig k) (C (1, 0)) =
      C (1, 0) := diagonalCenterProjection_eq_self _ _
        (rate_mul_profileCenterCoordinates eig k (1, 0))
  have hB : B (C (1, 0)) = b k := by
    apply b.equivFunL.injective
    change b.equivFunL (b.equivFunL.symm (fun i ↦ C (1, 0) (some i))) = b.equivFunL (b k)
    rw [b.equivFunL.apply_symm_apply]
    ext i
    by_cases hi : i = k
    · subst i
      simp [C]
    · simp [C, profileCenterCoordinates_of_ne k _ hi, hi]
  have hγ0 : γ 0 = 0 := by simp only [γ, hC0, hφ0, map_zero]
  have hinner : ContDiffAt ℝ 2 (fun s : ℝ ↦ C (s, 0)) 0 :=
    C.contDiff.contDiffAt.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hγ : ContDiffAt ℝ 2 γ 0 := by
    have hφC : ContDiffAt ℝ 2 φ (C ((0 : ℝ), (0 : ℝ))) := by
      simpa only [hC0] using hφ
    exact B.contDiff.contDiffAt.comp 0 (hφC.comp (f := fun s : ℝ ↦ C (s, 0)) 0 hinner)
  have hinnerD : HasDerivAt (fun s : ℝ ↦ C (s, 0)) (C (1, 0)) 0 := C.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have hγD : HasDerivAt γ (b k) 0 := by
    have h := B.hasFDerivAt.comp_hasDerivAt 0 (hDφ.comp_hasDerivAt_of_eq 0 hinnerD hC0.symm)
    simpa only [Function.comp_def, γ, hcenter, hB] using h
  have heq : (fun s ↦ augmentedProfileRemainder flux q b.equivFunL (φ (C (s, 0))) (some k)) =
      fun s ↦ b.equivFun (linearRemainder flux q (γ s)) k := by
    funext s
    simp only [augmentedProfileRemainder, C, hparameter, zero_mul, sub_zero]
    rfl
  rw [heq]
  exact b.iteratedDeriv_two_linearRemainder_coord hflux q eig k hdiag
    hr ha hrq haq heigen hγ hγ0 hγD

end PDE.Hyperbolic.ConservationLaw.System
