/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.PartialDeriv
public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Geometry
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import PDE.DistributionTheory.TestFunction
import PDE.Hyperbolic.ConservationLaw.AffineInterface.BoundaryIntegral

/-!
# Vector boundary integrals across affine interfaces

The scalar affine-interface boundary identity extends coordinatewise to
Euclidean-valued coefficients because continuous coordinate projections
commute with Bochner integration.
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.AffineInterface

noncomputable section

open MeasureTheory
open PDE.Common
open TopologicalSpace

open scoped Distributions Topology

/-- A vector-valued affine derivative integral reduces to its interface trace.

This is the boundary identity used for shocks in systems of conservation laws. It follows
coordinatewise from the scalar identity because Bochner integration commutes with continuous
linear coordinate projections. -/
theorem setIntegral_smul_add_smul_partialDeriv_leftHalfSpace {m : ℕ} (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ))
    (s : ℝ) (timeCoeff spaceCoeff : ℝ^m) :
    (∫ x in leftHalfSpace s, (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x • timeCoeff +
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x • spaceCoeff ∂volume) =
      (∫ t : ℝ, φ (interface s t) ∂volume) • (spaceCoeff - s • timeCoeff) := by
  classical
  let F : ℝ^2 → ℝ^m := fun x ↦ (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x • timeCoeff +
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x • spaceCoeff
  have hInt : Integrable F (volume.restrict (leftHalfSpace s)) :=
    ((φ.integrable_partialDeriv (0 : Fin 2)).restrict.smul_const timeCoeff).add
      ((φ.integrable_partialDeriv (1 : Fin 2)).restrict.smul_const spaceCoeff)
  ext i
  let proj : ℝ^m →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m ↦ ℝ) i
  have hproj : (∫ x in leftHalfSpace s, proj (F x) ∂volume) =
        proj (∫ x in leftHalfSpace s, F x ∂volume) := proj.integral_comp_comm hInt
  calc
    (∫ x in leftHalfSpace s, (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x • timeCoeff +
          (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x • spaceCoeff ∂volume) i = ∫ x in leftHalfSpace s,
          (timeCoeff i * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x +
            spaceCoeff i * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x) ∂volume := by
      rw [show (∫ x in leftHalfSpace s, (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x • timeCoeff +
            (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x • spaceCoeff ∂volume) =
          ∫ x in leftHalfSpace s, F x ∂volume by rfl]
      rw [← PiLp.proj_apply (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) i, ← hproj]
      apply integral_congr_ae
      filter_upwards with x
      simp [proj, F, mul_comm]
    _ = (spaceCoeff i - timeCoeff i * s) * ∫ t : ℝ, φ (interface s t) ∂volume :=
      setIntegral_linearCombination_partialDeriv_leftHalfSpace φ s (timeCoeff i) (spaceCoeff i)
    _ = ((∫ t : ℝ, φ (interface s t) ∂volume) •
          (spaceCoeff - s • timeCoeff)) i := by
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring

end

end PDE.Hyperbolic.ConservationLaw.AffineInterface
