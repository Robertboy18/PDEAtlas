/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.SobolevDilation
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarTested
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The Leray projection on test fields

The whole-space Leray projection is self-adjoint for the vector `L²` pairing, so it can be
moved from a field onto a test field. A smooth compactly supported field with zero divergence
is fixed by the projection, and pairing with it does not see the projection.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open scoped ENNReal Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

/-- The Leray projection is self-adjoint for the vector `L²` pairing. -/
theorem vectorL2Pairing_leraySobolev (φ x : VectorH n 0) :
    vectorL2Pairing φ (leraySobolev n 0 x) = vectorL2Pairing (leraySobolev n 0 φ) x := by
  rw [vectorL2Pairing_apply, vectorL2Pairing_apply, l2SobolevRow_leraySobolev,
    l2SobolevRow_leraySobolev]
  exact (Submodule.inner_starProjection_left_eq_right (l2Solenoidal n) _ _).symm

/-- Pairing with a field fixed by the Leray projection does not see the projection. -/
theorem vectorL2Pairing_leraySobolev_of_eq {φ : VectorH n 0} (hφ : leraySobolev n 0 φ = φ)
    (x : VectorH n 0) : vectorL2Pairing φ (leraySobolev n 0 x) = vectorL2Pairing φ x := by
  rw [vectorL2Pairing_leraySobolev, hφ]

/-- A smooth compactly supported field with zero divergence is fixed by the Leray projection. -/
theorem leraySobolev_vectorOfMemLp_of_divergenceFree (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hcs : ∀ j, HasCompactSupport (f j))
    (hdiv : ∀ x, ∑ i, (PDE.partialDeriv i (f i)) x = 0) :
    leraySobolev n 0 (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j)) =
      vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j) := by
  set v : ℝ^n → ℝ^n := fun x ↦ WithLp.toLp 2 (fun j ↦ f j x)
  have hv : ContDiff ℝ 1 v :=
    (contDiff_piLp (p := (2 : ℝ≥0∞))).2 fun j ↦ (hf j).of_le (by simp)
  have hvdiv : SpatialFieldDivergenceFree v := fun x ↦ hdiv x
  have hdist := hvdiv.distributionallyDivergenceFree hv
  have hmem : l2SobolevRow (baseIndex n 0) (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
      ∈ l2Solenoidal n := by
    rw [mem_l2Solenoidal_iff_distributionallyDivergenceFree]
    intro ψ hψ hψc
    have hae : weakDivergencePairingDensity (fun x ↦ (l2SobolevRow (baseIndex n 0)
        (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j)) : ℝ^n → ℝ^n) x) ψ =ᵐ[volume]
        weakDivergencePairingDensity v ψ := by
      filter_upwards [l2SobolevRow_vectorOfMemLp_ae f fun j ↦ memLp_of_test (hf j) (hcs j)]
        with x hx
      rw [weakDivergencePairingDensity_eq_sum, weakDivergencePairingDensity_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hx i]
    obtain ⟨hint, hzero⟩ := hdist ψ hψ hψc
    exact ⟨hint.congr hae.symm, (integral_congr_ae hae).trans hzero⟩
  apply l2SobolevRow_base_injective
  rw [l2SobolevRow_leraySobolev, lerayProjection_eq_self hmem]

end IncompressibleFlow
