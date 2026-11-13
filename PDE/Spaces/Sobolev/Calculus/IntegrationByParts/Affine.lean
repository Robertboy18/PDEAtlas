/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.Constant

/-!
# Affine gradient terms on the Dirichlet space

The integral of a constant vector paired with a zero-boundary weak
gradient vanishes. The argument applies to the representatives
and uses coordinatewise integration by parts, including in dimension zero.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} [IsFiniteMeasure (domainMeasure n Ω)]

/-- A constant vector paired with a Dirichlet gradient has zero
integral. This is the affine part of the null boundary contribution. -/
theorem integral_inner_gradientCLM_eq_zero (a : ℝ^n) (u : H¹₀(Ω)) :
    ∫ x, ⟪a, ∇ (u : H¹(Ω)) x⟫ ∂domainMeasure n Ω = 0 := by
  let q (i : Fin n) : DerivLp n 2 Ω :=
    wkpBaseCoordinateCLM (wkpConstant (a i))
  have hq (i : Fin n) : (q i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ a i :=
    wkpConstant_base_ae _
  have hQ : Lp.euclideanTuple q =ᵐ[domainMeasure n Ω] fun _ ↦ a := by
    filter_upwards [Lp.euclideanTuple_apply_ae q, ae_all_iff.mpr hq] with x hx hy
    exact PiLp.ext fun i ↦ (hx i).trans (hy i)
  have hu : ∇ (u : H¹(Ω)) = Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) := by
    apply Lp.ext
    filter_upwards [gradientCLM_apply_ae u,
      Lp.euclideanTuple_apply_ae (fun i ↦ derivCoordCLM i u)] with x hx hy
    exact PiLp.ext fun i ↦ (hx i).trans (hy i).symm
  calc
    _ = ⟪Lp.euclideanTuple q, ∇ (u : H¹(Ω))⟫ := by
      rw [L2.inner_def]
      exact integral_congr_ae
        (hQ.mono fun x hx ↦ congrArg (fun z : ℝ^n ↦ ⟪z, (∇ (u : H¹(Ω))) x⟫) hx.symm)
    _ = ∑ i, ⟪q i, derivCoordCLM i u⟫ := by rw [hu, Lp.inner_euclideanTuple]
    _ = 0 := Finset.sum_eq_zero fun i _ ↦
      inner_constant_derivCoordCLM_eq_zero (a i) (q i) (hq i) i u

end SobolevSpace.GraphSpace
