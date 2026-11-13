/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Taylor.LinearRemainder
public import PDE.Analysis.Spectral.FiniteDimensional.EigenvalueDerivative
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Curvature of a nonlinear remainder along a characteristic direction

The left coordinate of the flux Hessian on a right eigenvector equals the
directional derivative of its eigenvalue. A C² curve with that tangent has the
same second derivative after the flux linearization is subtracted. Its
acceleration makes no contribution.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Module.Basis

open PDE.Analysis

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second derivative of a left coordinate of the nonlinear remainder,
along any C² curve tangent to the corresponding right eigenvector, is the
directional derivative of that eigenvalue. -/
theorem iteratedDeriv_two_linearRemainder_coord
    (b : Basis ι ℝ E) {f : E → E} (hf : ContDiff ℝ 2 f) (q : E)
    (eig : ι → ℝ) (k : ι)
    (hdiag : ∀ j, fderiv ℝ f q (b j) = eig j • b j)
    {r : E → E} {a : E → ℝ}
    (hr : DifferentiableAt ℝ r q) (ha : DifferentiableAt ℝ a q)
    (hrq : r q = b k) (haq : a q = eig k)
    (heigen : ∀ᶠ y in 𝓝 q, fderiv ℝ f y (r y) = a y • r y)
    {γ : ℝ → E} (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hγ' : HasDerivAt γ (b k) 0) :
    iteratedDeriv 2 (fun s ↦ b.equivFun (linearRemainder f q (γ s)) k) 0 =
      fderiv ℝ a q (b k) := by
  let ℓ : E →L[ℝ] ℝ := (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  let R : ℝ → E := fun s ↦ linearRemainder f q (γ s)
  have hR : ContDiffAt ℝ 2 R 0 := (contDiff_linearRemainder hf q).contDiffAt.comp 0 hγ
  have hcoord : iteratedDeriv 2 (fun s ↦ ℓ (R s)) 0 = ℓ (iteratedDeriv 2 R 0) := by
    have h := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ ℝ) ℝ ↦
      D (fun _ ↦ 1)) (ℓ.iteratedFDeriv_comp_left hR le_rfl)
    change (iteratedFDeriv ℝ 2 (fun s ↦ ℓ (R s)) 0) (fun _ ↦ 1) =
      ℓ ((iteratedFDeriv ℝ 2 R 0) (fun _ ↦ 1)) at h
    simpa only [iteratedDeriv_eq_iteratedFDeriv] using h
  change iteratedDeriv 2 (fun s ↦ ℓ (R s)) 0 = _
  rw [hcoord]
  have hsecond : iteratedDeriv 2 R 0 =
      fderiv ℝ (fderiv ℝ f) q (b k) (b k) := by
    simpa only [R, hγ'.deriv] using iteratedDeriv_two_linearRemainder_comp hf q hγ hγ0
  rw [hsecond]
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (b.fderiv_eigenvalue_apply eig k hdiag (hDf.differentiable one_ne_zero q)
    hr ha hrq haq heigen (b k)).symm

end Module.Basis
