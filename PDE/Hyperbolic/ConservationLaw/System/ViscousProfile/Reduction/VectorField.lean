/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Coordinates
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.CenterCoordinates
public import PDE.LinearAlgebra.Eigenbasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The physical vector field on a profile graph

Project an augmented graph back through the fixed eigenvector coordinates.
Its scalar center field is the selected coordinate of the flux
remainder. Differential invariance then gives exactly the integrated vector
profile equation, including the speed displacement.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Evolution

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Recover the physical state displacement from the augmented coordinates.
The speed coordinate is discarded. -/
def profileStateProjection (e : E ≃L[ℝ] (ι → ℝ)) :
    (Option ι → ℝ) →L[ℝ] E :=
  e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (some i))

/-- The physical state on a graph, parametrized by amplitude and speed
displacement. -/
def profileGraph (q : E) (e : E ≃L[ℝ] (ι → ℝ)) (k : ι)
    (φ : (Option ι → ℝ) → (Option ι → ℝ)) (z : ℝ × ℝ) : E :=
  q + profileStateProjection e (φ (profileCenterCoordinates k z))

/-- The scalar velocity in the selected state coordinate of the augmented
profile equation. -/
def reducedProfileField (flux : E → E) (q : E) (e : E ≃L[ℝ] (ι → ℝ)) (k : ι)
    (φ : (Option ι → ℝ) → (Option ι → ℝ)) (z : ℝ × ℝ) : ℝ :=
  augmentedProfileRemainder flux q e (φ (profileCenterCoordinates k z)) (some k)

/-- Projection and translation preserve the regularity of the graph. -/
theorem contDiff_profileGraph (q : E) (e : E ≃L[ℝ] (ι → ℝ)) (k : ι)
    {φ : (Option ι → ℝ) → (Option ι → ℝ)} {n : WithTop ℕ∞}
    (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (profileGraph q e k φ) :=
  contDiff_const.add ((profileStateProjection e).contDiff.comp
    (hφ.comp (profileCenterCoordinates k).contDiff))

/-- The scalar velocity has the common regularity of the flux and graph. -/
theorem contDiff_reducedProfileField {flux : E → E} {n : WithTop ℕ∞}
    (hflux : ContDiff ℝ n flux) (q : E) (e : E ≃L[ℝ] (ι → ℝ)) (k : ι)
    {φ : (Option ι → ℝ) → (Option ι → ℝ)} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (reducedProfileField flux q e k φ) :=
  (contDiff_apply ℝ (fun _ ↦ ℝ) (some k)).comp
    ((contDiff_augmentedProfileRemainder hflux q e).comp
      (hφ.comp (profileCenterCoordinates k).contDiff))

omit [Fintype ι] in
/-- Differential invariance of an augmented graph gives the integrated
profile field in physical coordinates. No orthogonality of the eigenbasis is
used. -/
theorem fderiv_profileGraph_apply_reducedProfileField
    [Finite ι]
    (b : Module.Basis ι ℝ E) (flux : E → E) (q : E)
    (eig : ι → ℝ) (heig : Function.Injective eig) (k : ι)
    (hdiag : ∀ i, fderiv ℝ flux q (b i) = eig i • b i)
    {φ : (Option ι → ℝ) → (Option ι → ℝ)} (z : ℝ × ℝ)
    (hφ : DifferentiableAt ℝ φ (profileCenterCoordinates k z))
    (hparameter : φ (profileCenterCoordinates k z) none = z.2)
    (hinvariant :
      let X := φ (profileCenterCoordinates k z)
      let V := fun i ↦ augmentedProfileRate eig k i * X i +
        augmentedProfileRemainder flux q b.equivFunL X i
      fderiv ℝ φ (profileCenterCoordinates k z)
        (diagonalCenterProjection (augmentedProfileRate eig k) V) = V) :
    fderiv ℝ (profileGraph q b.equivFunL k φ) z
        (reducedProfileField flux q b.equivFunL k φ z, 0) =
      flux (profileGraph q b.equivFunL k φ z) - flux q -
        (eig k + z.2) • (profileGraph q b.equivFunL k φ z - q) := by
  let := Fintype.ofFinite ι
  let C := profileCenterCoordinates k
  let B := profileStateProjection b.equivFunL
  let X := φ (C z)
  let V := fun i ↦ augmentedProfileRate eig k i * X i +
    augmentedProfileRemainder flux q b.equivFunL X i
  have hcenter : diagonalCenterProjection (augmentedProfileRate eig k) V =
      C (reducedProfileField flux q b.equivFunL k φ z, 0) := by
    rw [diagonalCenterProjection_augmentedProfileRate eig heig k]
    congr 1
    ext <;> simp [V, augmentedProfileRate, augmentedProfileRemainder,
      reducedProfileField, X, C]
  have hd : HasFDerivAt (profileGraph q b.equivFunL k φ)
      (B.comp ((fderiv ℝ φ (C z)).comp C)) z := by
    simpa only [profileGraph, Function.comp_def, zero_add, Pi.add_apply, B, C] using!
      (hasFDerivAt_const (𝕜 := ℝ) q z).add
        (B.hasFDerivAt.comp z (hφ.hasFDerivAt.comp z C.hasFDerivAt))
  rw [hd.fderiv]
  change B (fderiv ℝ φ (C z)
    (C (reducedProfileField flux q b.equivFunL k φ z, 0))) = _
  rw [← hcenter, hinvariant]
  apply b.equivFunL.injective
  ext i
  change b.equivFunL (b.equivFunL.symm (fun j ↦ V (some j))) i = _
  rw [b.equivFunL.apply_symm_apply]
  have hdiagonal (y : ι → ℝ) (j : ι) :
      b.equivFunL (fderiv ℝ flux q (b.equivFunL.symm y)) j = eig j * y j := by
    have h := b.equivFun_apply_of_apply_basis_eq_smul
      (fderiv ℝ flux q).toLinearMap eig hdiag (b.equivFunL.symm y) j
    change b.equivFunL (fderiv ℝ flux q (b.equivFunL.symm y)) j =
      eig j * b.equivFunL (b.equivFunL.symm y) j at h
    rwa [b.equivFunL.apply_symm_apply] at h
  have heq := augmentedProfileRemainder_add_linear flux q b.equivFunL eig
    hdiagonal (eig k) X i
  simpa only [V, augmentedProfileRate, X, C, hparameter, profileGraph,
    add_sub_cancel_left, B, profileStateProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe] using! heq

end PDE.Hyperbolic.ConservationLaw.System
