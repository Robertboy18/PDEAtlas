/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Basic
public import PDE.Analysis.Calculus.Diffeomorph
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# State coordinate changes for quasilinear systems

For a smooth diffeomorphism `Φ` with inverse `Ψ`, the transformed coefficient
is `DΦ(Ψ(y)) B(Ψ(y)) DΨ(y)`. Its residual on `Φ ∘ u` is the image of the
original residual under `DΦ(u)`. The coefficients are conjugate at corresponding
states, preserving the characteristic polynomial and strict hyperbolicity.

`coordinateChange_strictlyHyperbolic_forward` is Evans, §11.1.2, Theorem 1:
`coordinateChange` is the coefficient (31), `residual_coordinateChange` is step 1 of the proof,
and `IsStrictlyHyperbolicAt.coordinateChange` moves the eigenbasis by `DΦ` with unchanged
speeds, as in (32)-(34). The forward-domain result assumes smoothness only for positive times.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.2, Theorem 1 and its proof, equations (29)-(34).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace PDE.Hyperbolic.Quasilinear

variable {m : ℕ}

/-- The coefficient field in the new state coordinates. -/
def coordinateChange (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m)
    (y : ℝ^m) : ℝ^m →L[ℝ] ℝ^m :=
  (fderiv ℝ Φ (Φ.symm y)).comp ((B (Φ.symm y)).comp (fderiv ℝ Φ.symm y))

/-- The transformed coefficient intertwines with the derivative of the change of
coordinates. The inverse derivative identity follows by the chain rule. -/
theorem coordinateChange_apply_fderiv
    (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m) (state v : ℝ^m) :
    coordinateChange B Φ (Φ state) (fderiv ℝ Φ state v) =
      fderiv ℝ Φ state (B state v) := by
  have hinv : (fderiv ℝ Φ.symm (Φ state)).comp (fderiv ℝ Φ state) =
      ContinuousLinearMap.id ℝ (ℝ^m) := by
    rw [← fderiv_comp state (Φ.symm.contDiff.differentiable (by simp) _)
      (Φ.contDiff.differentiable (by simp) _)]
    simp only [Function.comp_def, Φ.symm_apply_apply, fderiv_fun_id]
  have hv := congrArg (fun A : ℝ^m →L[ℝ] ℝ^m ↦ A v) hinv
  simpa only [coordinateChange, Φ.symm_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun w ↦ fderiv ℝ Φ state (B state w)) hv

/-- The full residual transforms by the derivative of the state diffeomorphism. -/
theorem residual_coordinateChange
    (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m)
    {u : ℝ^2 → ℝ^m} {p : ℝ^2} (hu : DifferentiableAt ℝ u p) :
    residual (coordinateChange B Φ) (Φ ∘ u) p =
      fderiv ℝ Φ (u p) (residual B u p) := by
  have hderiv (i : Fin 2) :
      (∂[i] (Φ ∘ u)) p = fderiv ℝ Φ (u p) ((∂[i] u) p) := by
    unfold partialDeriv
    rw [fderiv_comp p (Φ.contDiff.differentiable (by simp) _) hu]
    rfl
  simp only [residual, hderiv, Function.comp_apply, coordinateChange_apply_fderiv, map_add]

/-- A classical solution on any domain remains a solution in the new coordinates. -/
theorem IsClassicalSolutionOn.coordinateChange
    {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} {U : Set ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsClassicalSolutionOn B U u) (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m) :
    IsClassicalSolutionOn (coordinateChange B Φ) U (Φ ∘ u) where
  differentiableAt p hp :=
    (Φ.contDiff.differentiable (by simp) _).comp p (hu.differentiableAt p hp)
  residual_eq_zero p hp := by
    rw [residual_coordinateChange B Φ (hu.differentiableAt p hp), hu.residual_eq_zero p hp,
      map_zero]

/-- At corresponding states the coefficients are conjugate by Mathlib's
derivative equivalence of the given diffeomorphism. -/
theorem coordinateChange_eq_conj
    (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m) (state : ℝ^m) :
    (coordinateChange B Φ (Φ state)).toLinearMap =
      (Φ.fderivEquiv state).toLinearEquiv.conj
        (B state).toLinearMap := by
  let e : ℝ^m ≃L[ℝ] ℝ^m := Φ.fderivEquiv state
  have he : e.toContinuousLinearMap = fderiv ℝ Φ state := Φ.coe_fderivEquiv state
  ext v : 1
  obtain ⟨w, rfl⟩ := e.surjective v
  change coordinateChange B Φ (Φ state) (e w) =
    e.toLinearEquiv.conj (B state).toLinearMap (e w)
  simp only [LinearEquiv.conj_apply_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ← ContinuousLinearEquiv.toLinearEquiv_symm, ContinuousLinearEquiv.symm_apply_apply]
  simpa only [← he, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_coe] using
    coordinateChange_apply_fderiv B Φ state w

/-- The whole characteristic polynomial is preserved, including multiplicities. -/
theorem charpoly_coordinateChange
    (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m) (y : ℝ^m) :
    (coordinateChange B Φ y).toLinearMap.charpoly = (B (Φ.symm y)).toLinearMap.charpoly := by
  have h := congrArg LinearMap.charpoly (coordinateChange_eq_conj B Φ (Φ.symm y))
  simpa only [LinearEquiv.charpoly_conj, Φ.apply_symm_apply] using h

/-- Strict hyperbolicity is preserved at each corresponding state. -/
theorem IsStrictlyHyperbolicAt.coordinateChange
    {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m) {y : ℝ^m}
    (hB : IsStrictlyHyperbolicAt B (Φ.symm y)) :
    IsStrictlyHyperbolicAt (coordinateChange B Φ) y := by
  rcases hB with ⟨b, speed, hinj, heigen⟩
  let e := (Φ.fderivEquiv (Φ.symm y)).toLinearEquiv
  refine ⟨b.map e, speed, hinj, fun k ↦ ?_⟩
  have hc : (Quasilinear.coordinateChange B Φ y).toLinearMap =
      e.conj (B (Φ.symm y)).toLinearMap := by
    simpa only [Φ.apply_symm_apply] using coordinateChange_eq_conj B Φ (Φ.symm y)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, (b.map e).ne_zero k⟩
  rw [hc, Module.Basis.map_apply, LinearEquiv.conj_apply_apply, e.symm_apply_apply]
  rw [(heigen k).apply_eq_smul, map_smul]

/-- A smooth forward solution transforms to a smooth forward solution. -/
theorem coordinateChange_forward
    {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} {u : ℝ^2 → ℝ^m}
    (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m)
    (hu : ContDiffOn ℝ ∞ u PDE.Common.positiveTimeDomain)
    (hpde : ∀ p ∈ PDE.Common.positiveTimeDomain, residual B u p = 0) :
    ContDiffOn ℝ ∞ (Φ ∘ u) PDE.Common.positiveTimeDomain ∧
      IsClassicalSolutionOn (coordinateChange B Φ) PDE.Common.positiveTimeDomain (Φ ∘ u) := by
  refine ⟨Φ.contDiff.comp_contDiffOn hu, ?_⟩
  apply IsClassicalSolutionOn.coordinateChange (Φ := Φ)
  refine ⟨fun p hp ↦ ?_, hpde⟩
  exact (hu.contDiffAt (PDE.Common.isOpen_positiveTimeDomain.mem_nhds hp)).differentiableAt
    (by simp)

/-- A smooth solution of a strictly hyperbolic system remains a smooth solution
of a strictly hyperbolic system after a state diffeomorphism. Hyperbolicity
holds at every state, not just along the given solution. -/
theorem coordinateChange_strictlyHyperbolic_forward
    {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} {u : ℝ^2 → ℝ^m}
    (Φ : ℝ^m ≃ₘ[ℝ] ℝ^m)
    (hu : ContDiffOn ℝ ∞ u PDE.Common.positiveTimeDomain)
    (hpde : ∀ p ∈ PDE.Common.positiveTimeDomain, residual B u p = 0)
    (hB : ∀ state, IsStrictlyHyperbolicAt B state) :
    ContDiffOn ℝ ∞ (Φ ∘ u) PDE.Common.positiveTimeDomain ∧
      IsClassicalSolutionOn (coordinateChange B Φ) PDE.Common.positiveTimeDomain (Φ ∘ u) ∧
      ∀ y, IsStrictlyHyperbolicAt (coordinateChange B Φ) y := by
  obtain ⟨hsmooth, hsol⟩ := coordinateChange_forward Φ hu hpde
  exact ⟨hsmooth, hsol, fun y ↦ (hB (Φ.symm y)).coordinateChange Φ⟩

end PDE.Hyperbolic.Quasilinear
