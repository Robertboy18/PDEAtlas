/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Taylor.LinearRemainder
import CAS.ExactTactic

/-!
# Flux remainders in augmented eigenvector coordinates

The extra coordinate records the wave-speed displacement and has zero
derivative. The remaining coordinates are obtained through an arbitrary continuous linear
equivalence, not necessarily orthogonal. Subtracting the flux linearization leaves a smooth
remainder vanishing to first order at zero. The parameter contributes the bilinear term `-μx`.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonlinear part of the augmented profile equation in fixed linear
coordinates. `none` is the wave-speed displacement; `some i` is a state
coordinate. -/
def augmentedProfileRemainder (flux : E → E) (q : E) (e : E ≃L[ℝ] (ι → ℝ))
    (x : Option ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => e (linearRemainder flux q (e.symm (fun j ↦ x (some j)))) i -
      x none * x (some i)

omit [Fintype ι] in
/-- The augmented nonlinear remainder vanishes at the origin. -/
@[simp] theorem augmentedProfileRemainder_zero
    (flux : E → E) (q : E) (e : E ≃L[ℝ] (ι → ℝ)) :
    augmentedProfileRemainder flux q e 0 = 0 := by
  ext i
  cases i with
  | none => rfl
  | some i =>
    change e (linearRemainder flux q (e.symm 0)) i - 0 * 0 = 0
    simp

/-- Fixed coordinate changes and the speed parameter preserve the regularity
of the flux without a derivative loss. -/
theorem contDiff_augmentedProfileRemainder {flux : E → E} {n : WithTop ℕ∞}
    (hflux : ContDiff ℝ n flux) (q : E) (e : E ≃L[ℝ] (ι → ℝ)) :
    ContDiff ℝ n (augmentedProfileRemainder flux q e) := by
  have hs : ContDiff ℝ n (fun x : Option ι → ℝ ↦ fun i ↦ x (some i)) :=
    contDiff_pi.mpr fun i ↦ contDiff_apply ℝ (fun _ ↦ ℝ) (some i)
  have hr := e.contDiff.comp ((contDiff_linearRemainder hflux q).comp (e.symm.contDiff.comp hs))
  refine contDiff_pi.mpr fun i ↦ ?_
  cases i with
  | none => exact contDiff_const
  | some i =>
    exact ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp hr).sub
      ((contDiff_apply ℝ (fun _ ↦ ℝ) none).mul (contDiff_apply ℝ (fun _ ↦ ℝ) (some i)))

omit [Fintype ι] in
/-- The derivative of the augmented remainder is zero at the origin.
The bilinear parameter term also has zero derivative there. -/
theorem hasFDerivAt_augmentedProfileRemainder_zero [Finite ι] {flux : E → E}
    (q : E) (e : E ≃L[ℝ] (ι → ℝ)) (hflux : DifferentiableAt ℝ flux q) :
    HasFDerivAt (augmentedProfileRemainder flux q e)
      (0 : (Option ι → ℝ) →L[ℝ] (Option ι → ℝ)) 0 := by
  let := Fintype.ofFinite ι
  let B : (Option ι → ℝ) →L[ℝ] E := e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (some i))
  have hR : HasFDerivAt (linearRemainder flux q)
      (0 : E →L[ℝ] E) (B 0) := by
    simpa only [map_zero] using hasFDerivAt_linearRemainder_zero q hflux
  have hd : HasFDerivAt (fun x : Option ι → ℝ ↦ e (linearRemainder flux q (B x)))
      (0 : (Option ι → ℝ) →L[ℝ] (ι → ℝ)) 0 := by
    simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
      Function.comp_def] using! e.toContinuousLinearMap.hasFDerivAt.comp 0 (hR.comp 0 B.hasFDerivAt)
  refine hasFDerivAt_pi'' fun i ↦ ?_
  simp only [ContinuousLinearMap.comp_zero]
  cases i with
  | none =>
    simpa only [augmentedProfileRemainder] using!
      hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : Option ι → ℝ)
  | some i =>
    have hc := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp 0 hd
    have hm := (ContinuousLinearMap.proj none : (Option ι → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := 0) |>.mul
        (ContinuousLinearMap.proj (some i) : (Option ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
    simpa only [augmentedProfileRemainder, B, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Function.comp_def,
      ContinuousLinearMap.comp_zero, zero_smul, zero_add, sub_zero, Pi.zero_apply] using! hc.sub hm

omit [Fintype ι] in
/-- Adding the diagonal linear part gives the exact integrated profile field
with speed `s + μ`, expressed in the chosen coordinates. -/
theorem augmentedProfileRemainder_add_linear (flux : E → E) (q : E) (e : E ≃L[ℝ] (ι → ℝ))
    (eig : ι → ℝ) (hdiag : ∀ y i, e (fderiv ℝ flux q (e.symm y)) i = eig i * y i) (s : ℝ)
    (x : Option ι → ℝ) (i : ι) :
    (eig i - s) * x (some i) + augmentedProfileRemainder flux q e x (some i) =
      e (flux (q + e.symm (fun j ↦ x (some j))) - flux q -
        (s + x none) • e.symm (fun j ↦ x (some j))) i := by
  simp only [augmentedProfileRemainder, linearRemainder, map_sub, Pi.sub_apply,
    map_smul, Pi.smul_apply, smul_eq_mul, e.apply_symm_apply, hdiag]
  cas

end PDE.Hyperbolic.ConservationLaw.System
