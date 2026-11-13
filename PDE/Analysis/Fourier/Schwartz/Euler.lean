/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import PDE.Common.Euclidean

/-!
# The Euler operator and the Laplacian on Schwartz functions

The Euler operator `x · ∇ = ∑ⱼ xⱼ ∂ⱼ` is a continuous linear map on complex Schwartz functions
on `ℝⁿ`. Multiplication by a coordinate becomes a derivative under the Fourier transform, so

`𝓕 (x · ∇φ) (ξ) = -n 𝓕φ (ξ) - ξ · ∇𝓕φ (ξ)`,

and the Laplacian becomes multiplication by `-4π²|ξ|²`. The Fourier transform is Mathlib's
`𝓕 f ξ = ∫ exp (-2π i ⟪x, ξ⟫) f x dx`.
-/

@[expose] public noncomputable section

open FourierTransform LineDeriv Laplacian
open scoped SchwartzMap

namespace SchwartzMap

variable {n : ℕ}

/-- The coordinate multiplier `x ↦ x_j`, complex valued. -/
def coordMultiplier (j : Fin n) (x : ℝ^n) : ℂ := (inner ℝ x (EuclideanSpace.single j (1 : ℝ)) : ℂ)

theorem hasTemperateGrowth_coordMultiplier (j : Fin n) :
    (coordMultiplier (n := n) j).HasTemperateGrowth := by
  have := (Complex.ofRealCLM.comp ((innerSL ℝ).flip (EuclideanSpace.single j (1 : ℝ)) :
    ℝ^n →L[ℝ] ℝ)).hasTemperateGrowth
  convert this using 1
  funext x
  simp only [coordMultiplier, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, Complex.ofRealCLM_apply, innerSL_apply_apply]

theorem coordMultiplier_apply (j : Fin n) (x : ℝ^n) : coordMultiplier j x = (x j : ℂ) := by
  simp [coordMultiplier, EuclideanSpace.inner_single_right]

/-- The Euler operator `x · ∇` on complex Schwartz functions, coordinatewise. -/
def eulerCLM (n : ℕ) : 𝓢(ℝ^n, ℂ) →L[ℂ] 𝓢(ℝ^n, ℂ) :=
  ∑ j : Fin n, (smulLeftCLM ℂ (coordMultiplier (n := n) j)).comp
    (lineDerivOpCLM ℂ 𝓢(ℝ^n, ℂ) (EuclideanSpace.single j (1 : ℝ)))

theorem eulerCLM_apply (φ : 𝓢(ℝ^n, ℂ)) (x : ℝ^n) :
    eulerCLM n φ x = fderiv ℝ φ x x := by
  simp only [eulerCLM, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  simp only [smulLeftCLM_apply_apply (hasTemperateGrowth_coordMultiplier _),
    lineDerivOpCLM_apply, lineDerivOp_apply_eq_fderiv, coordMultiplier_apply]
  have hx : x = ∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ) := by
    simpa [EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x).symm
  calc _ = fderiv ℝ φ x (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) := by
        rw [map_sum]
        simp [map_smul, Complex.real_smul]
    _ = _ := by rw [← hx]

/-- Multiplication by a coordinate on the physical side is a derivative on the Fourier side. -/
theorem fourier_smulLeftCLM_coordMultiplier (j : Fin n) (g : 𝓢(ℝ^n, ℂ)) :
    𝓕 (smulLeftCLM ℂ (coordMultiplier (n := n) j) g) =
      (-(2 * Real.pi * Complex.I))⁻¹ • ∂_{EuclideanSpace.single j (1 : ℝ)} (𝓕 g) := by
  have h := lineDerivOp_fourier_eq g (EuclideanSpace.single j (1 : ℝ))
  have hreal : smulLeftCLM ℂ (inner ℝ · (EuclideanSpace.single j (1 : ℝ))) g =
      smulLeftCLM ℂ (coordMultiplier (n := n) j) g := by
    ext x
    have h1 : (fun x : ℝ^n ↦ inner ℝ x (EuclideanSpace.single j (1 : ℝ))).HasTemperateGrowth :=
      ((innerSL ℝ).flip (EuclideanSpace.single j (1 : ℝ))).hasTemperateGrowth
    rw [smulLeftCLM_apply_apply h1, smulLeftCLM_apply_apply (hasTemperateGrowth_coordMultiplier j),
      coordMultiplier, Complex.real_smul, smul_eq_mul]
  rw [hreal, FourierTransform.fourier_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_smul]

/-- The Fourier transform of the Euler operator: `𝓕 (x·∇φ) = -n 𝓕φ - ξ·∇ 𝓕φ`. -/
theorem fourier_eulerCLM_apply (φ : 𝓢(ℝ^n, ℂ)) (ξ : ℝ^n) :
    𝓕 (eulerCLM n φ) ξ = -(n : ℂ) * 𝓕 φ ξ - fderiv ℝ (fun η ↦ 𝓕 φ η) ξ ξ := by
  set F : 𝓢(ℝ^n, ℂ) := 𝓕 φ with hF
  have hterm (j : Fin n) :
      𝓕 (smulLeftCLM ℂ (coordMultiplier (n := n) j)
          (∂_{EuclideanSpace.single j (1 : ℝ)} φ)) ξ =
        -(F ξ + (ξ j : ℂ) * fderiv ℝ (fun η ↦ F η) ξ (EuclideanSpace.single j (1 : ℝ))) := by
    rw [fourier_smulLeftCLM_coordMultiplier, fourier_lineDerivOp_eq, ← hF]
    set m := EuclideanSpace.single j (1 : ℝ)
    have hc : (fun η : ℝ^n ↦ inner ℝ η m).HasTemperateGrowth :=
      ((innerSL ℝ).flip m).hasTemperateGrowth
    have hderiv : HasFDerivAt (fun η : ℝ^n ↦ inner ℝ η m • F η)
        (inner ℝ ξ m • fderiv ℝ (fun η ↦ F η) ξ +
          (((innerSL ℝ).flip m : ℝ^n →L[ℝ] ℝ).smulRight (F ξ))) ξ :=
      (((innerSL ℝ).flip m).hasFDerivAt).smul (F.differentiableAt.hasFDerivAt)
    have hfun : ⇑(smulLeftCLM ℂ (inner ℝ · m) F) = fun η : ℝ^n ↦ inner ℝ η m • F η := by
      funext η; exact smulLeftCLM_apply_apply hc F η
    simp only [smul_apply, lineDerivOp_smul, lineDerivOp_apply_eq_fderiv, hfun,
      hderiv.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply]
    have hmm : inner ℝ m m = (1 : ℝ) := by simp [m]
    have hξm : inner ℝ ξ m = ξ j := by simp [m, EuclideanSpace.inner_single_right]
    rw [hmm, hξm, smul_smul]
    have h2pi : (2 * Real.pi * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    rw [show ((-(2 * Real.pi * Complex.I))⁻¹ * (2 * Real.pi * Complex.I)) = -1 by
      field_simp]
    simp only [Complex.real_smul, neg_one_smul, one_smul]
    ring
  simp only [eulerCLM, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, lineDerivOpCLM_apply]
  rw [show 𝓕 (∑ j : Fin n, smulLeftCLM ℂ (coordMultiplier (n := n) j)
      (∂_{EuclideanSpace.single j (1 : ℝ)} φ)) =
      ∑ j : Fin n, 𝓕 (smulLeftCLM ℂ (coordMultiplier (n := n) j)
        (∂_{EuclideanSpace.single j (1 : ℝ)} φ)) from
    map_sum (fourierTransformCLM ℂ (V := ℝ^n) (E := ℂ)) _ _]
  simp only [sum_apply, hterm]
  have hx : ξ = ∑ i : Fin n, ξ i • EuclideanSpace.single i (1 : ℝ) := by
    simpa [EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr ξ).symm
  conv_rhs => rw [show fderiv ℝ (fun η ↦ F η) ξ ξ =
    fderiv ℝ (fun η ↦ F η) ξ (∑ i : Fin n, ξ i • EuclideanSpace.single i (1 : ℝ)) by
      rw [← hx]]
  rw [map_sum]
  simp only [map_smul, Complex.real_smul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The Fourier transform of the Laplacian of a Schwartz function. -/
theorem fourier_laplacian_apply (φ : 𝓢(ℝ^n, ℂ)) (ξ : ℝ^n) :
    𝓕 (Δ φ) ξ = -((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * 𝓕 φ ξ := by
  rw [laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ)]
  rw [show 𝓕 (∑ i : Fin n, ∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
      (∂_{EuclideanSpace.basisFun (Fin n) ℝ i} φ)) =
      ∑ i : Fin n, 𝓕 (∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
        (∂_{EuclideanSpace.basisFun (Fin n) ℝ i} φ)) from
    map_sum (fourierTransformCLM ℂ (V := ℝ^n) (E := ℂ)) _ _]
  simp only [sum_apply, fourier_lineDerivOp_eq, smul_apply]
  have hc (m : ℝ^n) : (fun η : ℝ^n ↦ inner ℝ η m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  simp only [smulLeftCLM_apply_apply (hc _), smul_apply]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, Complex.real_smul,
    smul_eq_mul]
  have hnorm : ‖ξ‖ ^ 2 = ∑ i : Fin n, ξ i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [hnorm]
  push_cast
  rw [Finset.mul_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [conj_trivial]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (ξ i : ℂ) ^ 2 * 𝓕 φ ξ) * hI

end SchwartzMap
