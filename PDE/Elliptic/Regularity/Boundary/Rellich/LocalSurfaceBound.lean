/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.GraphCollarFlux

/-!
# Local surface bounds for weak Green pairings

On a fixed compact window inside a C¹ graph patch, the conormal has a uniform
bound. The computed collar flux and localized strip energy therefore bound the
weak Green pairing in the physical surface L² norm. The constant is chosen
before the test function. No boundary value of the weak gradient is assumed.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Sobolev Gradient

namespace SobolevSpace.GraphSpace.Rellich

open Approximation.UpToBoundary Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A localized weak Poisson state has a finite surface bound on all C¹ tests
supported in a fixed compact chart window. The constant precedes the test. -/
theorem exists_greenPairing_surface_bound
    (P : InwardPartition Ω) (cover : Boundary.C1GraphBoundaryCover m Ω)
    (i : Fin cover.N) (z : H¹₀(Ω)) (u : ℝ^(m + 1) → ℝ)
    (hu : (baseCoordCLM z : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] u)
    (hpatch : tsupport (Ω.indicator u) ⊆ cover.boundaryPatch i)
    (f : DerivLp (m + 1) 2 Ω)
    (hweak : ∀ v : TestFunctionOn (m + 1) Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian v.1.toFun x
        ∂domainMeasure (m + 1) Ω) =
      ∫ x, (f : ℝ^(m + 1) → ℝ) x * v.1.toFun x ∂domainMeasure (m + 1) Ω)
    {K : Set ℝ^(m + 1)} (hK : IsCompact K) (hKP : K ⊆ cover.boundaryPatch i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : ℝ^(m + 1) → ℝ, ContDiff ℝ 1 φ → tsupport φ ⊆ K →
      |(∫ x, (f : ℝ^(m + 1) → ℝ) x * φ x ∂domainMeasure (m + 1) Ω) +
        ∫ x, inner ℝ ((wkpGradientCLM (z : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1)) x)
          (∇ φ x) ∂domainMeasure (m + 1) Ω| ≤
        C * Real.sqrt (∫ x, φ x ^ 2 ∂surfaceMeasure Ω) := by
  let d : ℝ^(m + 1) → ℝ := fun x ↦
    (cover.coordinates i x).2 - cover.height i (cover.coordinates i x).1
  have hd : ContDiff ℝ 1 d :=
    (cover.coordinates i).contDiff.snd.sub
      ((cover.height_contDiff i).comp (cover.coordinates i).contDiff.fst)
  obtain ⟨D₀, hD₀⟩ := hK.exists_bound_of_continuousOn
    (hd.continuous_fderiv one_ne_zero).continuousOn
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hDbound : ∀ x ∈ K, ‖fderiv ℝ d x‖ ≤ D := fun x hx ↦
    (hD₀ x hx).trans (le_max_left _ _)
  let χ : ℝ → ℝ := fun s ↦ 1 - Real.smoothTransition s
  have hχ : ContDiff ℝ 1 χ := contDiff_const.sub Real.smoothTransition.contDiff
  have hχ0 : χ 0 = 1 := by simp [χ]
  have hχbound : ∀ s, ‖χ s‖ ≤ 1 := fun s ↦ by
    simp only [χ, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.smoothTransition.le_one s, Real.smoothTransition.nonneg s]
  have hχzero : ∀ s, 1 ≤ s → χ s = 0 := fun s hs ↦ by
    simp only [χ, Real.smoothTransition.one_of_one_le hs, sub_self]
  let I := ∫ s : ℝ in (0 : ℝ)..1, deriv χ s ^ 2
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num)
    (fun s _ ↦ sq_nonneg (deriv χ s))
  let B := 2 * (m + 1 : ℕ) * ‖(cover.coordinates i).symm (0, 1)‖ * ‖f‖ * ‖z‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨Real.sqrt (B * (I * D)), Real.sqrt_nonneg _, fun φ hφ hsupp ↦ ?_⟩
  have hc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hsupp
  have hsq := greenPairing_sq_le_weighted_surfaceIntegral P cover i z u hu
    hpatch f hweak hK hKP hφ hsupp hχ hχ0 hχbound hχzero
  have hcsq : HasCompactSupport (fun x ↦ φ x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (hc.mul_right (f' := φ))
  have hsquare : Integrable (fun x ↦ φ x ^ 2) (surfaceMeasure Ω) :=
    (hφ.continuous.pow 2).integrable_of_hasCompactSupport hcsq
  have hweighted : Integrable (fun x ↦ φ x ^ 2 * ‖fderiv ℝ d x‖) (surfaceMeasure Ω) :=
    ((hφ.continuous.pow 2).mul (hd.continuous_fderiv one_ne_zero).norm
      ).integrable_of_hasCompactSupport hcsq.mul_right
  have hweight : (∫ x, φ x ^ 2 * ‖fderiv ℝ d x‖ ∂surfaceMeasure Ω) ≤
      D * ∫ x, φ x ^ 2 ∂surfaceMeasure Ω := by
    rw [← integral_const_mul]
    refine integral_mono hweighted (hsquare.const_mul D) fun x ↦ ?_
    by_cases hx : x ∈ tsupport φ
    · exact (mul_le_mul_of_nonneg_left (hDbound x (hsupp hx)) (sq_nonneg (φ x))).trans_eq
        (mul_comm _ _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hfinal : _ ≤ B * (I * D) * ∫ x, φ x ^ 2 ∂surfaceMeasure Ω :=
    (hsq.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hweight hI) hB)).trans_eq
      (by ring)
  exact (Real.abs_le_sqrt hfinal).trans_eq
    (Real.sqrt_mul (mul_nonneg hB (mul_nonneg hI hD)) _)

end SobolevSpace.GraphSpace.Rellich
