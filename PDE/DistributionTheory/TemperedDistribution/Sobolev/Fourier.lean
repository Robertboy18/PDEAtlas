/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Sobolev.WeakDerivatives
public import PDE.DistributionTheory.TemperedDistribution.Fourier.Derivatives

/-!
# Fourier characterization of weak derivatives

For an `L²` function, a specified weak derivative belongs to `L²` exactly when the
corresponding polynomial multiple of its Fourier transform does. The derivative is
then recovered by inverse Fourier transformation. This works at any order without
assuming that lower-order derivatives have already been constructed.

The factors `2πi` follow Mathlib's Fourier convention.
-/

@[expose] public noncomputable section

open FourierTransform MeasureTheory Set PDE
open scoped SchwartzMap

namespace SobolevSpace

/-- A weak derivative of an `L²` function has the expected Fourier multiplier,
with one factor `2πi ξᵢ` for each differentiation in coordinate `i`. -/
theorem hasComplexWeakDerivativeOn_iff_fourier {n : ℕ} (α : List (Fin n))
    (u v : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    HasComplexWeakDerivativeOn univ α u v ↔
      (fun ξ ↦ (∏ j : Fin α.length,
          (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)) *
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) =ᵐ[volume]
          (𝓕 v : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  rw [hasComplexWeakDerivativeOn_iff_temperedDerivative,
    TemperedDistribution.iteratedLineDerivOp_eq_iff_fourier]
  simp [EuclideanSpace.inner_single_right, smul_eq_mul]

/-- Square-integrability of the Fourier multiplier is sufficient as well as necessary
for a weak derivative in `L²`. The inverse transform constructs its representative. -/
theorem exists_hasComplexWeakDerivativeOn_iff_memLp_fourier {n : ℕ}
    (α : List (Fin n)) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∃ v : Lp ℂ 2 (volume : Measure (ℝ^n)),
      HasComplexWeakDerivativeOn univ α u v) ↔
      MemLp (fun ξ ↦ (∏ j : Fin α.length,
          (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)) *
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume := by
  constructor
  · rintro ⟨v, hv⟩
    exact (memLp_congr_ae ((hasComplexWeakDerivativeOn_iff_fourier α u v).1 hv)).2
      (Lp.memLp (𝓕 v))
  · intro h
    refine ⟨𝓕⁻ (h.toLp _), (hasComplexWeakDerivativeOn_iff_fourier α u _).2 ?_⟩
    simpa only [fourier_fourierInv_eq] using h.coeFn_toLp.symm

/-- Polynomial moments of the input give weak derivatives of its Fourier transform.
The negative sign comes from differentiating the Fourier exponential in frequency. -/
theorem hasComplexWeakDerivativeOn_fourier_iff {n : ℕ} (α : List (Fin n))
    (u v : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    HasComplexWeakDerivativeOn univ α
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) v ↔
      (fun x ↦ (∏ j : Fin α.length,
          -(2 * Real.pi * Complex.I) * (x (α.get j) : ℂ)) * u x) =ᵐ[volume]
        (𝓕⁻ v : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  rw [hasComplexWeakDerivativeOn_iff_temperedDerivative,
    ← Lp.fourier_toTemperedDistribution_eq,
    TemperedDistribution.iteratedLineDerivOp_fourier_eq_iff]
  simp [EuclideanSpace.inner_single_right, smul_eq_mul]

/-- A specified weak derivative of the Fourier transform belongs to `L²` exactly
when the corresponding polynomial moment of the original function belongs to `L²`. -/
theorem exists_hasComplexWeakDerivativeOn_fourier_iff_memLp {n : ℕ}
    (α : List (Fin n)) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∃ v : Lp ℂ 2 (volume : Measure (ℝ^n)),
      HasComplexWeakDerivativeOn univ α
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) v) ↔
      MemLp (fun x ↦ (∏ j : Fin α.length,
        -(2 * Real.pi * Complex.I) * (x (α.get j) : ℂ)) * u x) 2 volume := by
  constructor
  · rintro ⟨v, hv⟩
    exact (memLp_congr_ae ((hasComplexWeakDerivativeOn_fourier_iff α u v).1 hv)).2
      (Lp.memLp (𝓕⁻ v))
  · intro h
    refine ⟨𝓕 (h.toLp _), (hasComplexWeakDerivativeOn_fourier_iff α u _).2 ?_⟩
    simpa only [fourierInv_fourier_eq] using h.coeFn_toLp.symm

end SobolevSpace
