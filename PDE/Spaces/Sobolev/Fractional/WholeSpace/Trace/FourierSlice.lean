/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier inversion on the boundary hyperplane

For an integrable ambient Fourier datum, its inverse transform on the last-coordinate
hyperplane is the tangential inverse transform of its normal integral. The identity is
pointwise and follows from measure-preserving coordinates and Fubini. In particular it
applies to the Fourier transform of every Schwartz function.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace FourierTransform SchwartzMap

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

/-- Pairing with a boundary point discards the normal frequency coordinate. -/
theorem inner_join_boundary {n : ℕ} (p : ℝ^n × ℝ) (y : ℝ^n) :
    ⟪joinTangentialNormal p, joinTangentialNormal (y, 0)⟫ = ⟪p.1, y⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fin.sum_univ_castSucc]
  simp only [joinTangentialNormal_castSucc, joinTangentialNormal_last, zero_mul, add_zero]

/-- Restricting an inverse Fourier integral to the hyperplane integrates out normal frequency. -/
theorem fourierInv_join_boundary {n : ℕ} {g : ℝ^(n + 1) → ℂ}
    (hg : Integrable g) (y : ℝ^n) :
    𝓕⁻ g (joinTangentialNormal (y, 0)) =
      𝓕⁻ (fun ξ : ℝ^n ↦ ∫ t : ℝ, g (joinTangentialNormal (ξ, t))) y := by
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
  have hgprod : Integrable (fun p : ℝ^n × ℝ ↦ g (joinTangentialNormal p))
      ((volume : Measure ℝ^n).prod (volume : Measure ℝ)) := by
    simpa only [Function.comp_def, tangentialNormalMeasurableEquiv_symm_apply,
      Measure.volume_eq_prod] using
      hm.integrable_comp_of_integrable hg
  have hphase : Integrable (fun p : ℝ^n × ℝ ↦
      Real.fourierChar ⟪p.1, y⟫ • g (joinTangentialNormal p))
      ((volume : Measure ℝ^n).prod (volume : Measure ℝ)) := by
    apply hgprod.norm.mono'
    · exact (Real.continuous_fourierChar.comp
        (continuous_fst.inner continuous_const)).aestronglyMeasurable.smul
        hgprod.aestronglyMeasurable
    · filter_upwards with p
      simp only [Circle.norm_smul, le_refl]
  rw [Real.fourierInv_eq, ← hm.integral_comp
    tangentialNormalMeasurableEquiv.symm.measurableEmbedding]
  simp only [tangentialNormalMeasurableEquiv_symm_apply, inner_join_boundary]
  rw [Measure.volume_eq_prod, integral_prod _ hphase, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Circle.smul_def]
  exact integral_smul _ _

/-- Classical boundary values of a Schwartz function are recovered from its normal Fourier
integral, with the project's `2π` Fourier normalization. -/
theorem schwartz_boundary_eq_fourierInv_normal {n : ℕ}
    (f : 𝓢(ℝ^(n + 1), ℂ)) (y : ℝ^n) :
    f (joinTangentialNormal (y, 0)) =
      𝓕⁻ (fun ξ : ℝ^n ↦ ∫ t : ℝ,
        (𝓕 f : 𝓢(ℝ^(n + 1), ℂ)) (joinTangentialNormal (ξ, t))) y := by
  rw [← fourierInv_join_boundary (𝓕 f).integrable]
  rw [← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]

end SobolevSpace.Fractional.Trace
