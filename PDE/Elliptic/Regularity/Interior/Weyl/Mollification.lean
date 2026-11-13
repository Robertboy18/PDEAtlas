/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import PDE.DistributionTheory.TestFunction.IntegrationByParts
public import PDE.Elliptic.Classical.Harmonic.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.FDeriv.Calculus.Convolution
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives

/-!
# Localized mollifications of distributionally harmonic functions

A compactly supported cutoff makes locally integrable data globally integrable. Where the
cutoff is one throughout a reflected kernel support, the convolution is classically harmonic.
The proof tests the distributional equation with that reflected kernel; two coordinate
derivatives contribute two minus signs.

No continuity, Sobolev membership, or boundary trace of the original function is assumed.
This is the smoothing step in local Weyl regularity, before identifying an almost-everywhere
representative.
-/

@[expose] public section

open PDE (laplacian iteratedPartialDeriv)

open MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions

namespace LaplacianEquation

/-- A localized convolution of distributionally harmonic `L¹_loc` data is harmonic wherever
the cutoff equals one on every reflected kernel support.

The open set is carried by the canonical test-function space. The output set `V` need not be
open: the convolution is smooth on the entire Euclidean space. -/
theorem isHarmonicPDE_convolution_cutoff_of_integral_laplacian_eq_zero
    {n : ℕ} {Ω : Opens (ℝ^n)} {u k : ℝ^n → ℝ} {V : Set (ℝ^n)}
    (hu : LocallyIntegrableOn u Ω volume)
    (hweak : ∀ φ : 𝓓(Ω, ℝ), (∫ y, u y * laplacian (φ : ℝ^n → ℝ) y) = 0)
    (χ : 𝓓(Ω, ℝ)) (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hks : HasCompactSupport k)
    (hflat : ∀ x ∈ V, ∀ y, x - y ∈ tsupport k → χ y = 1) :
    IsHarmonicPDE n ((fun y ↦ χ y * u y) ⋆[ContinuousLinearMap.mul ℝ ℝ] k) V := by
  have hχu : Integrable (fun y ↦ χ y * u y) :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu χ
  have hk2 : ContDiff ℝ 2 k :=
    hk.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨(hks.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hχu.locallyIntegrable hk2).contDiffOn, ?_⟩
  intro x hx
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^n ↦ x - y) := by fun_prop
  have hreflect_support :
      tsupport (fun y ↦ k (x - y)) ⊆ (fun y ↦ x - y) ⁻¹' tsupport k :=
    tsupport_comp_subset_preimage k hsub.continuous
  have hreflect_domain : tsupport (fun y ↦ k (x - y)) ⊆ Ω := by
    intro y hy
    have hχ : χ y = 1 := hflat x hx y (hreflect_support hy)
    apply χ.tsupport_subset
    apply subset_tsupport (χ : ℝ^n → ℝ)
    change χ y ≠ 0
    rw [hχ]
    exact one_ne_zero
  let φ : 𝓓(Ω, ℝ) :=
    { toFun := fun y ↦ k (x - y)
      contDiff' := hk.comp hsub
      hasCompactSupport' := hks.comp_homeomorph (Homeomorph.subLeft x)
      tsupport_subset' := hreflect_domain }
  have hΔφ (y : ℝ^n) : laplacian (φ : ℝ^n → ℝ) y = laplacian k (x - y) := by
    change laplacian (fun z : ℝ^n ↦ k (x - z)) y = laplacian k (x - y)
    unfold laplacian
    apply Finset.sum_congr rfl
    intro i _
    simpa [iteratedPartialDeriv] using
      SobolevSpace.Approximation.iteratedPartialDeriv_comp_const_sub [i, i] hk x y
  calc
    laplacian ((fun y ↦ χ y * u y) ⋆[ContinuousLinearMap.mul ℝ ℝ] k) x =
        ((fun y ↦ χ y * u y) ⋆[ContinuousLinearMap.mul ℝ ℝ] laplacian k) x :=
      PDE.laplacian_convolution_right hχu.locallyIntegrable hks hk2 x
    _ = ∫ y, u y * laplacian (φ : ℝ^n → ℝ) y := by
      simp only [convolution_def, ContinuousLinearMap.mul_apply']
      apply integral_congr_ae
      filter_upwards with y
      rw [← hΔφ]
      by_cases hy : y ∈ tsupport (φ : ℝ^n → ℝ)
      · have hχ : χ y = 1 := hflat x hx y (hreflect_support hy)
        rw [hχ, one_mul]
      · have hΔzero : laplacian (φ : ℝ^n → ℝ) y = 0 := by
          by_contra hne
          exact hy (φ.support_laplacian_subset hne)
        rw [hΔzero, mul_zero, mul_zero]
    _ = 0 := hweak φ

end LaplacianEquation
