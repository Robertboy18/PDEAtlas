/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
public import PDE.FDeriv.Calculus.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Mollifying a weakly closed field

A distributional equality `∂ᵢ f = ∂ⱼ g` becomes an equality of classical
derivatives after convolution, at every point where the reflected kernel is
supported in the domain. Neither component is assumed to have a weak derivative
represented by a function. The reflected kernel is a smooth test
function, and the two minus signs cancel in its first derivatives.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions

namespace SobolevSpace

variable {n : ℕ}

/-- Convolution preserves an equality of distributional coordinate derivatives
where the translated kernel fits inside the testing domain. -/
theorem partialDeriv_convolution_eq_of_weakly_closed
    {Ω : Set (ℝ^n)} {f g k : ℝ^n → ℝ} (i j : Fin n)
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k)
    (hweak : ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      (∫ y, f y * (∂[i] (φ : ℝ^n → ℝ)) y) = ∫ y, g y * (∂[j] (φ : ℝ^n → ℝ)) y)
    (x : ℝ^n) (hx : tsupport (fun y ↦ k (x - y)) ⊆ Ω) :
    (∂[i] (f ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x =
      (∂[j] (g ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x := by
  let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    { toFun := fun y ↦ k (x - y)
      contDiff' := hk.comp (contDiff_const.sub contDiff_id)
      hasCompactSupport' := hkc.comp_homeomorph (Homeomorph.subLeft x)
      tsupport_subset' := subset_univ _ }
  have hsign (a : Fin n) :
      (fun y ↦ (∂[a] (φ : ℝ^n → ℝ)) y) = fun y ↦ -(∂[a] k) (x - y) := by
    funext y
    change (∂[a] (fun z ↦ k (x - z))) y = -(∂[a] k) (x - y)
    simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
      zero_add, pow_one, neg_one_mul] using
      Approximation.iteratedPartialDeriv_comp_const_sub [a] hk x y
  have h := hweak φ hx
  simp only [hsign, mul_neg, integral_neg] at h
  have heq := neg_injective h
  rw [PDE.partialDeriv_convolution_right i x hf hkc (hk.of_le (by simp)),
    PDE.partialDeriv_convolution_right j x hg hkc (hk.of_le (by simp))]
  simpa only [convolution_def, ContinuousLinearMap.mul_apply'] using heq

/-- A compact mollifier preserves weak closedness at points with a full kernel
ball in the domain. The radius condition follows from the support of the
kernel, rather than from a regularity assumption on the data. -/
theorem partialDeriv_mollify_eq_of_weakly_closed
    {Ω : Set (ℝ^n)} {f g : ℝ^n → ℝ} (i j : Fin n)
    (μ : Approximation.Mollifier n) {ε R : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall 0 R)
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hweak : ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      (∫ y, f y * (∂[i] (φ : ℝ^n → ℝ)) y) = ∫ y, g y * (∂[j] (φ : ℝ^n → ℝ)) y)
    (x : ℝ^n) (hx : Metric.closedBall x (ε * R) ⊆ Ω) :
    (∂[i] (Approximation.mollify μ ε f)) x =
      (∂[j] (Approximation.mollify μ ε g)) x := by
  let k := Approximation.scaled μ ε
  have hsupport : tsupport (fun y ↦ k (x - y)) ⊆ Ω := by
    apply (closure_minimal ?_ Metric.isClosed_closedBall).trans hx
    intro y hy
    have hxy := Approximation.support_scaled_subset_closedBall μ hε hR hy
    simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero,
      norm_sub_rev] using hxy
  have hcomm (v : ℝ^n → ℝ) :
      Approximation.mollify μ ε v =
        v ⋆[ContinuousLinearMap.mul ℝ ℝ] k := by
    funext z
    rw [Approximation.mollify, Approximation.convolution_lsmul_eq_mul,
      convolution_mul_swap]
    simp only [convolution_def, ContinuousLinearMap.mul_apply', mul_comm, k]
  rw [hcomm f, hcomm g]
  exact partialDeriv_convolution_eq_of_weakly_closed i j hf hg
    (Approximation.scaled_contDiff μ)
    (Approximation.scaled_hasCompactSupport μ hε) hweak x hsupport

end SobolevSpace
