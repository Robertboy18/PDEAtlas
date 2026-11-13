/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.Energy
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Lebesgue integrability of the derivative from the partial derivatives

The operator norm of the derivative of a map on `ℝⁿ` is at most the sum of the norms of its
partial derivatives, so a continuously differentiable map whose partial derivatives lie in
`Lᵖ` has its derivative in `Lᵖ` (`memLp_fderiv_of_memLp_partialDeriv`), with
`‖Df‖_{Lᵖ} ≤ Σᵢ ‖∂ᵢf‖_{Lᵖ}` for `p ≥ 1` (`toReal_eLpNorm_fderiv_le_sum`). The derivative is in
`Lᵖ` exactly when the first iterated derivative is (`memLp_fderiv_of_memLp_iteratedFDeriv_one`),
and a linear map on `ℝⁿ` acts in coordinates by its columns
(`ContinuousLinearMap.apply_eq_sum_mul_apply_single`).
-/

@[expose] public section

open MeasureTheory

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- A continuously differentiable map on `ℝⁿ` whose partial derivatives lie in `Lᵖ` has its
derivative in `Lᵖ`. -/
theorem memLp_fderiv_of_memLp_partialDeriv {f : ℝ^n → F} (hf : ContDiff ℝ 1 f) {p : ENNReal}
    (h : ∀ i : Fin n, MemLp (∂[i] f) p volume) : MemLp (fderiv ℝ f) p volume := by
  have hsum : MemLp (fun x ↦ ∑ i : Fin n, ‖(∂[i] f) x‖) p volume :=
    memLp_finsetSum _ fun i _ ↦ (h i).norm
  refine hsum.of_le (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]
  exact norm_fderiv_le_sum_norm_partialDeriv f x

/-- For `p ≥ 1`, the `Lᵖ` norm of the derivative of a continuously differentiable map on `ℝⁿ` is
at most the sum of the `Lᵖ` norms of its partial derivatives. -/
theorem toReal_eLpNorm_fderiv_le_sum {f : ℝ^n → F} (hf : ContDiff ℝ 1 f) {p : ENNReal}
    (hp : 1 ≤ p) (h : ∀ i : Fin n, MemLp (∂[i] f) p volume) :
    (eLpNorm (fderiv ℝ f) p volume).toReal ≤ ∑ i : Fin n, (eLpNorm (∂[i] f) p volume).toReal := by
  have h₁ : eLpNorm (fderiv ℝ f) p volume ≤
      eLpNorm (fun x ↦ ∑ i : Fin n, ‖(∂[i] f) x‖) p volume :=
    eLpNorm_mono_real (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
      fun x ↦ norm_fderiv_le_sum_norm_partialDeriv f x
  have h₂ : eLpNorm (fun x ↦ ∑ i : Fin n, ‖(∂[i] f) x‖) p volume ≤
      ∑ i : Fin n, eLpNorm (∂[i] f) p volume := by
    have hsum := eLpNorm_sum_le (μ := volume) (s := Finset.univ)
      (f := fun i x ↦ ‖(∂[i] f) x‖) hp
    have hs : (∑ i : Fin n, fun x ↦ ‖(∂[i] f) x‖) = fun x ↦ ∑ i : Fin n, ‖(∂[i] f) x‖ := by
      funext x
      simp [Finset.sum_apply]
    rw [hs] at hsum
    refine hsum.trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
    exact eLpNorm_norm (∂[i] f) (h i).aestronglyMeasurable
  have hfin : ∑ i : Fin n, eLpNorm (∂[i] f) p volume ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ ↦ (h i).eLpNorm_ne_top
  rw [← ENNReal.toReal_sum fun i _ ↦ (h i).eLpNorm_ne_top]
  exact ENNReal.toReal_mono hfin (h₁.trans h₂)

/-- A continuously differentiable map whose first iterated derivative is in `Lᵖ` has its
derivative in `Lᵖ`. -/
theorem memLp_fderiv_of_memLp_iteratedFDeriv_one {f : ℝ^n → F} (hf : ContDiff ℝ 1 f)
    {p : ENNReal} (h : MemLp (iteratedFDeriv ℝ 1 f) p volume) : MemLp (fderiv ℝ f) p volume :=
  h.of_le (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_one])

end PDE

/-- A continuous linear map between Euclidean spaces in coordinates:
`(L w)ⱼ = Σᵢ wᵢ (L eᵢ)ⱼ`. -/
theorem ContinuousLinearMap.apply_eq_sum_mul_apply_single {m : ℕ} (L : ℝ^n →L[ℝ] ℝ^m)
    (w : ℝ^n) (j : Fin m) :
    L w j = ∑ i : Fin n, w i * L (EuclideanSpace.single i 1) j := by
  have hw : w = ∑ i : Fin n, w i • EuclideanSpace.single i (1 : ℝ) := by
    ext l
    simp [Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, map_smul]
