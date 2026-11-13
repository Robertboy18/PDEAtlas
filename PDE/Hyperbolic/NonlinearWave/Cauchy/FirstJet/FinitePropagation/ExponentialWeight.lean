/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors

/-!
# Exponential localization weights

Exponentiating the standard expanding cutoff gives a positive bounded
Sobolev weight equal to one on the inner ball and exponentially small outside
the outer ball. Its relative gradient grows only linearly in the exponent.
These are the weights used to pass from energy stability to local agreement.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

variable {n : ℕ}

/-- One constant controls all first derivatives of the expanding cutoff. -/
theorem exists_cutoff_gradient_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ (i : Fin n) (x : ℝ^n), |(∂[i] (cutoff R)) x| ≤ C / R := by
  classical
  choose c hc hb using fun i : Fin n ↦ exists_abs_iteratedPartialDeriv_cutoff_le [i]
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ ↦ hc i), fun R hR i x ↦ ?_⟩
  have hi := hb i R hR x
  simp only [List.length_singleton, pow_one, iteratedPartialDeriv] at hi
  exact hi.trans (by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ ↦ hc j) (Finset.mem_univ i)) (inv_nonneg.mpr hR.le))

/-- A smooth weight with exponential suppression beyond the cutoff support. -/
def exponentialCutoff (R σ : ℝ) (x : ℝ^n) : ℝ :=
  Real.exp (σ * (cutoff R x - 1))

/-- The exponential cutoff is smooth in space. -/
theorem exponentialCutoff_contDiff (R σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (exponentialCutoff (n := n) R σ) :=
  (contDiff_const.mul ((cutoff_contDiff R).sub contDiff_const)).exp

/-- The exponential weight lies between zero and one. -/
theorem exponentialCutoff_bounds (R : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (x : ℝ^n) :
    0 < exponentialCutoff R σ x ∧ exponentialCutoff R σ x ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonneg_of_nonpos hσ (sub_nonpos.mpr (cutoff_le_one R x))

/-- On the inner ball there is no damping. -/
theorem exponentialCutoff_eq_one {R : ℝ} (hR : 0 < R) (σ : ℝ) {x : ℝ^n}
    (hx : x ∈ Metric.closedBall 0 R) : exponentialCutoff R σ x = 1 := by
  simp only [exponentialCutoff, cutoff_eq_one_of_mem_closedBall hR hx,
    sub_self, mul_zero, Real.exp_zero]

/-- Outside the outer ball the damping is the constant exponential factor. -/
theorem exponentialCutoff_eq_exp_neg {R : ℝ} (hR : 0 < R) (σ : ℝ) {x : ℝ^n}
    (hx : x ∉ Metric.closedBall 0 (2 * R)) :
    exponentialCutoff R σ x = Real.exp (-σ) := by
  have hz : cutoff R x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ hx (tsupport_cutoff_subset_closedBall hR h))
  simp only [exponentialCutoff, hz, zero_sub, mul_neg, mul_one]

/-- The relative coordinate derivative is the exponent times the cutoff derivative. -/
theorem partialDeriv_exponentialCutoff (R σ : ℝ) (i : Fin n) (x : ℝ^n) :
    (∂[i] (exponentialCutoff R σ)) x = σ * (∂[i] (cutoff R)) x * exponentialCutoff R σ x := by
  have h := ((((cutoff_contDiff R).differentiable (by simp)).differentiableAt
    (x := x)).hasFDerivAt.sub_const (1 : ℝ)).const_mul σ |>.exp
  change fderiv ℝ (exponentialCutoff R σ) x (EuclideanSpace.single i 1) = _
  unfold exponentialCutoff
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, PDE.partialDeriv]
  ac_rfl

/-- The exponential cutoff defines a bounded first-order Sobolev multiplier,
with the relative derivative estimate used by weighted energy stability. -/
theorem exists_exponentialCutoff_multiplier {C R σ : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hgrad : ∀ (i : Fin n) (x : ℝ^n), |(∂[i] (cutoff R)) x| ≤ C / R) :
    ∃ χ : W^{1,∞}(ℝ^n),
      ((χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n univ] exponentialCutoff R σ ∧
      (∀ᵐ x ∂domainMeasure n univ,
        0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x) ∧
      ∀ i : Fin n, ∀ᵐ x ∂domainMeasure n univ,
        |(χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) x| ≤
          (σ * (C / R)) * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x := by
  have hrelative (i : Fin n) (x : ℝ^n) :
      |(∂[i] (exponentialCutoff R σ)) x| ≤
        (σ * (C / R)) * exponentialCutoff R σ x := by
    rw [partialDeriv_exponentialCutoff, abs_mul, abs_mul, abs_of_nonneg hσ,
      abs_of_pos (exponentialCutoff_bounds R hσ x).1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgrad i x) hσ)
      (exponentialCutoff_bounds R hσ x).1.le
  have hm (a : DerivIndex n 1) : MemLp
      (fun x ↦ iteratedPartialDeriv a.toList (exponentialCutoff R σ) x)
      ∞ (domainMeasure n univ) := by
    have hc := (contDiff_top_iteratedPartialDeriv
      (exponentialCutoff_contDiff (n := n) R σ) a.toList).continuous
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · apply memLp_top_of_bound hc.aestronglyMeasurable 1
      filter_upwards [] with x
      simpa only [baseIndex_toList, iteratedPartialDeriv, Real.norm_eq_abs,
        abs_of_pos (exponentialCutoff_bounds R hσ x).1] using (exponentialCutoff_bounds R hσ x).2
    · apply memLp_top_of_bound hc.aestronglyMeasurable (σ * (C / R))
      filter_upwards [] with x
      simp only [singleDerivIndex_toList, iteratedPartialDeriv, Real.norm_eq_abs]
      exact (hrelative i x).trans (mul_le_of_le_one_right
        (mul_nonneg hσ (div_nonneg hC hR.le)) (exponentialCutoff_bounds R hσ x).2)
  let χ : W^{1,∞}(ℝ^n) := mkWkpSpaceOnOfContDiffMemLp
    (exponentialCutoff R σ) (exponentialCutoff_contDiff R σ) hm
  have hbase : ((χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n univ] exponentialCutoff R σ := by
    simpa only [baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiffMemLp_apply_ae (exponentialCutoff R σ)
        (exponentialCutoff_contDiff R σ) hm (baseIndex n 1)
  refine ⟨χ, hbase, ?_, ?_⟩
  · filter_upwards [hbase] with x hx
    rw [hx]
    exact (exponentialCutoff_bounds R hσ x).1.le
  · intro i
    have hi := mkWkpSpaceOnOfContDiffMemLp_apply_ae (exponentialCutoff R σ)
      (exponentialCutoff_contDiff R σ) hm (singleDerivIndex n i)
    filter_upwards [hbase, hi] with x hx hxi
    change (χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) x =
      iteratedPartialDeriv (singleDerivIndex n i).toList (exponentialCutoff R σ) x at hxi
    rw [hxi, hx]
    simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hrelative i x

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
