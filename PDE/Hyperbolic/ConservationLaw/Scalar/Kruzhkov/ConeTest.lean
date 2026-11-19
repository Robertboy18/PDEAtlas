/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.BoundaryInequality
public import PDE.Analysis.Calculus.ScaledSmoothTransition

/-!
# Smooth tests on backward cones

Two increasing transitions describe the left and right sides of a shrinking interval.
If the flux is bounded by the density times the cone speed, their spatial and temporal
contributions have the sign needed for local contraction.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common
open PDE.Analysis (scaledSmoothTransition contDiff_scaledSmoothTransition
  scaledSmoothTransition_nonneg scaledSmoothTransition_le_one scaledSmoothTransition_of_nonpos
  scaledSmoothTransition_of_le deriv_scaledSmoothTransition_nonneg)
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- A smooth approximation to the interval `[a + ct, b - ct]`. -/
def coneWeight (c a b δ : ℝ) (p : ℝ^2) : ℝ :=
  scaledSmoothTransition δ (p 1 - a - c * p 0) *
    scaledSmoothTransition δ (b - c * p 0 - p 1)

/-- The cone weight is continuously differentiable. -/
theorem contDiff_coneWeight (c a b δ : ℝ) : ContDiff ℝ 1 (coneWeight c a b δ) := by
  have ht : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 0) := (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).contDiff
  have hx : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 1) := (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).contDiff
  exact ((contDiff_scaledSmoothTransition δ (n := 1)).comp
    ((hx.sub contDiff_const).sub (contDiff_const.mul ht))).mul
      ((contDiff_scaledSmoothTransition δ (n := 1)).comp
        ((contDiff_const.sub (contDiff_const.mul ht)).sub hx))

/-- The cone weight is nonnegative. -/
theorem coneWeight_nonneg (c a b δ : ℝ) (p : ℝ^2) : 0 ≤ coneWeight c a b δ p :=
  mul_nonneg (scaledSmoothTransition_nonneg _ _) (scaledSmoothTransition_nonneg _ _)

/-- The cone weight is at most one. -/
theorem coneWeight_le_one (c a b δ : ℝ) (p : ℝ^2) : coneWeight c a b δ p ≤ 1 :=
  (mul_le_mul_of_nonneg_right (scaledSmoothTransition_le_one _ _)
    (scaledSmoothTransition_nonneg _ _)).trans (by simpa using scaledSmoothTransition_le_one _ _)

/-- The cone weight vanishes outside the shrinking interval. -/
theorem coneWeight_zero {c a b δ : ℝ} (hδ : 0 < δ) (p : ℝ^2)
    (hp : p 1 ∉ Icc (a + c * p 0) (b - c * p 0)) : coneWeight c a b δ p = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hp
  rcases hp with hp | hp
  · unfold coneWeight
    rw [scaledSmoothTransition_of_nonpos hδ (by linarith), zero_mul]
  · unfold coneWeight
    rw [scaledSmoothTransition_of_nonpos hδ (by linarith : b - c * p 0 - p 1 ≤ 0), mul_zero]

/-- The cone weight is one away from its two transition layers. -/
theorem coneWeight_one {c a b δ : ℝ} (hδ : 0 < δ) (p : ℝ^2)
    (hp : p 1 ∈ Icc (a + c * p 0 + δ) (b - c * p 0 - δ)) :
    coneWeight c a b δ p = 1 := by
  unfold coneWeight
  rw [scaledSmoothTransition_of_le hδ (by linarith [hp.1]),
    scaledSmoothTransition_of_le hδ (by linarith [hp.2]), mul_one]

/-- A compact time cutoff makes the cone weight compactly supported in spacetime. -/
theorem hasCompactSupport_time_mul_coneWeight {τ : ℝ → ℝ} (hτ : HasCompactSupport τ)
    {c a b δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun p : ℝ^2 ↦ τ (p 0) * coneWeight c a b δ p) := by
  obtain ⟨R, hR⟩ := hτ.isBounded.exists_norm_le
  let S := |a| + |b| + |c| * |R|
  have hcompact : IsCompact ((fun p : ℝ × ℝ ↦ !₂[p.1, p.2]) '' (tsupport τ ×ˢ Icc (-S) S)) :=
    (hτ.prod isCompact_Icc).image (by fun_prop)
  refine HasCompactSupport.of_support_subset_isCompact hcompact fun p hp ↦ ?_
  obtain ⟨ht, hx⟩ := mul_ne_zero_iff.mp hp
  have ht' := subset_tsupport τ ht
  have hp' : p 1 ∈ Icc (a + c * p 0) (b - c * p 0) := by_contra fun h ↦ hx (coneWeight_zero hδ p h)
  have hb : |c * p 0| ≤ |c| * |R| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hR _ ht').trans (le_abs_self R)) (abs_nonneg c)
  refine ⟨(p 0, p 1), ⟨ht', ?_⟩, ?_⟩
  · dsimp [S]
    constructor <;> nlinarith [hp'.1, hp'.2, le_abs_self a, neg_abs_le a,
      le_abs_self b, neg_abs_le b, le_abs_self (c * p 0), neg_abs_le (c * p 0),
      abs_nonneg a, abs_nonneg b]
  · ext i
    fin_cases i <;> simp

/-- A time cutoff multiplied by a shrinking spatial interval. -/
def coneTest (c a b : ℝ) {δ : ℝ} (hδ : 0 < δ) (τ : ℝ → ℝ)
    (hτ : ContDiff ℝ 1 τ) (hcτ : HasCompactSupport τ) : InitialValueTestFunction where
  toFun p := τ (p 0) * coneWeight c a b δ p
  contDiff' := (hτ.comp (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).contDiff).mul
    (contDiff_coneWeight c a b δ)
  hasCompactSupport' := hasCompactSupport_time_mul_coneWeight hcτ hδ
  tsupport_subset' := subset_univ _

/-- The differentiated cone test separates the two inward-moving boundary layers. -/
theorem integrand_coneTest (u q : ℝ^2 → ℝ) (c a b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ 1 τ) (hcτ : HasCompactSupport τ) (p : ℝ^2) :
    InteriorWeakForm.integrand u q (coneTest c a b hδ τ hτ hcτ) p =
      deriv τ (p 0) * (coneWeight c a b δ p * u p) + τ (p 0) *
        (deriv (scaledSmoothTransition δ) (p 1 - a - c * p 0) *
            scaledSmoothTransition δ (b - c * p 0 - p 1) * (q p - c * u p) +
          scaledSmoothTransition δ (p 1 - a - c * p 0) *
            deriv (scaledSmoothTransition δ) (b - c * p 0 - p 1) * (-q p - c * u p)) := by
  have ht := (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hx := (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hS : ContDiff ℝ 1 (scaledSmoothTransition δ) := contDiff_scaledSmoothTransition δ
  have hl := (hS.differentiable_one _).hasDerivAt.comp_hasFDerivAt p
    ((hx.sub_const a).sub (ht.const_mul c))
  have hr := (hS.differentiable_one _).hasDerivAt.comp_hasFDerivAt p
    (((ht.const_mul c).const_sub b).sub hx)
  have hd := ((hτ.differentiable_one _).hasDerivAt.comp_hasFDerivAt p ht).mul (hl.mul hr)
  simp only [Function.comp_def, Pi.mul_def, Pi.sub_def, EuclideanSpace.coe_proj] at hd
  unfold InteriorWeakForm.integrand partialDeriv
  change (fderiv ℝ (fun p : ℝ^2 ↦ τ (p 0) * coneWeight c a b δ p) p _ * u p +
    fderiv ℝ (fun p : ℝ^2 ↦ τ (p 0) * coneWeight c a b δ p) p _ * q p) = _
  unfold coneWeight
  rw [hd.fderiv]
  simp only [Fin.isValue, smul_add, add_apply, smul_apply, sub_apply, neg_apply, PiLp.proj_apply,
    PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, one_ne_zero, not_false_eq_true,
    PiLp.single_eq_of_ne, sub_zero, mul_neg, zero_sub, zero_ne_one, mul_zero, neg_zero, add_zero]
  ring

/-- A flux bounded by `c` times the density gives a nonpositive cone-boundary term. -/
theorem integrand_coneTest_le (u q : ℝ^2 → ℝ) (c a b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ 1 τ) (hcτ : HasCompactSupport τ) (p : ℝ^2)
    (hτp : 0 ≤ τ (p 0)) (hflux : |q p| ≤ c * u p) :
    InteriorWeakForm.integrand u q (coneTest c a b hδ τ hτ hcτ) p ≤
      deriv τ (p 0) * (coneWeight c a b δ p * u p) := by
  rw [integrand_coneTest]
  apply add_le_of_nonpos_right
  apply mul_nonpos_of_nonneg_of_nonpos hτp
  apply add_nonpos
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (deriv_scaledSmoothTransition_nonneg hδ _) (scaledSmoothTransition_nonneg _ _))
      (sub_nonpos.mpr ((le_abs_self _).trans hflux))
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (scaledSmoothTransition_nonneg _ _) (deriv_scaledSmoothTransition_nonneg hδ _))
      (sub_nonpos.mpr ((neg_le_abs _).trans hflux))

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
