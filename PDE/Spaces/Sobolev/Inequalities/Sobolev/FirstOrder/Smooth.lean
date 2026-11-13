/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff.FDeriv

/-!
# Sobolev inequalities for noncompact continuously differentiable functions

Expanding cutoffs extend homogeneous Sobolev inequalities from compactly supported
functions to `C¹ ∩ Lᵖ`. The product rule contributes an error bounded by
`K / R * ‖f‖ₚ`, which vanishes as the radius grows. Fatou's lemma preserves the
constant in the compact-support inequality.

The derivative norm in the extended-norm inequality may be infinite. Its finiteness
gives membership in the target Lebesgue space and a real-valued norm bound.

The inner-product-target results apply to real and complex functions and to
possibly infinite-dimensional Hilbert targets. A second set of results allows any
finite-dimensional normed target, using Mathlib's corresponding norm-equivalence
constant. Neither set requires a bundled Sobolev-space input.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace SobolevSpace.Inequalities

open Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem eLpNorm_fderiv_cutoff_smul_le (μ : Measure ℝ^n)
    {f : ℝ^n → F} (hf : ContDiff ℝ 1 f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (R : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcut : ∀ x : ℝ^n, ‖fderiv ℝ (cutoff R) x‖ ≤ K) :
    eLpNorm (fderiv ℝ (fun x ↦ cutoff R x • f x)) p μ ≤
      eLpNorm (fderiv ℝ f) p μ + ENNReal.ofReal K * eLpNorm f p μ := by
  have hpoint (x : ℝ^n) :
      ‖fderiv ℝ (fun y ↦ cutoff R y • f y) x‖ ≤ ‖fderiv ℝ f x‖ + K * ‖f x‖ := by
    change ‖fderiv ℝ (cutoff (n := n) R • f) x‖ ≤ _
    rw [fderiv_smul ((cutoff_contDiff R).differentiable (by simp) x)
      (hf.differentiable (by simp) x)]
    calc
      ‖cutoff R x • fderiv ℝ f x + (fderiv ℝ (cutoff R) x).smulRight (f x)‖
          ≤ ‖cutoff R x • fderiv ℝ f x‖ +
            ‖(fderiv ℝ (cutoff R) x).smulRight (f x)‖ := norm_add_le _ _
      _ = cutoff R x * ‖fderiv ℝ f x‖ + ‖fderiv ℝ (cutoff R) x‖ * ‖f x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg R x),
          ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1 * ‖fderiv ℝ f x‖ + K * ‖f x‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right (cutoff_le_one R x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hcut x) (norm_nonneg _))
      _ = ‖fderiv ℝ f x‖ + K * ‖f x‖ := by rw [one_mul]
  calc
    eLpNorm (fderiv ℝ (fun x ↦ cutoff R x • f x)) p μ
        ≤ eLpNorm (fun x ↦ ‖fderiv ℝ f x‖ + K * ‖f x‖) p μ :=
      eLpNorm_mono_real
        ((((cutoff_contDiff R).of_le (by simp)).smul hf).continuous_fderiv
          (by simp)).aestronglyMeasurable hpoint
    _ ≤ eLpNorm (fun x ↦ ‖fderiv ℝ f x‖) p μ +
        eLpNorm (fun x ↦ K * ‖f x‖) p μ := eLpNorm_add_le hp
    _ = eLpNorm (fderiv ℝ f) p μ + ENNReal.ofReal K * eLpNorm f p μ := by
      rw [eLpNorm_norm _ (hf.continuous_fderiv (by simp)).aestronglyMeasurable]
      change _ + eLpNorm (K • (fun x ↦ ‖f x‖)) p μ = _
      rw [eLpNorm_const_smul, eLpNorm_norm _ hf.continuous.aestronglyMeasurable,
        Real.enorm_eq_ofReal hK]

/-- A homogeneous first-derivative estimate for compactly supported `C¹` functions
extends, with the same constant, to `C¹ ∩ Lᵖ`. No integrability assumption on the
derivative is needed for this extended-norm inequality. -/
theorem eLpNorm_le_of_compactSupport_estimate (μ : Measure ℝ^n)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) {C : ℝ≥0}
    (hcompact : ∀ g : ℝ^n → F, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm g q μ ≤ C * eLpNorm (fderiv ℝ g) p μ)
    {f : ℝ^n → F} (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) :
    eLpNorm f q μ ≤ C * eLpNorm (fderiv ℝ f) p μ := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_fderiv_cutoff_le (n := n)
  let D := eLpNorm (fderiv ℝ f) p μ
  let M := eLpNorm f p μ
  let u : ℕ → ℝ^n → F := fun j x ↦ cutoff (j : ℝ) x • f x
  have hu (j : ℕ) : ContDiff ℝ 1 (u j) :=
    ((cutoff_contDiff (j : ℝ)).of_le (by simp)).smul hf
  have hpoint (x : ℝ^n) : Tendsto (fun j ↦ u j x) atTop (𝓝 (f x)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_cutoff_eq_one tendsto_natCast_atTop_atTop x] with j hj
    simp only [u, hj, one_smul]
  have hfatou : eLpNorm f q μ ≤ atTop.liminf (fun j ↦ eLpNorm (u j) q μ) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j ↦ (hu j).continuous.aestronglyMeasurable)
      f hf.continuous.aestronglyMeasurable (Eventually.of_forall hpoint)
  have hbound : ∀ᶠ j : ℕ in atTop,
      eLpNorm (u j) q μ ≤ C * (D + ENNReal.ofReal (K / (j : ℝ)) * M) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    have hjR : 0 < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hj)
    exact (hcompact (u j) (hu j) (cutoff_hasCompactSupport hjR.ne').smul_right).trans
      (mul_le_mul_right
        (eLpNorm_fderiv_cutoff_smul_le μ hf hp (j : ℝ)
          (div_nonneg hK hjR.le) (hcut j hjR)) C)
  have herr : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (K / (j : ℝ)) * M) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat K))
      (Or.inr hfp.eLpNorm_ne_top)
  have hsum : Tendsto (fun j : ℕ ↦ D + ENNReal.ofReal (K / (j : ℝ)) * M)
      atTop (𝓝 (D + 0)) := tendsto_const_nhds.add herr
  have hlimit : Tendsto (fun j : ℕ ↦ C * (D + ENNReal.ofReal (K / (j : ℝ)) * M))
      atTop (𝓝 (C * D)) := by
    simpa only [add_zero] using ENNReal.Tendsto.const_mul hsum
      (Or.inr (show (C : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top))
  exact hfatou.trans ((Filter.liminf_le_liminf hbound).trans_eq hlimit.liminf_eq)

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (μ : Measure ℝ^n) [Measure.IsAddHaarMeasure μ] {p q : ℝ≥0} {f : ℝ^n → H}

/-- The noncompact Gagliardo–Nirenberg–Sobolev inequality for a real inner-product
target. The relation `q⁻¹ = p⁻¹ - n⁻¹` gives the usual exponent `q = np/(n-p)`
when `1 ≤ p < n`. The derivative norm may be infinite. -/
theorem eLpNorm_le_eLpNorm_fderiv_of_memLp_inner
    (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) (hp : 1 ≤ p) (hn : 0 < n)
    (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    eLpNorm f q μ ≤ eLpNormLESNormFDerivOfEqInnerConst μ p * eLpNorm (fderiv ℝ f) p μ := by
  refine eLpNorm_le_of_compactSupport_estimate μ (by exact_mod_cast hp) ?_ hf hfp
  intro g hg hgc
  exact eLpNorm_le_eLpNorm_fderiv_of_eq_inner μ hg hgc hp (by simpa using hn)
    (by simpa using hq)

/-- A continuously differentiable function whose value and derivative are in `Lᵖ`
belongs to the Sobolev-conjugate Lebesgue space, for any real inner-product target. -/
theorem memLp_of_memLp_fderiv_inner
    (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) (hDf : MemLp (fderiv ℝ f) p μ)
    (hp : 1 ≤ p) (hn : 0 < n) (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    MemLp f q μ :=
  (eLpNorm_le_eLpNorm_fderiv_of_memLp_inner μ hf hfp hp hn hq).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hDf.eLpNorm_lt_top)

/-- The real-valued homogeneous Sobolev norm estimate for a noncompact
inner-product-valued function with both `Lᵖ` norms finite. -/
theorem eLpNorm_toReal_le_eLpNorm_fderiv_of_memLp_inner
    (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) (hDf : MemLp (fderiv ℝ f) p μ)
    (hp : 1 ≤ p) (hn : 0 < n) (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    (eLpNorm f q μ).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst μ p : ℝ) * (eLpNorm (fderiv ℝ f) p μ).toReal := by
  have hfinite :
      (eLpNormLESNormFDerivOfEqInnerConst μ p : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p μ ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hDf.eLpNorm_lt_top).ne
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using
    ENNReal.toReal_mono hfinite
      (eLpNorm_le_eLpNorm_fderiv_of_memLp_inner μ hf hfp hp hn hq)

end InnerProduct

section FiniteDimensional

variable [FiniteDimensional ℝ F] (μ : Measure ℝ^n) [Measure.IsAddHaarMeasure μ]
  {p q : ℝ≥0} {f : ℝ^n → F}

/-- The noncompact Gagliardo–Nirenberg–Sobolev inequality for a finite-dimensional
normed target, with Mathlib's norm-equivalence constant. -/
theorem eLpNorm_le_eLpNorm_fderiv_of_memLp
    (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) (hp : 1 ≤ p) (hn : 0 < n)
    (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    eLpNorm f q μ ≤ SNormLESNormFDerivOfEqConst F μ p * eLpNorm (fderiv ℝ f) p μ := by
  refine eLpNorm_le_of_compactSupport_estimate μ (by exact_mod_cast hp) ?_ hf hfp
  intro g hg hgc
  exact eLpNorm_le_eLpNorm_fderiv_of_eq μ hg hgc hp (by simpa using hn)
    (by simpa using hq)

/-- Finite-dimensional normed targets also admit the noncompact Sobolev
Lebesgue-space inclusion. -/
theorem memLp_of_memLp_fderiv
    (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) (hDf : MemLp (fderiv ℝ f) p μ)
    (hp : 1 ≤ p) (hn : 0 < n) (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    MemLp f q μ :=
  (eLpNorm_le_eLpNorm_fderiv_of_memLp μ hf hfp hp hn hq).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hDf.eLpNorm_lt_top)

/-- The real-valued noncompact Sobolev estimate for finite-dimensional normed
targets when the value and derivative are both in `Lᵖ`. -/
theorem eLpNorm_toReal_le_eLpNorm_fderiv_of_memLp
    (hf : ContDiff ℝ 1 f) (hfp : MemLp f p μ) (hDf : MemLp (fderiv ℝ f) p μ)
    (hp : 1 ≤ p) (hn : 0 < n) (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    (eLpNorm f q μ).toReal ≤
      (SNormLESNormFDerivOfEqConst F μ p : ℝ) * (eLpNorm (fderiv ℝ f) p μ).toReal := by
  have hfinite :
      (SNormLESNormFDerivOfEqConst F μ p : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p μ ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hDf.eLpNorm_lt_top).ne
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using
    ENNReal.toReal_mono hfinite
      (eLpNorm_le_eLpNorm_fderiv_of_memLp μ hf hfp hp hn hq)

end FiniteDimensional

end SobolevSpace.Inequalities
