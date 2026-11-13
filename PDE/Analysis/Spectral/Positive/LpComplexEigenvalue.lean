/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.PositiveOperator
public import PDE.Analysis.MeasureTheory.Lp.PositivePairing

/-!
# Complex eigenvalue comparison for positive `L²` operators

An everywhere positive adjoint weight compares a complex eigenvector with
its pointwise modulus. The argument uses positivity of the real operator,
with real and imaginary parts in the complex `L²` space.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LinearMap

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A positive adjoint weight bounds the reciprocal modulus of every nonzero
complex eigenvector of a positive real `L²` operator. -/
theorem le_norm_of_pos_adjoint_weight
    (A : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ)
    (hA : ∀ v : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    (q : Lp ℝ 2 μ) (hq : ∀ᵐ x ∂μ, 0 < q x)
    {r : ℝ} (hr : 0 < r)
    (hweight : ∀ v : Lp ℝ 2 μ, r * ⟪q, A v⟫_ℝ = ⟪q, v⟫_ℝ)
    (F : Lp ℂ 2 μ) (hF : F ≠ 0) (z : ℂ)
    (hre : Complex.reCLM.compLpL 2 μ F =
      z.re • A (Complex.reCLM.compLpL 2 μ F) -
        z.im • A (Complex.imCLM.compLpL 2 μ F))
    (him : Complex.imCLM.compLpL 2 μ F =
      z.re • A (Complex.imCLM.compLpL 2 μ F) +
        z.im • A (Complex.reCLM.compLpL 2 μ F)) :
    r ≤ ‖z‖ := by
  let u := Complex.reCLM.compLpL 2 μ F
  let v := Complex.imCLM.compLpL 2 μ F
  let w : Lp ℝ 2 μ := lipschitzWith_one_norm.compLp (_root_.norm_zero) F
  have hwval : ∀ᵐ x ∂μ, w x = ‖F x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) F
  have huw : ∀ᵐ x ∂μ, ‖(⟨u x, v x⟩ : ℂ)‖ ≤ w x := by
    filter_upwards [Complex.reCLM.coeFn_compLpL F, Complex.imCLM.coeFn_compLpL F,
      hwval] with x hu hv hw
    change u x = (F x).re at hu
    change v x = (F x).im at hv
    simp only [hu, hv, hw, Complex.eta, le_refl]
  have hw0 : ∀ᵐ x ∂μ, 0 ≤ w x :=
    hwval.mono fun x hx ↦ hx.symm ▸ norm_nonneg (F x)
  have hwne : w ≠ 0 := by
    intro hw
    apply hF
    apply Lp.ext
    have hwzero : ∀ᵐ x ∂μ, w x = 0 := by
      rw [hw]
      exact Lp.coeFn_zero ℝ 2 μ
    filter_upwards [hwval, hwzero, Lp.coeFn_zero ℂ 2 μ] with x hx hx0 hz
    exact (norm_eq_zero.mp (hx.symm.trans hx0)).trans hz.symm
  have hreval : ∀ᵐ x ∂μ, u x = z.re * A u x - z.im * A v x := by
    filter_upwards [Lp.coeFn_sub (z.re • A u) (z.im • A v),
      Lp.coeFn_smul z.re (A u), Lp.coeFn_smul z.im (A v)] with x hs hr hi
    have h := congrArg (fun f : Lp ℝ 2 μ ↦ f x) hre
    change u x = (z.re • A u - z.im • A v) x at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs hr hi
    simpa only [hs, hr, hi] using h
  have himval : ∀ᵐ x ∂μ, v x = z.re * A v x + z.im * A u x := by
    filter_upwards [Lp.coeFn_add (z.re • A v) (z.im • A u),
      Lp.coeFn_smul z.re (A v), Lp.coeFn_smul z.im (A u)] with x hs hr hi
    have h := congrArg (fun f : Lp ℝ 2 μ ↦ f x) him
    change v x = (z.re • A v + z.im • A u) x at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs hr hi
    simpa only [hs, hr, hi] using h
  have hbound : ∀ᵐ x ∂μ, w x ≤ (‖z‖ • A w) x := by
    filter_upwards [A.norm_pair_apply_le_of_nonneg hA u v w huw,
      hreval, himval, hwval, Complex.reCLM.coeFn_compLpL F,
      Complex.imCLM.coeFn_compLpL F, Lp.coeFn_smul ‖z‖ (A w)]
        with x hnorm hu hv hw hur hui hs
    change u x = (F x).re at hur
    change v x = (F x).im at hui
    have heq : F x = z * (⟨A u x, A v x⟩ : ℂ) := by
      apply Complex.ext
      · simpa only [Complex.mul_re, ← hur] using hu
      · simpa only [Complex.mul_im, ← hui] using hv
    rw [hw, heq, norm_mul, hs]
    exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  have hpair := Lp.inner_mono_of_nonneg_ae q w (‖z‖ • A w)
    (hq.mono fun _ hx ↦ hx.le) hbound
  rw [real_inner_smul_right] at hpair
  have hpos := Lp.inner_pos_of_pos_ae_of_nonneg_ae q w hq hw0 hwne
  have heq := hweight w
  have hmul := mul_le_mul_of_nonneg_left hpair hr.le
  nlinarith

end LinearMap
