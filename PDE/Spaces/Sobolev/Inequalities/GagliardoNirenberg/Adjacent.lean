/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.SignedPower

/-!
# Integration by parts for adjacent derivative interpolation

Testing a first derivative against its signed power relates three adjacent
derivative orders. The identity works for every real exponent greater than two,
including the nonintegral exponents needed in higher-order Sobolev composition.
Compact support removes the boundary term; the direction and dimension are arbitrary.
-/

@[expose] public noncomputable section

open MeasureTheory Measure
open scoped ENNReal Topology

namespace SobolevSpace.GagliardoNirenberg

private theorem lpNorm_mul_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} {q r s : ℝ≥0∞} [ENNReal.HolderTriple q r s]
    (hf : MemLp f q ν) (hg : MemLp g r ν) :
    lpNorm (fun x ↦ f x * g x) s ν ≤ lpNorm f q ν * lpNorm g r ν := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := q) (q := r) (r := s)
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm, Pi.smul_apply, smul_eq_mul,
    Pi.mul_def] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h

private theorem lpNorm_abs_rpow {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℝ} {q : ℝ≥0∞} {a : ℝ}
    (hf : AEStronglyMeasurable f ν) (ha : 0 < a) :
    lpNorm (fun x ↦ |f x| ^ a) q ν = lpNorm f (q * ENNReal.ofReal a) ν ^ a := by
  simpa only [Real.norm_eq_abs, ← ENNReal.toReal_rpow, toReal_eLpNorm] using
    congrArg ENNReal.toReal (eLpNorm_norm_rpow f hf ha (p := q))

private theorem holderTriple_half {p : ℝ} (hp : 2 < p) :
    ENNReal.HolderTriple (ENNReal.ofReal (p / 2))
      (ENNReal.ofReal (p / (p - 2))) 1 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hhalf : 0 < p / 2 := by positivity
  have hconj : 0 < p / (p - 2) := div_pos hp0 hp2
  constructor
  rw [← ENNReal.ofReal_inv_of_pos hhalf, ← ENNReal.ofReal_inv_of_pos hconj,
    ← ENNReal.ofReal_add (inv_nonneg.mpr hhalf.le) (inv_nonneg.mpr hconj.le)]
  have heq : (p / 2)⁻¹ + (p / (p - 2))⁻¹ = 1 := by
    field_simp
    ring
  simp only [heq, ENNReal.ofReal_one, inv_one]

private theorem integral_abs_rpow_eq_lpNorm {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f : X → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f ν) :
    (∫ x, |f x| ^ p ∂ν) = lpNorm f (ENNReal.ofReal p) ν ^ p := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity)
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs]
  rw [← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity),
    inv_mul_cancel₀ hp.ne', Real.rpow_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

/-- Testing a derivative against its signed power gives the adjacent-order
interpolation identity. Only two directional derivatives are used. -/
theorem integral_abs_rpow_derivative_eq
    {u v w : E → ℝ} {direction : E} {p : ℝ} (hp : 2 < p)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hdu : ∀ x, HasLineDerivAt ℝ u (v x) x direction)
    (hdv : ∀ x, HasLineDerivAt ℝ v (w x) x direction) :
    (∫ x, |v x| ^ p ∂μ) =
      -(p - 1) * ∫ x, u x * w x * |v x| ^ (p - 2) ∂μ := by
  have hpow : Continuous (fun x ↦ |v x| ^ (p - 2)) :=
    hv.abs.rpow_const (fun _ ↦ Or.inr (by linarith))
  have hG : Continuous (fun x ↦ v x * |v x| ^ (p - 2)) := hv.mul hpow
  have hGderiv (x : E) :
      HasLineDerivAt ℝ (fun x ↦ v x * |v x| ^ (p - 2))
        ((p - 1) * |v x| ^ (p - 2) * w x) x direction := by
    have h := (Real.hasDerivAt_mul_abs_rpow (v (x + (0 : ℝ) • direction))
      (by linarith : 0 < p - 2)).comp 0 (hdv x)
    simpa only [HasLineDerivAt, zero_smul, add_zero, Function.comp_def,
      show p - 2 + 1 = p - 1 by ring] using h
  have hvg : Integrable (fun x ↦ v x * (v x * |v x| ^ (p - 2))) μ :=
    (hv.mul hG).integrable_of_hasCompactSupport hvc.mul_right
  have hug' : Integrable
      (fun x ↦ u x * ((p - 1) * |v x| ^ (p - 2) * w x)) μ :=
    (hu.mul ((continuous_const.mul hpow).mul hw)).integrable_of_hasCompactSupport
      huc.mul_right
  have hug : Integrable (fun x ↦ u x * (v x * |v x| ^ (p - 2))) μ :=
    (hu.mul hG).integrable_of_hasCompactSupport huc.mul_right
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hvg hug' hug
    (fun x _ ↦ hdu x) (fun x _ ↦ hGderiv x)
  have hpower (x : E) : v x * (v x * |v x| ^ (p - 2)) = |v x| ^ p := by
    by_cases hx : v x = 0
    · simp [hx, Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        v x * (v x * |v x| ^ (p - 2)) = |v x| ^ (2 : ℝ) * |v x| ^ (p - 2) := by
          rw [Real.rpow_two, sq_abs]
          ring
        _ = |v x| ^ p := by
          rw [← Real.rpow_add (abs_pos.mpr hx)]
          congr 1
          ring
  have hright :
      (∫ x, u x * ((p - 1) * |v x| ^ (p - 2) * w x) ∂μ) =
        (p - 1) * ∫ x, u x * w x * |v x| ^ (p - 2) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  change (∫ x, u x * ((p - 1) * |v x| ^ (p - 2) * w x) ∂μ) =
    -(∫ x, v x * (v x * |v x| ^ (p - 2)) ∂μ) at hibp
  simp only [hpower, hright] at hibp
  linarith

/-- The unsigned form of the adjacent-order identity, before Hölder's inequality. -/
theorem integral_abs_rpow_derivative_le
    {u v w : E → ℝ} {direction : E} {p : ℝ} (hp : 2 < p)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hdu : ∀ x, HasLineDerivAt ℝ u (v x) x direction)
    (hdv : ∀ x, HasLineDerivAt ℝ v (w x) x direction) :
    (∫ x, |v x| ^ p ∂μ) ≤
      (p - 1) * ∫ x, |u x| * |w x| * |v x| ^ (p - 2) ∂μ := by
  rw [integral_abs_rpow_derivative_eq hp hu hv hw huc hvc hdu hdv, neg_mul]
  calc
    -((p - 1) * ∫ x, u x * w x * |v x| ^ (p - 2) ∂μ) ≤
        |(p - 1) * ∫ x, u x * w x * |v x| ^ (p - 2) ∂μ| := neg_le_abs _
    _ ≤ (p - 1) * ∫ x, |u x| * |w x| * |v x| ^ (p - 2) ∂μ := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < p - 1)]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg
        (abs_nonneg _) _)] using norm_integral_le_integral_norm
          (fun x ↦ u x * w x * |v x| ^ (p - 2))

/-- Adjacent directional derivatives satisfy the dimension-independent
Gagliardo–Nirenberg estimate. The Hölder triple states `1/q + 1/r = 2/p`;
in particular the lower-order exponent `q` may be infinity. -/
theorem lpNorm_derivative_sq_le
    {u v w : E → ℝ} {direction : E} {p : ℝ} {q r : ℝ≥0∞}
    [ENNReal.HolderTriple q r (ENNReal.ofReal (p / 2))]
    (hp : 2 < p) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v) (hwc : HasCompactSupport w)
    (hdu : ∀ x, HasLineDerivAt ℝ u (v x) x direction)
    (hdv : ∀ x, HasLineDerivAt ℝ v (w x) x direction) :
    lpNorm v (ENNReal.ofReal p) μ ^ 2 ≤
      (p - 1) * lpNorm u q μ * lpNorm w r μ := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hconj : 0 < p / (p - 2) := div_pos hp0 hp2
  let s := ENNReal.ofReal (p / 2)
  let t := ENNReal.ofReal (p / (p - 2))
  have : ENNReal.HolderTriple s t 1 := holderTriple_half hp
  have huLp : MemLp u q μ := hu.memLp_of_hasCompactSupport huc
  have hwLp : MemLp w r μ := hw.memLp_of_hasCompactSupport hwc
  have huw : MemLp (fun x ↦ u x * w x) s μ := huLp.mul (r := s) hwLp
  have hvpowc : HasCompactSupport (fun x ↦ |v x| ^ (p - 2)) :=
    hvc.comp_left (g := fun y : ℝ ↦ |y| ^ (p - 2))
      (by simp only [abs_zero, Real.zero_rpow hp2.ne'])
  have hvpow : MemLp (fun x ↦ |v x| ^ (p - 2)) t μ :=
    (hv.abs.rpow_const (fun _ ↦ Or.inr hp2.le)).memLp_of_hasCompactSupport hvpowc
  have ht : t * ENNReal.ofReal (p - 2) = ENNReal.ofReal p := by
    dsimp only [t]
    rw [← ENNReal.ofReal_mul hconj.le, div_mul_cancel₀ _ hp2.ne']
  have hHolder := lpNorm_mul_le (q := s) (r := t) (s := 1) huw hvpow
  have hmeas : AEStronglyMeasurable (fun x ↦ u x * w x * |v x| ^ (p - 2)) μ := by
    simpa only [Pi.mul_def] using huw.aestronglyMeasurable.mul hvpow.aestronglyMeasurable
  rw [lpNorm_one_eq_integral_norm hmeas,
    lpNorm_abs_rpow hv.aestronglyMeasurable hp2, ht] at hHolder
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg
    (abs_nonneg _) _)] at hHolder
  have hproduct := lpNorm_mul_le (q := q) (r := r) (s := s) huLp hwLp
  have hintegral := integral_abs_rpow_eq_lpNorm hp0 (hv.aestronglyMeasurable (μ := μ))
  have hestimate : lpNorm v (ENNReal.ofReal p) μ ^ p ≤
      ((p - 1) * lpNorm u q μ * lpNorm w r μ) *
        lpNorm v (ENNReal.ofReal p) μ ^ (p - 2) := by
    rw [← hintegral]
    calc
      _ ≤ (p - 1) * ∫ x, |u x| * |w x| * |v x| ^ (p - 2) ∂μ :=
        integral_abs_rpow_derivative_le hp hu hv hw huc hvc hdu hdv
      _ ≤ (p - 1) *
          (lpNorm (fun x ↦ u x * w x) s μ * lpNorm v (ENNReal.ofReal p) μ ^ (p - 2)) :=
        mul_le_mul_of_nonneg_left hHolder (by linarith)
      _ ≤ (p - 1) *
          ((lpNorm u q μ * lpNorm w r μ) * lpNorm v (ENNReal.ofReal p) μ ^ (p - 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hproduct (Real.rpow_nonneg lpNorm_nonneg _))
          (by linarith)
      _ = _ := by ring
  by_cases hvzero : lpNorm v (ENNReal.ofReal p) μ = 0
  · rw [hvzero, zero_pow (by decide)]
    exact mul_nonneg (mul_nonneg (by linarith) lpNorm_nonneg) lpNorm_nonneg
  · have hvpos : 0 < lpNorm v (ENNReal.ofReal p) μ :=
      lt_of_le_of_ne lpNorm_nonneg (Ne.symm hvzero)
    have hsplit : lpNorm v (ENNReal.ofReal p) μ ^ p =
        lpNorm v (ENNReal.ofReal p) μ ^ 2 * lpNorm v (ENNReal.ofReal p) μ ^ (p - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_add hvpos]
      congr 1
      ring
    rw [hsplit] at hestimate
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hvpos (p - 2))).mp hestimate

end SobolevSpace.GagliardoNirenberg
