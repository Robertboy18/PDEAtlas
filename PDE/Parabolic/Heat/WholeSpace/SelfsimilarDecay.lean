/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Selfsimilar
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Decay of free self-similar heat evolution

The heat symbol absorbs the growth of the dilated Bessel weight uniformly
in similarity time. The remaining factor is the exact L² Jacobian, giving
decay at rate one quarter in dimension three. The constants in the Sobolev
order are explicit and are not claimed to be optimal.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Fractional BesselPotentialSpace PDE.Analysis.Fourier
open scoped ENNReal NNReal Sobolev BesselPotentialSpace

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- A uniform bound for the heat symbol times the dilated integer Bessel weight. -/
def selfsimilarBesselConstant (k : ℕ) : ℝ := (k.factorial : ℝ) * Real.exp 1

theorem selfsimilarBesselConstant_pos (k : ℕ) : 0 < selfsimilarBesselConstant k := by
  unfold selfsimilarBesselConstant
  positivity

/-- The exponential series controls every nonnegative integer weight. -/
theorem polynomial_mul_heatGaussian_le (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (1 + q) ^ k * Real.exp (-(4 * Real.pi ^ 2 * q)) ≤ selfsimilarBesselConstant k := by
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hpow : (1 + q) ^ k ≤ Real.exp (1 + q) * (k.factorial : ℝ) :=
    (div_le_iff₀ hf).1 (Real.pow_div_factorial_le_exp (1 + q) (by positivity) k)
  have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ (Real.exp (1 + q) * (k.factorial : ℝ)) *
        Real.exp (-(4 * Real.pi ^ 2 * q)) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * Real.exp (1 + (1 - 4 * Real.pi ^ 2) * q) := by
      rw [mul_right_comm, ← Real.exp_add, mul_comm]
      congr 2
      ring
    _ ≤ selfsimilarBesselConstant k := by
      apply mul_le_mul_of_nonneg_left _ hf.le
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Heat absorption removes all time growth from the dilated Bessel weight. -/
theorem norm_besselSymbol_dilation_mul_heatSymbol_le (k : ℕ) (τ : ℝ≥0) (ξ : ℝ^n) :
    ‖besselSymbol n (k : ℝ) (selfsimilarFactor τ • ξ)‖ *
        ‖heatSymbol n (selfsimilarHeatTime τ) ξ‖ ≤
      selfsimilarBesselConstant k * ‖besselSymbol n (k : ℝ) ξ‖ := by
  let t : ℝ := selfsimilarHeatTime τ
  let q : ℝ := t * ‖ξ‖ ^ 2
  have ht : 0 ≤ t := (selfsimilarHeatTime τ).property
  have hq : 0 ≤ q := mul_nonneg ht (sq_nonneg _)
  have ha : selfsimilarFactor τ ^ 2 = 1 + t := by
    rw [selfsimilarFactor_sq]
    dsimp [t]
    ring
  have hweight : (1 + ‖selfsimilarFactor τ • ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤
      (1 + q) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
    calc
      _ ≤ ((1 + q) * (1 + ‖ξ‖ ^ 2)) ^ ((k : ℝ) / 2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha]
        dsimp [q]
        nlinarith [mul_nonneg ht (sq_nonneg (‖ξ‖ ^ 2))]
      _ = (1 + q) ^ ((k : ℝ) / 2) *
          (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (1 + q) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hgaussian := polynomial_mul_heatGaussian_le k hq
  simp only [besselSymbol, heatSymbol, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((1 + q) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)) *
        Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
    _ = ((1 + q) ^ k * Real.exp (-(4 * Real.pi ^ 2 * q))) *
        (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
      dsimp [q]
      rw [mul_assoc (4 * Real.pi ^ 2) t]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hgaussian (Real.rpow_nonneg (by positivity) _)

private theorem norm_ofWkpSpace_selfsimilarHeatSobolev_le_factor
    (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    ‖ofWkpSpace (selfsimilarHeatSobolev n k τ u)‖ ≤
      selfsimilarBesselConstant k *
        (selfsimilarFactor τ * |(selfsimilarFactor τ ^ n)⁻¹|) *
        |((selfsimilarFactor τ)⁻¹ ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal *
        ‖ofWkpSpace u‖ := by
  let a := selfsimilarFactor τ
  let t := selfsimilarHeatTime τ
  let J := |(a ^ n)⁻¹|
  let v := (𝓕 (toLp (ofWkpSpace u)) : Lp ℂ 2 (volume : Measure (ℝ^n)))
  let d := Lp.compSMul volume 2 a⁻¹ (inv_ne_zero (selfsimilarFactor_pos τ).ne') v
  let f := (𝓕 (baseL2 u) : Lp ℂ 2 (volume : Measure (ℝ^n)))
  let g := (heatSymbolLinf n t • f : Lp ℂ 2 (volume : Measure (ℝ^n)))
  have ha : 0 < a := selfsimilarFactor_pos τ
  have hJ : 0 ≤ J := abs_nonneg _
  have hsmul (w : Lp ℂ 2 (volume : Measure (ℝ^n))) :
      𝓕 (a • w) = a • 𝓕 w :=
    (fourierCLM ℂ (Lp ℂ 2 (volume : Measure (ℝ^n)))).map_smul_of_tower _ _
  have hbase :
      𝓕 (baseL2 (selfsimilarHeatSobolev n k τ u)) =
        (a * J) • Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') g := by
    rw [baseL2_selfsimilarHeatSobolev, hsmul, fourier_compSMul, fourier_heatL2,
      finrank_euclideanSpace_fin, smul_smul]
  have hcomp := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^n))
    (inv_ne_zero ha.ne')
  have hinput := hcomp.ae_eq_comp (coeFn_fourier_toLp_ofWkpSpace u)
  have hheat := hcomp.ae_eq_comp (Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) f)
  have hsymbol := hcomp.ae_eq_comp (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  have hmajor :
      ‖𝓕 (toLp (ofWkpSpace (selfsimilarHeatSobolev n k τ u)))‖ ≤
        (selfsimilarBesselConstant k * (a * J)) * ‖d‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have houtput := coeFn_fourier_toLp_ofWkpSpace (selfsimilarHeatSobolev n k τ u)
    rw [hbase] at houtput
    filter_upwards [houtput,
      Lp.coeFn_smul (a * J) (Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') g),
      Lp.coeFn_compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') g,
      Lp.coeFn_compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') v,
      hinput, hheat, hsymbol] with ξ hout hscale hg hd hin hmul hsym
    simp only [Function.comp_apply, smul_eq_mul, Pi.mul_apply] at hin hmul hsym
    rw [hout, hscale]
    simp only [Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos ha, abs_of_nonneg hJ, hg]
    change ‖besselSymbol n (k : ℝ) ξ‖ * (a * J * ‖g (a⁻¹ • ξ)‖) ≤
      selfsimilarBesselConstant k * (a * J) * ‖d ξ‖
    change g (a⁻¹ • ξ) = _ at hmul
    change d ξ = _ at hd
    change v (a⁻¹ • ξ) =
      besselSymbol n (k : ℝ) (a⁻¹ • ξ) * f (a⁻¹ • ξ) at hin
    change heatSymbolLinf n t (a⁻¹ • ξ) = _ at hsym
    rw [hmul, hsym, hd, hin, norm_mul, norm_mul]
    have hweight := norm_besselSymbol_dilation_mul_heatSymbol_le (n := n) k τ (a⁻¹ • ξ)
    rw [smul_inv_smul₀ ha.ne'] at hweight
    calc
      _ = (a * J * ‖f (a⁻¹ • ξ)‖) *
          (‖besselSymbol n (k : ℝ) ξ‖ * ‖heatSymbol n t (a⁻¹ • ξ)‖) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hweight (by positivity)).trans_eq (by ring)
  have hd : ‖d‖ = |((a⁻¹) ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal * ‖ofWkpSpace u‖ := by
    dsimp only [d, v]
    rw [Lp.norm_compSMul, finrank_euclideanSpace_fin, norm_fourier_toLp_eq]
  rw [norm_fourier_toLp_eq, hd] at hmajor
  simpa only [mul_assoc] using hmajor

/-- The two Fourier Jacobians give the exact dimension-dependent decay factor. -/
theorem selfsimilar_jacobian_factor (n : ℕ) (τ : ℝ≥0) :
    (selfsimilarFactor τ * |(selfsimilarFactor τ ^ n)⁻¹|) *
        |((selfsimilarFactor τ)⁻¹ ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal =
      Real.exp (((2 : ℝ) - n) * τ / 4) := by
  have hexp (x : ℝ) : |Real.exp x| = Real.exp x := abs_of_pos (Real.exp_pos _)
  simp only [selfsimilarFactor, ← Real.exp_nat_mul, ← Real.exp_neg, hexp]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  norm_num
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The physical L² change of variables has the same exact decay factor. -/
theorem selfsimilar_volume_factor (n : ℕ) (τ : ℝ≥0) :
    selfsimilarFactor τ * |(selfsimilarFactor τ ^ n)⁻¹| ^
        (1 / (2 : ℝ≥0∞)).toReal =
      Real.exp (((2 : ℝ) - n) * τ / 4) := by
  have hexp (x : ℝ) : |Real.exp x| = Real.exp x := abs_of_pos (Real.exp_pos _)
  simp only [selfsimilarFactor, ← Real.exp_nat_mul, ← Real.exp_neg, hexp]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  norm_num
  rw [← Real.exp_add]
  congr 1
  ring

/-- Integer powers of the similarity factor have their literal exponential value. -/
theorem selfsimilarFactor_pow (m : ℕ) (τ : ℝ≥0) :
    selfsimilarFactor τ ^ m = Real.exp ((m : ℝ) * τ / 2) := by
  rw [selfsimilarFactor, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Free self-similar evolution has a uniform Bessel bound with exact time decay. -/
theorem norm_ofWkpSpace_selfsimilarHeatSobolev_le
    (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    ‖ofWkpSpace (selfsimilarHeatSobolev n k τ u)‖ ≤
      selfsimilarBesselConstant k * Real.exp (((2 : ℝ) - n) * τ / 4) *
        ‖ofWkpSpace u‖ := by
  have h := norm_ofWkpSpace_selfsimilarHeatSobolev_le_factor τ u
  rw [mul_assoc (selfsimilarBesselConstant k), selfsimilar_jacobian_factor] at h
  exact h

/-- The norm-comparison constant for free self-similar evolution on Sobolev graphs. -/
def selfsimilarGraphConstant (n k : ℕ) : ℝ :=
  toWkpSpaceNormBound n k * selfsimilarBesselConstant k *
    ((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1))

theorem selfsimilarGraphConstant_nonneg (n k : ℕ) : 0 ≤ selfsimilarGraphConstant n k := by
  exact mul_nonneg
    (mul_nonneg toWkpSpaceNormBound_nonneg (selfsimilarBesselConstant_pos k).le)
    (by positivity)

/-- The actual graph-space semigroup retains the dimension-dependent free decay. -/
theorem norm_selfsimilarHeatSobolev_le (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    ‖selfsimilarHeatSobolev n k τ u‖ ≤
      selfsimilarGraphConstant n k * Real.exp (((2 : ℝ) - n) * τ / 4) * ‖u‖ := by
  have hforward := norm_toWkpSpace_le
    (ofWkpSpace (selfsimilarHeatSobolev n k τ u))
    (isRealL2_toL2Fun_ofWkpSpace (selfsimilarHeatSobolev n k τ u))
  rw [toWkpSpace_ofWkpSpace] at hforward
  calc
    _ ≤ toWkpSpaceNormBound n k * ‖ofWkpSpace (selfsimilarHeatSobolev n k τ u)‖ :=
      hforward
    _ ≤ toWkpSpaceNormBound n k *
        (selfsimilarBesselConstant k * Real.exp (((2 : ℝ) - n) * τ / 4) *
          ‖ofWkpSpace u‖) :=
      mul_le_mul_of_nonneg_left (norm_ofWkpSpace_selfsimilarHeatSobolev_le τ u)
        toWkpSpaceNormBound_nonneg
    _ ≤ toWkpSpaceNormBound n k *
        (selfsimilarBesselConstant k * Real.exp (((2 : ℝ) - n) * τ / 4) *
          (((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1)) * ‖u‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_ofWkpSpace_le u)
          (mul_nonneg (selfsimilarBesselConstant_pos k).le (Real.exp_pos _).le))
        toWkpSpaceNormBound_nonneg
    _ = _ := by unfold selfsimilarGraphConstant; ring

end HeatEquation.WholeSpace
