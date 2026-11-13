/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import PDE.Analysis.Integration.Primitive.Quotient
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Curvature

import CAS.ExactTactic

/-!
# Derivatives of the integral shooting weights

The passage times and speed weights are scalar integral expressions for the
linear fast field with ratio decay rate four. Their first and second level
derivatives identify the relative curvature with `linearFastWeightCurvature`.
In particular the entire contribution multiplied by the weight ratio remains.

`GateRegularity` contains regularity and nonvanishing conditions on the clock.
`SpeedIntegralDifferentiation` states the differentiation-under-the-integral
hypothesis for the speed parameter.

-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace Gate.Weights

/-- Scalar clock data. The upward passage is anchored at `base`; its speed
variation has the independent additive constant `speedConstant`. -/
structure PassageData where
  /-- Scalar clock field; the upward level speed is `g y + 1`. -/
  g : ℝ → ℝ
  /-- Lower feedback cutoff, entering the downward speed as `4 - g y + 4 * C y`. -/
  C : ℝ → ℝ
  /-- Level from which the upward passage integrals are measured. -/
  base : ℝ
  /-- Time at which the upward passage reaches `base`. -/
  upBaseTime : ℝ
  /-- Time at which the downward passage reaches level zero. -/
  terminalTime : ℝ
  /-- Contribution of the moving anchor and terminal clock to the upward
  logarithmic speed weight. -/
  speedConstant : ℝ

namespace PassageData

/-- Downward speed magnitude below the switching region. -/
def downSpeed (D : PassageData) (y : ℝ) : ℝ :=
  4 - D.g y + 4 * D.C y

/-- Remaining downward travel time, including the lower feedback cutoff. -/
def downTime (D : PassageData) (y : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..y, 1 / D.downSpeed v

/-- The downward speed-variation moment. -/
def downMoment (D : PassageData) (y : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..y, v / D.downSpeed v ^ 2

/-- The upward speed-variation moment, anchored inside the gate. -/
def upMoment (D : PassageData) (y : ℝ) : ℝ :=
  ∫ v in D.base..y, v / (D.g v + 1) ^ 2

/-- Upward passage time in the region with feedback equal to one. -/
def tPlus (D : PassageData) (y : ℝ) : ℝ :=
  D.upBaseTime + ∫ v in D.base..y, 1 / (D.g v + 1)

/-- Downward passage time, reconstructed from the remaining travel time. -/
def tMinus (D : PassageData) (y : ℝ) : ℝ :=
  D.terminalTime - D.downTime y

/-- The upward value weight. -/
def wPlus (D : PassageData) (y : ℝ) : ℝ :=
  Real.exp (-4 * (D.terminalTime - D.tPlus y)) / (D.g y + 1)

/-- The downward value weight on the gate, where `C = 0`. -/
def wMinus (D : PassageData) (y : ℝ) : ℝ :=
  Real.exp (-4 * (D.terminalTime - D.tMinus y)) / (4 - D.g y)

/-- The downward logarithmic speed weight from the lower travel integral. -/
def qMinus (D : PassageData) (y : ℝ) : ℝ :=
  4 * D.downMoment y - y / (4 - D.g y)

/-- The upward logarithmic speed weight. The whole moving-clock contribution
at the anchor is retained in `speedConstant`. -/
def qPlus (D : PassageData) (y : ℝ) : ℝ :=
  D.speedConstant + 4 * D.upMoment y + y / (D.g y + 1)

/-- The exponential form of the upward/downward value-weight ratio. -/
def R (D : PassageData) (y : ℝ) : ℝ :=
  (4 - D.g y) / (D.g y + 1) * Real.exp (-4 * (D.tMinus y - D.tPlus y))

/-- The speed weight divided by the downward value weight. -/
def Q (D : PassageData) (y : ℝ) : ℝ :=
  D.qMinus y + D.R y * D.qPlus y

/-- The coefficient in the exact equation `R' = H * R`. -/
def H (D : PassageData) (y : ℝ) : ℝ :=
  5 * (4 - deriv D.g y) / ((D.g y + 1) * (4 - D.g y))

/-- The logarithmic derivative of `H`, wherever `4 - g'` is nonzero. -/
def L (D : PassageData) (y : ℝ) : ℝ :=
  -deriv (deriv D.g) y / (4 - deriv D.g y) -
    deriv D.g y * ((4 - D.g y) - (D.g y + 1)) /
      ((D.g y + 1) * (4 - D.g y))

/-- The explicit first derivative of the downward speed weight. -/
def minusFirst (D : PassageData) (y : ℝ) : ℝ :=
  ((4 - deriv D.g y) * y - (4 - D.g y)) / (4 - D.g y) ^ 2

/-- The explicit second derivative of the downward speed weight. -/
def minusSecond (D : PassageData) (y : ℝ) : ℝ :=
  (4 - y * deriv (deriv D.g) y) / (4 - D.g y) ^ 2 +
    2 * deriv D.g y * ((4 - deriv D.g y) * y - (4 - D.g y)) /
      (4 - D.g y) ^ 3

/-- The explicit first derivative of the upward speed weight. -/
def plusFirst (D : PassageData) (y : ℝ) : ℝ :=
  ((4 - deriv D.g y) * y + (D.g y + 1)) / (D.g y + 1) ^ 2

/-- The explicit second derivative of the upward speed weight. -/
def plusSecond (D : PassageData) (y : ℝ) : ℝ :=
  (4 - y * deriv (deriv D.g) y) / (D.g y + 1) ^ 2 -
    2 * deriv D.g y * ((4 - deriv D.g y) * y + (D.g y + 1)) /
      (D.g y + 1) ^ 3

/-- The first derivative of the normalized speed weight before cancellation. -/
def qFirst (D : PassageData) (y : ℝ) : ℝ :=
  D.minusFirst y + D.H y * D.R y * D.qPlus y + D.R y * D.plusFirst y

/-- The second derivative of the normalized speed weight before cancellation. -/
def qSecond (D : PassageData) (y : ℝ) : ℝ :=
  D.minusSecond y +
    D.R y * (D.H y * (D.H y + D.L y) * D.qPlus y +
      2 * D.H y * D.plusFirst y + D.plusSecond y)

end PassageData

/-- Analytic hypotheses for the integral formulas on an open gate. The
denominators are required to be nonzero only on the integration segments.
No inequality about curvature, determinant, or rank is a field. -/
structure GateRegularity (D : PassageData) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  continuous_g : Continuous D.g
  continuous_C : Continuous D.C
  differentiable_g : ∀ y ∈ I, DifferentiableAt ℝ D.g y
  differentiable_deriv_g : ∀ y ∈ I, DifferentiableAt ℝ (deriv D.g) y
  cutoff_zero : ∀ y ∈ I, D.C y = 0
  up_nonzero : ∀ y ∈ I, ∀ v ∈ uIcc D.base y, D.g v + 1 ≠ 0
  down_nonzero : ∀ y ∈ I, ∀ v ∈ uIcc 0 y, D.downSpeed v ≠ 0

private theorem hasDerivAt_deriv_of_local_formula {f F : ℝ → ℝ} {I : Set ℝ} {y v : ℝ}
    (hI : IsOpen I) (hy : y ∈ I) (hf : ∀ z ∈ I, HasDerivAt f (F z) z) (hF : HasDerivAt F v y) :
    HasDerivAt (deriv f) v y := by
  apply hF.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds hy] with z hz using (hf z hz).deriv

namespace GateRegularity

variable {D : PassageData} {I : Set ℝ} (h : GateRegularity D I)

include h

theorem up_ne {y : ℝ} (hy : y ∈ I) : D.g y + 1 ≠ 0 :=
  h.up_nonzero y hy y right_mem_uIcc

theorem down_ne {y : ℝ} (hy : y ∈ I) : 4 - D.g y ≠ 0 := by
  simpa [PassageData.downSpeed, h.cutoff_zero y hy] using h.down_nonzero y hy y right_mem_uIcc

theorem continuous_downSpeed : Continuous D.downSpeed :=
  (continuous_const.sub h.continuous_g).add (continuous_const.mul h.continuous_C)

theorem hasDerivAt_downTime {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.downTime (1 / (4 - D.g y)) y := by
  apply (PDE.Analysis.hasDerivAt_integral_quotient (f := fun _ : ℝ ↦ 1)
    continuous_const h.continuous_downSpeed (h.down_nonzero y hy)).congr_deriv
  simp only [PassageData.downSpeed, h.cutoff_zero y hy, mul_zero, add_zero]

theorem hasDerivAt_downMoment {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.downMoment (y / (4 - D.g y) ^ 2) y := by
  have hd : HasDerivAt D.downMoment (y / D.downSpeed y ^ 2) y :=
    PDE.Analysis.hasDerivAt_integral_quotient continuous_id (h.continuous_downSpeed.pow 2)
      (fun v hv ↦ pow_ne_zero 2 (h.down_nonzero y hy v hv))
  simpa only [PassageData.downSpeed, h.cutoff_zero y hy, mul_zero, add_zero] using hd

theorem hasDerivAt_upMoment {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.upMoment (y / (D.g y + 1) ^ 2) y :=
  PDE.Analysis.hasDerivAt_integral_quotient continuous_id
    ((h.continuous_g.add continuous_const).pow 2)
    (fun v hv ↦ pow_ne_zero 2 (h.up_nonzero y hy v hv))

theorem hasDerivAt_tPlus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.tPlus (1 / (D.g y + 1)) y :=
  (PDE.Analysis.hasDerivAt_integral_quotient (f := fun _ : ℝ ↦ 1) continuous_const
    (h.continuous_g.add continuous_const) (h.up_nonzero y hy)).const_add D.upBaseTime

theorem hasDerivAt_tMinus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.tMinus (-(1 / (4 - D.g y))) y :=
  (h.hasDerivAt_downTime hy).const_sub D.terminalTime

/-- The derivative uses the lower travel integral, not a constant-clock model. -/
theorem hasDerivAt_qMinus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.qMinus (D.minusFirst y) y := by
  have hg := (h.differentiable_g y hy).hasDerivAt
  have hd := h.down_ne hy
  apply (((h.hasDerivAt_downMoment hy).const_mul 4).sub
    ((hasDerivAt_id y).div (hg.const_sub 4) hd)).congr_deriv
  simp only [id_eq]
  unfold PassageData.minusFirst
  field_simp
  ring

/-- The constant recording the moving upper clock disappears after one level derivative. -/
theorem hasDerivAt_qPlus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.qPlus (D.plusFirst y) y := by
  have hg := (h.differentiable_g y hy).hasDerivAt
  have hu := h.up_ne hy
  apply ((((h.hasDerivAt_upMoment hy).const_mul 4).const_add D.speedConstant).add
    ((hasDerivAt_id y).div (hg.add_const 1) hu)).congr_deriv
  simp only [id_eq]
  unfold PassageData.plusFirst
  field_simp
  ring

/-- Differentiating the explicit downward first derivative requires only `g''`. -/
theorem hasDerivAt_minusFirst {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.minusFirst (D.minusSecond y) y := by
  have hg := (h.differentiable_g y hy).hasDerivAt
  have hv := (h.differentiable_deriv_g y hy).hasDerivAt
  have hd := h.down_ne hy
  have hnum : HasDerivAt (fun z ↦ (4 - deriv D.g z) * z - (4 - D.g z))
      (4 - y * deriv (deriv D.g) y) y := by
    apply (((hv.const_sub 4).mul (hasDerivAt_id y)).sub (hg.const_sub 4)).congr_deriv
    simp only [id_eq]
    ring
  apply (hnum.div ((hg.const_sub 4).pow 2) (pow_ne_zero 2 hd)).congr_deriv
  unfold PassageData.minusSecond
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- Differentiating the explicit upward first derivative requires only `g''`. -/
theorem hasDerivAt_plusFirst {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.plusFirst (D.plusSecond y) y := by
  have hg := (h.differentiable_g y hy).hasDerivAt
  have hv := (h.differentiable_deriv_g y hy).hasDerivAt
  have hu := h.up_ne hy
  have hnum : HasDerivAt (fun z ↦ (4 - deriv D.g z) * z + (D.g z + 1))
      (4 - y * deriv (deriv D.g) y) y := by
    apply (((hv.const_sub 4).mul (hasDerivAt_id y)).add (hg.add_const 1)).congr_deriv
    simp only [id_eq]
    ring
  apply (hnum.div ((hg.add_const 1).pow 2) (pow_ne_zero 2 hu)).congr_deriv
  unfold PassageData.plusSecond
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_deriv_qMinus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt (deriv D.qMinus) (D.minusSecond y) y :=
  hasDerivAt_deriv_of_local_formula h.isOpen hy
    (fun _ hz ↦ h.hasDerivAt_qMinus hz) (h.hasDerivAt_minusFirst hy)

theorem hasDerivAt_deriv_qPlus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt (deriv D.qPlus) (D.plusSecond y) y :=
  hasDerivAt_deriv_of_local_formula h.isOpen hy
    (fun _ hz ↦ h.hasDerivAt_qPlus hz) (h.hasDerivAt_plusFirst hy)

/-- The exponential expression is exactly the ratio of the two passage weights. -/
theorem R_eq_weight_ratio {y : ℝ} (hy : y ∈ I) :
    D.R y = D.wPlus y / D.wMinus y := by
  have hu := h.up_ne hy
  have hd := h.down_ne hy
  have he := Real.exp_ne_zero (-4 * (D.terminalTime - D.tMinus y))
  have hexp : Real.exp (-4 * (D.tMinus y - D.tPlus y)) =
        Real.exp (-4 * (D.terminalTime - D.tPlus y)) /
          Real.exp (-4 * (D.terminalTime - D.tMinus y)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  unfold PassageData.R PassageData.wPlus PassageData.wMinus
  rw [hexp]
  field_simp

theorem wMinus_ne {y : ℝ} (hy : y ∈ I) : D.wMinus y ≠ 0 :=
  div_ne_zero (Real.exp_ne_zero _) (h.down_ne hy)

/-- This is the normalization of the speed functional's two passage weights. -/
theorem Q_eq_normalized_weight {y : ℝ} (hy : y ∈ I) :
    D.Q y = (D.wPlus y * D.qPlus y + D.wMinus y * D.qMinus y) / D.wMinus y := by
  unfold PassageData.Q
  rw [h.R_eq_weight_ratio hy]
  have hm := h.wMinus_ne hy
  field_simp
  ring

theorem R_ne {y : ℝ} (hy : y ∈ I) : D.R y ≠ 0 :=
  mul_ne_zero (div_ne_zero (h.down_ne hy) (h.up_ne hy)) (Real.exp_ne_zero _)

/-- The equation for `R` follows from the two passage integrals. -/
theorem hasDerivAt_R {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.R (D.H y * D.R y) y := by
  have hg := (h.differentiable_g y hy).hasDerivAt
  have hu := h.up_ne hy
  have hd := h.down_ne hy
  have hratio := (hg.const_sub 4).div (hg.add_const 1) hu
  have hexp := (((h.hasDerivAt_tMinus hy).sub (h.hasDerivAt_tPlus hy)).const_mul (-4)).exp
  apply (hratio.mul hexp).congr_deriv
  unfold PassageData.H PassageData.R
  simp only [Pi.div_apply, Pi.sub_apply]
  field_simp
  ring

/-- `H' = H L` is an identity in the first two derivatives of the clock. -/
theorem hasDerivAt_H {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    HasDerivAt D.H (D.H y * D.L y) y := by
  have hg := (h.differentiable_g y hy).hasDerivAt
  have hv := (h.differentiable_deriv_g y hy).hasDerivAt
  have hu := h.up_ne hy
  have hd := h.down_ne hy
  apply (((hv.const_sub 4).const_mul 5).div
    ((hg.add_const 1).mul (hg.const_sub 4)) (mul_ne_zero hu hd)).congr_deriv
  unfold PassageData.H PassageData.L
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem H_ne {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    D.H y ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) hJ) (mul_ne_zero (h.up_ne hy) (h.down_ne hy))

/-- A second level derivative of the integral weight ratio. -/
theorem hasDerivAt_deriv_R {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    HasDerivAt (deriv D.R) (D.H y * (D.H y + D.L y) * D.R y) y := by
  apply hasDerivAt_deriv_of_local_formula h.isOpen hy (fun _ hz ↦ h.hasDerivAt_R hz)
  apply ((h.hasDerivAt_H hy hJ).mul (h.hasDerivAt_R hy)).congr_deriv
  ring

theorem deriv_R_ne {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    deriv D.R y ≠ 0 := by
  rw [(h.hasDerivAt_R hy).deriv]
  exact mul_ne_zero (h.H_ne hy hJ) (h.R_ne hy)

/-- The quotient needed by relative curvature is obtained from the integral ratio. -/
theorem deriv_deriv_R_div_deriv_R {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    deriv (deriv D.R) y / deriv D.R y = D.H y + D.L y := by
  rw [(h.hasDerivAt_deriv_R hy hJ).deriv, (h.hasDerivAt_R hy).deriv]
  have hH := h.H_ne hy hJ
  have hR := h.R_ne hy
  field_simp

theorem hasDerivAt_Q {y : ℝ} (hy : y ∈ I) :
    HasDerivAt D.Q (D.qFirst y) y := by
  apply ((h.hasDerivAt_qMinus hy).add ((h.hasDerivAt_R hy).mul (h.hasDerivAt_qPlus hy))).congr_deriv
  unfold PassageData.qFirst
  ring

theorem hasDerivAt_qFirst {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    HasDerivAt D.qFirst (D.qSecond y) y := by
  have hHR := (h.hasDerivAt_H hy hJ).mul (h.hasDerivAt_R hy)
  apply (((h.hasDerivAt_minusFirst hy).add (hHR.mul (h.hasDerivAt_qPlus hy))).add
    ((h.hasDerivAt_R hy).mul (h.hasDerivAt_plusFirst hy))).congr_deriv
  unfold PassageData.qSecond
  simp only [Pi.mul_apply]
  ring

theorem hasDerivAt_deriv_Q {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    HasDerivAt (deriv D.Q) (D.qSecond y) y :=
  hasDerivAt_deriv_of_local_formula h.isOpen hy
    (fun _ hz ↦ h.hasDerivAt_Q hz) (h.hasDerivAt_qFirst hy hJ)

/-- Identification with the scalar curvature expression. The only extra nonvanishing condition makes
`R'` nonzero. -/
theorem relative_curvature_eq {y : ℝ} (hy : y ∈ I) (hJ : 4 - deriv D.g y ≠ 0) :
    deriv (deriv D.Q) y - deriv (deriv D.R) y / deriv D.R y * deriv D.Q y =
      linearFastWeightCurvature y (D.g y) (deriv D.g y) (deriv (deriv D.g) y) (D.R y) := by
  rw [(h.hasDerivAt_deriv_Q hy hJ).deriv,
    h.deriv_deriv_R_div_deriv_R hy hJ, (h.hasDerivAt_Q hy).deriv]
  have hcancel : D.qSecond y - (D.H y + D.L y) * D.qFirst y =
        D.minusSecond y - (D.H y + D.L y) * D.minusFirst y +
          D.R y * ((D.H y - D.L y) * D.plusFirst y + D.plusSecond y) := by
    unfold PassageData.qSecond PassageData.qFirst
    ring
  exact hcancel

end GateRegularity

namespace PassageData

/-- Exact remaining downward time at speed `μ`; the integration limits stay fixed. -/
def downRemaining (D : PassageData) (μ y : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..y, 1 / (D.downSpeed v + μ * v)

/-- Speed-dependent upward travel from the anchor to the gate level. -/
def upPassageIntegral (D : PassageData) (μ y : ℝ) : ℝ :=
  ∫ v in D.base..y, 1 / (D.g v + 1 - μ * v)

/-- Remaining upward-to-terminal time. `A μ` includes all later switch and
terminal-time motion and is not held constant when `μ` varies. -/
def upRemaining (D : PassageData) (A : ℝ → ℝ) (μ y : ℝ) : ℝ :=
  A μ - D.upPassageIntegral μ y

/-- Downward value weight at speed `μ`, with the physical-time decay rate four. -/
def parameterWeightMinus (D : PassageData) (y μ : ℝ) : ℝ :=
  Real.exp (-4 * D.downRemaining μ y) / (4 - D.g y + μ * y)

/-- Upward value weight at speed `μ`, including the moving remaining time. -/
def parameterWeightPlus (D : PassageData) (A : ℝ → ℝ) (y μ : ℝ) : ℝ :=
  Real.exp (-4 * D.upRemaining A μ y) / (D.g y + 1 - μ * y)

@[simp] theorem downRemaining_zero (D : PassageData) (y : ℝ) :
    D.downRemaining 0 y = D.downTime y := by
  simp [downRemaining, downTime]

theorem upRemaining_zero (D : PassageData) (A : ℝ → ℝ)
    (hA : A 0 = D.terminalTime - D.upBaseTime) (y : ℝ) :
    D.upRemaining A 0 y = D.terminalTime - D.tPlus y := by
  simp only [upRemaining, upPassageIntegral, zero_mul, sub_zero, hA, tPlus]
  ring

theorem wMinus_eq_downTime (D : PassageData) (y : ℝ) :
    D.wMinus y = Real.exp (-4 * D.downTime y) / (4 - D.g y) := by
  simp [wMinus, tMinus]

@[simp] theorem parameterWeightMinus_zero (D : PassageData) (y : ℝ) :
    D.parameterWeightMinus y 0 = D.wMinus y := by
  simp [parameterWeightMinus, wMinus_eq_downTime]

theorem parameterWeightPlus_zero (D : PassageData) (A : ℝ → ℝ)
    (hA : A 0 = D.terminalTime - D.upBaseTime) (y : ℝ) :
    D.parameterWeightPlus A y 0 = D.wPlus y := by
  simp [parameterWeightPlus, upRemaining_zero D A hA y, wPlus]

end PassageData

/-- The two residual parameter-integral derivatives. These are precise analytic
obligations, not axioms or conclusions asserted for a shooting map.
Neither field assumes a derivative of `R`, `Q`, curvature, or rank. -/
structure SpeedIntegralDifferentiation (D : PassageData) (I : Set ℝ) : Prop where
  down : ∀ y ∈ I, HasDerivAt (fun μ ↦ D.downRemaining μ y) (-D.downMoment y) 0
  up : ∀ y ∈ I, HasDerivAt (fun μ ↦ D.upPassageIntegral μ y) (D.upMoment y) 0

private theorem hasDerivAt_exp_time_div {E d : ℝ → ℝ} {E' d' x : ℝ}
    (hE : HasDerivAt E E' x) (hd : HasDerivAt d d' x) (hne : d x ≠ 0) :
    HasDerivAt (fun μ ↦ Real.exp (-4 * E μ) / d μ)
      (Real.exp (-4 * E x) / d x * (-4 * E' - d' / d x)) x := by
  apply (((hE.const_mul (-4)).exp).div hd hne).congr_deriv
  field_simp

namespace SpeedIntegralDifferentiation

variable {D : PassageData} {I : Set ℝ}
    (h : GateRegularity D I) (hs : SpeedIntegralDifferentiation D I)

include h hs

/-- Differentiating the downward value weight gives `wMinus * qMinus`, once
the stated parameter-integral derivative has been established. -/
theorem hasDerivAt_parameterWeightMinus {y : ℝ} (hy : y ∈ I) :
    HasDerivAt (D.parameterWeightMinus y) (D.wMinus y * D.qMinus y) 0 := by
  have hd : HasDerivAt (fun μ : ℝ ↦ 4 - D.g y + μ * y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add (4 - D.g y)
  apply (hasDerivAt_exp_time_div (hs.down y hy) hd
    (by simpa using h.down_ne hy)).congr_deriv
  simp only [zero_mul, add_zero, PassageData.downRemaining_zero]
  rw [D.wMinus_eq_downTime y]
  unfold PassageData.qMinus
  ring

/-- The upward formula retains the anchor derivative, including the switch and
terminal-time motion. Its constant is `speedConstant = -4 * A'(0)`. -/
theorem hasDerivAt_parameterWeightPlus {A : ℝ → ℝ} {y : ℝ} (hy : y ∈ I)
    (hA0 : A 0 = D.terminalTime - D.upBaseTime) (hA : HasDerivAt A (-D.speedConstant / 4) 0) :
    HasDerivAt (D.parameterWeightPlus A y) (D.wPlus y * D.qPlus y) 0 := by
  have hE : HasDerivAt (fun μ ↦ D.upRemaining A μ y) (-D.speedConstant / 4 - D.upMoment y) 0 :=
    hA.sub (hs.up y hy)
  have hu : HasDerivAt (fun μ : ℝ ↦ D.g y + 1 - μ * y) (-y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_sub (D.g y + 1)
  apply (hasDerivAt_exp_time_div hE hu
    (by simpa using h.up_ne hy)).congr_deriv
  simp only [zero_mul, sub_zero, D.upRemaining_zero A hA0 y]
  unfold PassageData.wPlus PassageData.qPlus
  ring

end SpeedIntegralDifferentiation

end Gate.Weights
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
