/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import PDE.Analysis.MeasureTheory.Lp.RadialPower
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Integrability of compactly cut off radial powers and their derivatives

On a finite-dimensional real normed space of dimension `d`, the power `‖x‖ ^ a` is
locally in `Lᵖ` when `-a p < d`. Multiplying by a continuous compactly supported
cutoff `φ` gives a global `Lᵖ` function, and `max (‖x‖ ^ a - 1) 0` is in `Lᵖ` for
`a ≤ 0`. Away from the origin `‖D (‖x‖ ^ a)‖ ≤ |a| ‖x‖ ^ (a - 1)`, so for a smooth
compactly supported `φ` the derivative of `φ x * ‖x‖ ^ a` is in `Lᵖ` when also
`-(a - 1) p < d`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Multiplication by a continuous compactly supported function preserves the
local radial-power integrability criterion. -/
theorem Continuous.memLp_mul_norm_rpow_of_hasCompactSupport
    {φ : E → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hd : 1 ≤ Module.finrank ℝ E) {p : ℝ≥0∞}
    (hp : p ≠ 0) (hp' : p ≠ ∞) {a : ℝ}
    (ha : -a * p.toReal < (Module.finrank ℝ E : ℝ)) :
    MemLp (fun x ↦ φ x * ‖x‖ ^ a) p μ := by
  have hr : MemLp ((tsupport φ).indicator (fun x : E ↦ ‖x‖ ^ a)) p μ := by
    rw [memLp_indicator_iff_restrict hφc.measurableSet.nullMeasurableSet]
    simpa only [sub_zero] using
      memLp_norm_sub_rpow_of_isBounded (μ := μ) hd hp hp' ha 0 hφc.isBounded
  have hprod := (hφ.memLp_top_of_hasCompactSupport hφc μ).mul (r := p) hr
  refine hprod.ae_eq (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ tsupport φ
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport hx]

/-- The positive part of a negative radial power minus one has the same local
`Lᵖ` criterion as the untruncated power, and vanishes outside the unit ball. -/
theorem MeasureTheory.memLp_posPart_norm_rpow_sub_one
    (hd : 1 ≤ Module.finrank ℝ E) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞)
    {a : ℝ} (ha : a ≤ 0) (hpa : -a * p.toReal < (Module.finrank ℝ E : ℝ)) :
    MemLp (fun x : E ↦ max (‖x‖ ^ a - 1) 0) p μ := by
  have hr : MemLp ((Metric.ball (0 : E) 1).indicator (fun x ↦ ‖x‖ ^ a)) p μ := by
    rw [memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet]
    simpa only [sub_zero] using
      memLp_norm_sub_rpow_of_isBounded (μ := μ) hd hp hp' hpa 0 Metric.isBounded_ball
  have hF : LipschitzWith 1 (fun z : ℝ ↦ max (z - 1) 0) := by
    simpa only [one_mul, Function.comp_def, sub_eq_add_neg] using
      Lp.lipschitzWith_pos_part.comp (isometry_add_right (-1 : ℝ)).lipschitzWith
  refine (hF.comp_memLp (by norm_num) hr).ae_eq (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ Metric.ball (0 : E) 1
  · simp [hx]
  · have hx' : 1 ≤ ‖x‖ := by simpa using hx
    have hr' := Real.rpow_le_one_of_one_le_of_nonpos hx' ha
    simp [hx, max_eq_right (sub_nonpos.mpr hr')]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace PDE

/-- Away from the origin, the derivative of a radial power has the expected
operator-norm upper bound. -/
theorem norm_fderiv_norm_rpow_le_of_ne_zero (a : ℝ) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ a) x‖ ≤ |a| * ‖x‖ ^ (a - 1) := by
  have hnorm : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    (contDiffAt_norm ℝ hx).differentiableAt one_ne_zero
  rw [(hnorm.hasFDerivAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hx))).fderiv]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hn : ‖fderiv ℝ (fun y : E ↦ ‖y‖) x‖ ≤ 1 :=
    by simpa only [NNReal.coe_one] using
      (norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (f := fun y : E ↦ ‖y‖)
        lipschitzWith_one_norm)
  exact mul_le_of_le_one_right (by positivity) hn

end PDE

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The derivative of a compactly cut off radial power is in `Lᵖ` whenever
both the power and its first derivative satisfy the dimensional criterion. -/
theorem ContDiff.memLp_fderiv_mul_norm_rpow_of_hasCompactSupport
    [Nontrivial E] {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hd : 1 ≤ Module.finrank ℝ E)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞) {a : ℝ}
    (ha : -a * p.toReal < (Module.finrank ℝ E : ℝ))
    (ha' : -(a - 1) * p.toReal < (Module.finrank ℝ E : ℝ)) :
    MemLp (fderiv ℝ (fun x ↦ φ x * ‖x‖ ^ a)) p μ := by
  have h₁ := hφ.continuous.norm.memLp_mul_norm_rpow_of_hasCompactSupport
    (μ := μ) hφc.norm hd hp hp' ha'
  have h₂ := Continuous.memLp_mul_norm_rpow_of_hasCompactSupport
    (μ := μ) (hφ.continuous_fderiv (by norm_num)).norm (hφc.fderiv (𝕜 := ℝ)).norm hd hp hp' ha
  have hb := (h₁.const_mul |a|).add h₂
  refine hb.mono' (measurable_fderiv ℝ _).aestronglyMeasurable ?_
  filter_upwards [μ.ae_ne (0 : E)] with x hx
  have hnc : ContDiffAt ℝ 1 (fun y : E ↦ ‖y‖ ^ a) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  have hnorm := hnc.differentiableAt one_ne_zero
  rw [fderiv_fun_mul (hφ.differentiable one_ne_zero x) hnorm]
  calc
    ‖φ x • fderiv ℝ (fun y : E ↦ ‖y‖ ^ a) x +
        ‖x‖ ^ a • fderiv ℝ φ x‖
        ≤ ‖φ x‖ * ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ a) x‖ +
          ‖x‖ ^ a * ‖fderiv ℝ φ x‖ := by
          simpa only [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
            norm_add_le (φ x • fderiv ℝ (fun y : E ↦ ‖y‖ ^ a) x)
              (‖x‖ ^ a • fderiv ℝ φ x)
    _ ≤ ‖φ x‖ * (|a| * ‖x‖ ^ (a - 1)) + ‖x‖ ^ a * ‖fderiv ℝ φ x‖ := by
      gcongr
      exact PDE.norm_fderiv_norm_rpow_le_of_ne_zero a hx
    _ = |a| * (‖φ x‖ * ‖x‖ ^ (a - 1)) + ‖fderiv ℝ φ x‖ * ‖x‖ ^ a := by
      ring


end InnerProduct
