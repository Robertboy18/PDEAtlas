/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.WeakQuadraticFTC
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The product estimate for a weak derivative on the line

Square integrability supplies arbitrarily small values on both half-lines.
Combining the two quadratic fundamental theorems costs only one integral of
`|f g|`. Cauchy–Schwarz gives `|f(x)|² ≤ ‖f‖₂ ‖g‖₂`, without a decay hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Integrable

/-- An integrable real function cannot stay above a positive constant on a
set of infinite measure. -/
theorem exists_mem_lt_of_measure_eq_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {s : Set α}
    (hf : Integrable f μ) (hsm : MeasurableSet s) (hs : μ s = ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ s, f x < ε := by
  by_contra! h
  have hc : IntegrableOn (fun _ : α ↦ ε) s μ := by
    apply hf.restrict.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem hsm] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos hε] using h x hx
  have hc' := (integrableOn_const_iff).mp hc
  simp [hs, hε.ne'] at hc'

end MeasureTheory.Integrable

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- The two half-lines give the bound `|f x|² ≤ ∫ |f g|` for the square. -/
theorem sq_apply_le_integral_abs_mul {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    (hbase : MemLp f 2 volume) (hderiv : MemLp g 2 volume) (x : ℝ) :
    f x ^ 2 ≤ ∫ t, |f t * g t| := by
  have hfg : Integrable (fun t ↦ f t * g t) volume := hbase.integrable_mul hderiv
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, hfa⟩ := hbase.integrable_sq.exists_mem_lt_of_measure_eq_top
    measurableSet_Iio (s := Iio x) Real.volume_Iio hε
  obtain ⟨b, hb, hfb⟩ := hbase.integrable_sq.exists_mem_lt_of_measure_eq_top
    measurableSet_Ioi (s := Ioi x) Real.volume_Ioi hε
  have hleft := hweak.integral_mul_eq_half_sq_sub hf a x
  have hright := hweak.integral_mul_eq_half_sq_sub hf x b
  have hleftAbs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := fun t ↦ f t * g t) ha.le
  have hrightAbs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := fun t ↦ f t * g t) hb.le
  have hsum : (∫ t in a..x, |f t * g t|) + (∫ t in x..b, |f t * g t|) ≤
      ∫ t, |f t * g t| := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      hfg.abs.intervalIntegrable hfg.abs.intervalIntegrable,
      intervalIntegral.integral_of_le (ha.le.trans hb.le)]
    exact setIntegral_le_integral hfg.abs (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
  have hl := (le_abs_self _).trans hleftAbs
  have hr := (neg_le_abs _).trans hrightAbs
  rw [hleft] at hl
  rw [hright] at hr
  nlinarith

/-- One-dimensional Sobolev control `|f x|² ≤ ‖f‖₂ ‖g‖₂` from a weak derivative. -/
theorem sq_apply_le_l2_mul_l2 {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    (hbase : MemLp f 2 volume) (hderiv : MemLp g 2 volume) (x : ℝ) :
    f x ^ 2 ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  refine (hweak.sq_apply_le_integral_abs_mul hf hbase hderiv x).trans ?_
  have h := abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hbase.norm hderiv.norm
  rw [abs_of_nonneg (integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    at h
  rw [lpNorm_norm hbase.aestronglyMeasurable, lpNorm_norm hderiv.aestronglyMeasurable] at h
  simpa only [Real.norm_eq_abs, abs_mul, toReal_eLpNorm] using h

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
