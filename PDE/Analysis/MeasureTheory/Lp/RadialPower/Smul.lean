/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.RadialPower

/-!
# Multiplication by negative radial powers

A function in both Lᵖ and L∞ remains in Lᵖ after multiplication by a negative
radial power with an integrable local singularity. Inside a unit ball, Hölder
uses the radial power's local Lᵖ membership. Outside the ball, the weight is
at most one. The measure may be any additive Haar measure.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A bounded Lᵖ function remains in Lᵖ after multiplication by a negative radial
power whose local singularity satisfies the dimensional integrability criterion. -/
theorem MemLp.norm_sub_rpow_smul {f : E → F} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hfb : MemLp f ∞ μ)
    (hd : 1 ≤ Module.finrank ℝ E) (hp : p ≠ 0) (hp' : p ≠ ∞)
    {a : ℝ} (ha : a ≤ 0) (hap : -a * p.toReal < (Module.finrank ℝ E : ℝ)) (z : E) :
    MemLp (fun x ↦ ‖x - z‖ ^ a • f x) p μ := by
  classical
  have hm : AEStronglyMeasurable (fun x ↦ ‖x - z‖ ^ a • f x) μ :=
    ((measurable_id.sub_const z).norm.pow_const a).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  have hnear : MemLp (fun x ↦ ‖x - z‖ ^ a • f x) p (μ.restrict (ball z 1)) :=
    (memLp_norm_sub_rpow_of_isBounded hd hp hp' hap z isBounded_ball).smul
      (hfb.restrict (ball z 1))
  have hfar : MemLp (fun x ↦ ‖x - z‖ ^ a • f x) p (μ.restrict (ball z 1)ᶜ) := by
    apply (hf.restrict (ball z 1)ᶜ).mono hm.restrict
    filter_upwards [self_mem_ae_restrict measurableSet_ball.compl] with x hx
    have hxnorm : 1 ≤ ‖x - z‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hx
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hxnorm ha)
  simpa only [piecewise_same] using hnear.piecewise measurableSet_ball.nullMeasurableSet hfar

end MeasureTheory
