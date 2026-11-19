/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

/-!
# Spherical averages of convolutions

A locally integrable measurable kernel convolved with continuous compactly
supported data commutes with spherical averaging. Product integrability follows
from continuity of the convolution of the absolute values on the compact sphere;
Fubini then gives the identity for every center and every signed radius.
-/

@[expose] public section

open MeasureTheory Set PDE.Analysis

namespace PDE.Analysis

/-- A spherical average commutes with convolution against continuous compactly supported data. -/
theorem unitSphereAverage_integral_convolution {n : ℕ} {k f : ℝ^n → ℝ}
    (hk : LocallyIntegrable k volume) (hkm : Measurable k)
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : ℝ^n) (t : ℝ) :
    unitSphereAverage n (fun z ↦ ∫ y, k (z - y) * f y) x t =
      ∫ y, unitSphereAverage n k (x - y) t * f y := by
  let σ := (volume : Measure (ℝ^n)).toSphere
  let p : Metric.sphere (0 : ℝ^n) 1 → ℝ^n := fun ω ↦ x + t • (ω : ℝ^n)
  have hp : Continuous p := by fun_prop
  have hm : Measurable (fun z : Metric.sphere (0 : ℝ^n) 1 × ℝ^n ↦
      k (p z.1 - z.2) * f z.2) := by dsimp [p]; fun_prop
  have hint (ω : Metric.sphere (0 : ℝ^n) 1) :
      Integrable (fun y ↦ k (p ω - y) * f y) := by
    have h := ((hfc.convolutionExists_right (L := ContinuousLinearMap.mul ℝ ℝ)
      hk hf) (p ω)).integrable.comp_sub_left (p ω)
    simpa only [ContinuousLinearMap.mul_apply', sub_sub_cancel] using h
  have hn (ω : Metric.sphere (0 : ℝ^n) 1) :
      (∫ y, ‖k (p ω - y) * f y‖) =
        convolution (fun z ↦ ‖k z‖) (fun z ↦ ‖f z‖)
          (ContinuousLinearMap.mul ℝ ℝ) volume (p ω) := by
    have h := integral_sub_left_eq_self
      (fun y ↦ ‖k y‖ * ‖f (p ω - y)‖) volume (p ω)
    simpa only [norm_mul, sub_sub_cancel, convolution_mul] using h
  have hc : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
      ∫ y, ‖k (p ω - y) * f y‖) := by
    simp_rw [hn]
    exact (hfc.norm.continuous_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrableOn_univ.mp (hk.locallyIntegrableOn univ).norm) hf.norm).comp hp
  have hprod : Integrable
      (fun z : Metric.sphere (0 : ℝ^n) 1 × ℝ^n ↦ k (p z.1 - z.2) * f z.2)
      (σ.prod volume) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hint, ?_⟩
    exact hc.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ mem_univ _))
  unfold unitSphereAverage
  change (∫ ω, ∫ y, k (p ω - y) * f y ∂volume ∂σ) / unitSphereArea n = _
  rw [integral_integral_swap hprod]
  simp_rw [integral_mul_const]
  rw [← integral_div]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  have hpoint (ω : Metric.sphere (0 : ℝ^n) 1) : p ω - y = x - y + t • (ω : ℝ^n) := by
    dsimp [p]
    abel
  simp_rw [hpoint]
  ring

end PDE.Analysis
