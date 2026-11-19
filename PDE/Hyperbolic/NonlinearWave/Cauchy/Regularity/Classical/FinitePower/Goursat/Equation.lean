/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Analysis.Integration.Primitive.Parametric
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Polynomial
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula

/-!
# Differentiation of the characteristic integral equation

Rectangle normalization and one-variable integral differentiation give the mixed characteristic
equation and its exact characteristic traces.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The two normalized integrals are the oriented integral over the characteristic rectangle. -/
theorem integral_rectangle_eq_normalized (f : ℝ → ℝ → ℝ) (a b : ℝ) :
    a * b * (∫ s : I, ∫ t : I, f (a * (s : ℝ)) (b * (t : ℝ))) =
      ∫ s in (0 : ℝ)..a, ∫ t in (0 : ℝ)..b, f s t := by
  have hscale (g : ℝ → ℝ) (r : ℝ) :
      r * (∫ s : I, g (r * (s : ℝ))) = ∫ s in (0 : ℝ)..r, g s := by
    rw [integral_unitInterval (fun s : ℝ ↦ g (r * s))]
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left g (a := 0) (b := 1) r
  rw [mul_assoc, ← integral_const_mul]
  simp_rw [hscale]
  exact hscale (fun s : ℝ ↦ ∫ t in (0 : ℝ)..b, f s t) a

/-- The first characteristic derivative is the single remaining primitive. -/
theorem hasDerivAt_polynomial_goursat_first {c : ℝ → ℝ} {W : Parameter → ℝ} {δ a b ε : ℝ}
    (hc : ContDiff ℝ 1 c) (hW : ContDiff ℝ 1 W)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2)
    (hp : (a, b, ε) ∈ Metric.ball 0 δ) :
    HasDerivAt (fun s : ℝ ↦ W (s, b, ε))
      (ε + ∫ t in (0 : ℝ)..b, c (a - t) * W (a, t, ε) ^ 2) a := by
  have hf : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ c (z.1 - z.2) * W (z.1, z.2, ε) ^ 2) :=
    (hc.comp (contDiff_fst.sub contDiff_snd)).mul
      ((hW.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).pow 2)
  have hA : Continuous (fun s : ℝ ↦ ∫ t in (0 : ℝ)..b, c (s - t) * W (s, t, ε) ^ 2) :=
    (contDiff_intervalIntegral hf 0 b).continuous
  have hd := ((hasDerivAt_id a).const_mul ε).add
    (intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable 0 a)
      hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt)
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  have hpath : Continuous (fun s : ℝ ↦ (s, b, ε)) := continuous_id.prodMk continuous_const
  filter_upwards [hpath.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with s hs
  exact heq (s, b, ε) hs

/-- Differentiating the remaining primitive gives the polynomial mixed PDE. -/
theorem hasDerivAt_polynomial_goursat_mixed {c : ℝ → ℝ} {W : Parameter → ℝ} {δ a b ε : ℝ}
    (hc : ContDiff ℝ 1 c) (hW : ContDiff ℝ 1 W)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2)
    (hp : (a, b, ε) ∈ Metric.ball 0 δ) :
    HasDerivAt (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a) (c (a - b) * W (a, b, ε) ^ 2) b := by
  have hf : Continuous (fun t : ℝ ↦ c (a - t) * W (a, t, ε) ^ 2) :=
    (hc.continuous.comp (continuous_const.sub continuous_id)).mul
      ((hW.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))).pow 2)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 b)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_add ε
  apply hd.congr_of_eventuallyEq
  have hpath : Continuous (fun t : ℝ ↦ (a, t, ε)) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  filter_upwards [hpath.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with t ht
  exact (hasDerivAt_polynomial_goursat_first hc hW heq ht).deriv

/-- The constructed field vanishes on the incoming characteristic. -/
theorem polynomial_goursat_zero_characteristic {c : ℝ → ℝ} {W : Parameter → ℝ} {δ b ε : ℝ}
    (heq : ∀ p ∈ Metric.ball 0 δ,
      W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
        c (s - t) * W (s, t, p.2.2) ^ 2)
    (hp : ((0 : ℝ), b, ε) ∈ Metric.ball 0 δ) : W (0, b, ε) = 0 := by
  simpa using heq (0, b, ε) hp

/-- The other characteristic carries the prescribed linear displacement. -/
theorem polynomial_goursat_linear_characteristic {c : ℝ → ℝ} {W : Parameter → ℝ} {δ a ε : ℝ}
    (heq : ∀ p ∈ Metric.ball 0 δ,
      W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
        c (s - t) * W (s, t, p.2.2) ^ 2)
    (hp : (a, (0 : ℝ), ε) ∈ Metric.ball 0 δ) : W (a, 0, ε) = ε * a := by
  simpa using heq (a, 0, ε) hp

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
