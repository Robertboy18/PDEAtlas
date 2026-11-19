/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Continuity

/-!
# Differentiation of the Hilbert principal value

The derivative of the cancellation kernel is the cancellation kernel of the
input derivative. Compact support and a Lipschitz bound for that derivative give
the domination required to differentiate under the ordinary integral.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped ContDiff NNReal Topology

noncomputable section

/-- Differentiation in the evaluation point commutes with the fixed-radius
cancellation kernel, including its defined value at zero. -/
theorem hasDerivAt_hilbertRegularizedKernel_eval {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (x R t : ℝ) :
    HasDerivAt (fun y ↦ hilbertRegularizedKernel f y R t)
      (hilbertRegularizedKernel (deriv f) x R t) x := by
  have hshift := (hf (x - t)).hasDerivAt.comp_sub_const x t
  unfold hilbertRegularizedKernel
  by_cases ht : |t| < R
  · simp only [indicator_of_mem (s := {s : ℝ | |s| < R}) ht]
    exact (hshift.sub (hf x).hasDerivAt).div_const t
  · simp only [indicator_of_notMem (s := {s : ℝ | |s| < R}) ht, sub_zero]
    exact hshift.div_const t

/-- For compactly supported differentiable input with Lipschitz derivative, the
principal value is differentiable and its derivative is the principal value
of the input derivative. -/
theorem hasDerivAt_hilbertPV_of_lipschitzWith_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hsupp : HasCompactSupport f)
    {K : ℝ≥0} (hderiv : LipschitzWith K (deriv f)) (x : ℝ) :
    HasDerivAt (hilbertPV f) (hilbertPV (deriv f) x) x := by
  have hC1 : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr ⟨hf, hderiv.continuous⟩
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hC1 (by norm_num)
  have hint (y : ℝ) := integrable_hilbertRegularizedKernel_one_of_lipschitzWith hC hsupp y
  have hint' (y : ℝ) :=
    integrable_hilbertRegularizedKernel_one_of_lipschitzWith hderiv hsupp.deriv y
  obtain ⟨bound, hbound, hdom⟩ :=
    exists_integrable_bound_hilbertRegularizedKernel_one hderiv hsupp.deriv x
  have hdiff : HasDerivAt (fun y ↦ ∫ t, hilbertRegularizedKernel f y 1 t)
      (∫ t, hilbertRegularizedKernel (deriv f) x 1 t) x := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds x zero_lt_one)
      (Eventually.of_forall fun y ↦ (hint y).aestronglyMeasurable) (hint x)
      (hint' x).aestronglyMeasurable _ hbound _).2
    · exact Eventually.of_forall fun t y hy ↦ hdom y hy t
    · exact Eventually.of_forall fun t y _ ↦ hasDerivAt_hilbertRegularizedKernel_eval hf y 1 t
  have hscaled := hdiff.const_mul Real.pi⁻¹
  rw [← (hasHilbertPV_of_regularized (hint' x)).hilbertPV_eq] at hscaled
  exact hscaled.congr_of_eventuallyEq (Eventually.of_forall fun y ↦
    (hasHilbertPV_of_regularized (hint y)).hilbertPV_eq)

/-- Compact `C²` input satisfies classical commutation of differentiation with
the Hilbert principal value. -/
theorem hasDerivAt_hilbertPV_of_contDiff_two_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (hilbertPV f) (hilbertPV (deriv f) x) x := by
  have hC1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp.deriv hC1 (by norm_num)
  exact hasDerivAt_hilbertPV_of_lipschitzWith_deriv (hf.differentiable (by norm_num)) hsupp hK x

/-- The commutation identity as an equality of functions for compact `C²` input. -/
theorem deriv_hilbertPV_of_contDiff_two_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f) :
    deriv (hilbertPV f) = hilbertPV (deriv f) :=
  funext fun x ↦ (hasDerivAt_hilbertPV_of_contDiff_two_compactSupport hf hsupp x).deriv

/-- One additional continuous derivative of compactly supported input suffices
for each finite order of regularity of its principal value. -/
theorem contDiff_hilbertPV_of_contDiff_succ_compactSupport (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (n + 1) f) (hsupp : HasCompactSupport f) :
    ContDiff ℝ n (hilbertPV f) := by
  induction n generalizing f with
  | zero =>
    exact contDiff_zero.mpr (continuous_hilbertPV_of_contDiff_one_compactSupport hf hsupp)
  | succ n ih =>
    have hC2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast Nat.le_add_left 2 n)
    simp only [Nat.cast_add, Nat.cast_one] at hf ⊢
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun x ↦
      (hasDerivAt_hilbertPV_of_contDiff_two_compactSupport hC2 hsupp x).differentiableAt, ?_, ?_⟩
    · simp
    · rw [deriv_hilbertPV_of_contDiff_two_compactSupport hC2 hsupp]
      exact ih hf.deriv' hsupp.deriv

/-- Smooth compactly supported input has a smooth Hilbert principal value. -/
theorem contDiff_hilbertPV_of_contDiff_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) :
    ContDiff ℝ ∞ (hilbertPV f) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_hilbertPV_of_contDiff_succ_compactSupport n (hf.of_le (by simp)) hsupp

end

end PDE.Analysis
