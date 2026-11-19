/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import CAS.ExactTactic

/-!
# Real mollification with control of the first derivative

Convolution by a normalized smooth bump improves regularity, preserves oddness,
and preserves zero collars after shrinking them by the kernel radius. For a compact
`C¹` input, both the value and its derivative converge uniformly.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology Convolution

namespace PDE.Analysis.Calculus

/-- Convolution with a normalized, even, compact smooth kernel. -/
def realMollify (φ : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ) : ℝ → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

theorem contDiff_realMollify (φ : ContDiffBump (0 : ℝ)) {f : ℝ → ℝ}
    (hf : Continuous f) {n : ℕ∞} : ContDiff ℝ n (realMollify φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _
    φ.contDiff_normed hf.locallyIntegrable

theorem hasCompactSupport_realMollify (φ : ContDiffBump (0 : ℝ)) {f : ℝ → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (realMollify φ f) :=
  φ.hasCompactSupport_normed.convolution _ hf

/-- Differentiation acts on the `C¹` input, so the error in its derivative is another
ordinary mollification error. -/
theorem deriv_realMollify (φ : ContDiffBump (0 : ℝ)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    deriv (realMollify φ f) = realMollify φ (deriv f) := by
  funext x
  exact (hfc.hasDerivAt_convolution_right _
    φ.integrable_normed.locallyIntegrable hf x).deriv

/-- The even kernel preserves oddness without a subsequent symmetrization. -/
theorem realMollify_neg (φ : ContDiffBump (0 : ℝ)) {f : ℝ → ℝ}
    (hodd : ∀ x, f (-x) = -f x) (x : ℝ) :
    realMollify φ f (-x) = -realMollify φ f x := by
  change (∫ t, φ.normed volume t * f (-x - t)) =
    -(∫ t, φ.normed volume t * f (x - t))
  rw [← integral_neg_eq_self]
  simp only [φ.normed_neg, sub_neg_eq_add]
  have heq : (fun t ↦ φ.normed volume t * f (-x + t)) =
      (fun t ↦ -(φ.normed volume t * f (x - t))) := by
    funext t
    rw [show -x + t = -(x - t) by cas, hodd, mul_neg]
  rw [heq, integral_neg]

/-- If the input vanishes on a centered interval, convolution vanishes on the interval
shrunk by the kernel radius. -/
theorem realMollify_eq_zero_of_inner {φ : ContDiffBump (0 : ℝ)} {f : ℝ → ℝ}
    {r x : ℝ} (hf : ∀ y, |y| < r → f y = 0) (hx : |x| + φ.rOut ≤ r) :
    realMollify φ f x = 0 := by
  have hball : ∀ y ∈ ball x φ.rOut, f y = f x := by
    intro y hy
    have hy' : |y - x| < φ.rOut := by simpa only [mem_ball, Real.dist_eq] using hy
    have hxy : |y| < r := calc
      |y| ≤ |y - x| + |x| := by
        simpa only [sub_add_cancel] using abs_add_le (y - x) x
      _ < φ.rOut + |x| := add_lt_add_of_lt_of_le hy' le_rfl
      _ ≤ r := by cas
    rw [hf y hxy, hf x (by have := φ.rOut_pos; cas)]
  exact (ContDiffBump.normed_convolution_eq_right hball).trans
    (hf x (by have := φ.rOut_pos; cas))

/-- An outer zero collar likewise survives convolution after enlarging the support
radius by the kernel radius. -/
theorem realMollify_eq_zero_of_outer {φ : ContDiffBump (0 : ℝ)} {f : ℝ → ℝ}
    {R x : ℝ} (hf : ∀ y, R ≤ |y| → f y = 0) (hx : R + φ.rOut ≤ |x|) :
    realMollify φ f x = 0 := by
  have hball : ∀ y ∈ ball x φ.rOut, f y = f x := by
    intro y hy
    have hy' : |x - y| < φ.rOut := by
      simpa only [mem_ball, Real.dist_eq, abs_sub_comm] using hy
    have hxy : R ≤ |y| := by
      have htri : |x| ≤ |x - y| + |y| := by
        simpa only [sub_add_cancel] using abs_add_le (x - y) y
      cas
    rw [hf y hxy, hf x (by have := φ.rOut_pos; cas)]
  exact (ContDiffBump.normed_convolution_eq_right hball).trans
    (hf x (by have := φ.rOut_pos; cas))

/-- Every sufficiently small normalized bump approximates both available jets uniformly.
The hypotheses concern only the input, not an assumed approximation error. -/
theorem exists_realMollify_uniform_jet_radius {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ φ : ContDiffBump (0 : ℝ), φ.rOut ≤ d →
      (∀ x, |realMollify φ f x - f x| ≤ ε) ∧
      (∀ x, |deriv (realMollify φ f) x - deriv f x| ≤ ε) := by
  obtain ⟨d₀, hd₀, h₀⟩ := Metric.uniformContinuous_iff.mp
    (hfc.uniformContinuous_of_continuous hf.continuous) ε hε
  obtain ⟨d₁, hd₁, h₁⟩ := Metric.uniformContinuous_iff.mp
    (hfc.deriv.uniformContinuous_of_continuous hf.continuous_deriv_one) ε hε
  refine ⟨min d₀ d₁, lt_min hd₀ hd₁, fun φ hφ ↦ ⟨?_, ?_⟩⟩
  · intro x
    exact φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
      (fun y hy ↦ (h₀ (lt_of_lt_of_le hy (hφ.trans (min_le_left _ _)))).le)
  · intro x
    rw [deriv_realMollify φ hf hfc]
    exact φ.dist_normed_convolution_le hf.continuous_deriv_one.aestronglyMeasurable
      (fun y hy ↦ (h₁ (lt_of_lt_of_le hy (hφ.trans (min_le_right _ _)))).le)

end PDE.Analysis.Calculus
