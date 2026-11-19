/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# The normalized normal-frequency kernel

For a positive tangential frequency scale `a`, the square root of the centered
Cauchy density has unit `L²` norm in the normal frequency. Multiplication by
this kernel will give the isometric lifting in Fourier coordinates for the
hyperplane trace theorem. The normalization is Mathlib's Cauchy integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional.Trace

/-- The Cauchy square-root kernel, with unit `L²` norm when `a ≠ 0`. -/
def normalKernel (a : ℝ≥0) (t : ℝ) : ℝ :=
  Real.sqrt (cauchyPDFReal 0 a t)

/-- The normal-frequency kernel is nonnegative. -/
theorem normalKernel_nonneg (a : ℝ≥0) (t : ℝ) : 0 ≤ normalKernel a t :=
  Real.sqrt_nonneg _

/-- Squaring the kernel recovers the normalized Cauchy density. -/
theorem normalKernel_sq (a : ℝ≥0) (t : ℝ) :
    normalKernel a t ^ 2 = cauchyPDFReal 0 a t := by
  apply Real.sq_sqrt
  unfold cauchyPDFReal
  positivity

/-- Reflection in normal frequency leaves the kernel unchanged. -/
theorem normalKernel_neg (a : ℝ≥0) (t : ℝ) :
    normalKernel a (-t) = normalKernel a t := by
  simp [normalKernel, cauchyPDFReal]

/-- The kernel is measurable even at the totalized zero scale. -/
theorem measurable_normalKernel (a : ℝ≥0) : Measurable (normalKernel a) :=
  (measurable_cauchyPDFReal 0 a).sqrt

/-- The kernel is square integrable. -/
theorem memLp_normalKernel (a : ℝ≥0) : MemLp (normalKernel a) 2 volume := by
  rw [memLp_two_iff_integrable_sq (measurable_normalKernel a).aestronglyMeasurable]
  simpa only [normalKernel_sq] using integrable_cauchyPDFReal (x₀ := 0) (γ := a)

/-- A positive frequency scale gives exactly unit squared integral. -/
theorem integral_normalKernel_sq (a : ℝ≥0) (ha : a ≠ 0) :
    ∫ t : ℝ, normalKernel a t ^ 2 = 1 := by
  simpa only [normalKernel_sq] using integral_cauchyPDFReal_eq_one 0 ha

/-- The normalized normal-frequency kernel has unit `L²` norm. -/
theorem norm_normalKernel_toLp (a : ℝ≥0) (ha : a ≠ 0) :
    ‖(memLp_normalKernel a).toLp (normalKernel a)‖ = 1 := by
  have hs : ‖(memLp_normalKernel a).toLp (normalKernel a)‖ ^ 2 = 1 := by
    rw [Lp.norm_sq_eq_integral_sq]
    calc
      _ = ∫ t : ℝ, normalKernel a t ^ 2 :=
        integral_congr_ae ((memLp_normalKernel a).coeFn_toLp.fun_comp (fun x : ℝ ↦ x ^ 2))
      _ = 1 := integral_normalKernel_sq a ha
  nlinarith [norm_nonneg ((memLp_normalKernel a).toLp (normalKernel a))]

end SobolevSpace.Fractional.Trace
