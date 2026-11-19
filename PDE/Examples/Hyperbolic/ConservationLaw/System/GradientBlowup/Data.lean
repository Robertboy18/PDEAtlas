/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import CAS.ExactTactic

/-!
# Smooth compact compression data

Multiplying `-x` by Mathlib's smooth bump gives compact initial
data with derivative `-1` at the origin. The bump equals one near the origin, so
the datum equals `-x` there.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup

/-- A smooth cutoff equal to one on the unit interval. -/
def cutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- Compact smooth compression with unit negative slope at zero. -/
def compression (x : ℝ) : ℝ := -x * cutoff x

/-- The compression datum is smooth. -/
theorem contDiff_compression : ContDiff ℝ ∞ compression :=
  contDiff_id.neg.mul cutoff.contDiff

/-- The compression datum has compact support. -/
theorem hasCompactSupport_compression : HasCompactSupport compression :=
  cutoff.hasCompactSupport.mul_left

/-- Near the origin the datum is `-x`. -/
theorem compression_eventuallyEq : compression =ᶠ[𝓝 0] fun x ↦ -x := by
  filter_upwards [cutoff.eventuallyEq_one] with x hx
  simp only [compression, hx, Pi.one_apply, mul_one]

/-- The derivative of the datum at the origin is `-1`. -/
theorem hasDerivAt_compression_zero : HasDerivAt compression (-1) 0 := by
  have hd : HasDerivAt (fun x : ℝ ↦ -x) (-1) 0 := by cas
  exact hd.congr_of_eventuallyEq compression_eventuallyEq

/-- `deriv compression 0 = -1`. -/
theorem deriv_compression_zero : deriv compression 0 = -1 :=
  hasDerivAt_compression_zero.deriv

/-- The datum vanishes at the origin. -/
@[simp] theorem compression_zero : compression 0 = 0 := by
  simp only [compression, neg_zero, zero_mul]

end PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup
