/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Completion
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeEnergy
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Smooth

/-!
# Fractional energy of a Sobolev trace

The trace of a `W^{1,p}` function on the upper half-space has finite fractional
energy of order `1 - 1/p`, for every real `p > 1`. The bound depends only on the
dimension and exponent. Its right-hand side is the sum of the p-th powers of the
weak partial-derivative norms, written `‖∂[i] u‖ₑ ^ p`.

The smooth estimate splits a boundary difference through points at height
`‖x - y‖`, using Hardy's inequality in the normal direction and translation
estimates tangentially. Density and Fatou's lemma then give the estimate below
for the Sobolev trace. The order-zero Sobolev norm of each partial
derivative equals its `L^p` norm.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.Trace.HalfSpace

/-- Fractional trace energy is bounded by the weak partial-derivative energy,
with one finite constant for all functions. The zero-dimensional boundary is included, where
the estimate holds trivially. -/
theorem exists_trace_fractional_bound (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊),
      (∫⁻ z : ℝ^n × ℝ^n,
        ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] u‖ₑ ^ p := by
  obtain ⟨C, hC⟩ := exists_lintegral_smoothBoundaryValue_enorm_div_le (F := ℝ) n hp
  refine ⟨C, fun u ↦ ?_⟩
  have hsmooth (φ : GlobalTestFunction n) :=
    hC φ.1.toFun (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport
  simpa only [GraphSpace.enorm_partialDeriv_eq_wkpCoordinateCLM] using
    lintegral_traceLp_sub_rpow_div_le_of_smooth n p hp C hsmooth u

/-- The fractional trace energy is finite; no fractional regularity of the trace
is assumed in advance. -/
theorem lintegral_traceLp_sub_rpow_div_lt_top (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊)) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)) < ∞ := by
  obtain ⟨C, hC⟩ := exists_trace_fractional_bound n p hp
  apply lt_of_le_of_lt (hC u)
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  exact ENNReal.sum_lt_top.mpr fun i _ ↦
    ENNReal.rpow_lt_top_of_nonneg (zero_lt_one.trans hp).le enorm_ne_top

end SobolevSpace.Trace.HalfSpace
