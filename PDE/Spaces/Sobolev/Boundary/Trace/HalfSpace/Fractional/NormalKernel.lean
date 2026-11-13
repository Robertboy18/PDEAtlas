/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Polar
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.NormalIncrement

/-!
# Radial control of normal trace increments

Polar integration reduces the normal part of the fractional trace kernel to
the one-dimensional Hardy weight. Its integral is bounded by the physical
normal partial energy on the upper half-space. The same bound applies to
functions with values in any real Banach space.
-/

@[expose] public section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ^(n + 1) → F}

/-- For positive boundary dimension, the normal fractional trace kernel is
controlled by the upper half-space normal derivative energy with the exact
angular mass and Hardy constant. -/
theorem lintegral_normal_kernel_le (hn : 1 ≤ n) {p : ℝ} (hp : 1 < p)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n,
      ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
        ENNReal.ofReal (‖normalSlice f x ‖h‖ - normalSlice f x 0‖ ^ p)) ≤
      (volume : Measure (ℝ^n)).toSphere univ *
        ENNReal.ofReal ((p / (p - 1)) ^ p *
          ∫ z in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) z‖ ^ p) := by
  let : Nontrivial (ℝ^n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using Nat.zero_lt_one.trans_le hn)
  have hradial (x : ℝ^n) :
      (∫⁻ h : ℝ^n,
        ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
          ENNReal.ofReal (‖normalSlice f x ‖h‖ - normalSlice f x 0‖ ^ p)) =
        (volume : Measure (ℝ^n)).toSphere univ *
          ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (‖normalSlice f x r - normalSlice f x 0‖ ^ p * r ^ (-p)) := by
    have hslice : Continuous (normalSlice f x) := (normalSlice_contDiff hf x).continuous
    calc
      _ = (volume : Measure (ℝ^n)).toSphere univ *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (-p)) *
            ENNReal.ofReal (‖normalSlice f x r - normalSlice f x 0‖ ^ p) := by
        simpa using lintegral_norm_rpow_mul_addHaar (volume : Measure (ℝ^n)) p
          (f := fun r ↦ ENNReal.ofReal (‖normalSlice f x r - normalSlice f x 0‖ ^ p))
          (ENNReal.measurable_ofReal.comp
            ((hslice.sub continuous_const).norm.measurable.pow_const p))
      _ = _ := by
        congr 1
        apply lintegral_congr
        intro r
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), mul_comm]
  calc
    _ = ∫⁻ x : ℝ^n, (volume : Measure (ℝ^n)).toSphere univ *
        ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (‖normalSlice f x r - normalSlice f x 0‖ ^ p * r ^ (-p)) :=
      lintegral_congr hradial
    _ = (volume : Measure (ℝ^n)).toSphere univ *
        ∫⁻ x : ℝ^n, ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (‖normalSlice f x r - normalSlice f x 0‖ ^ p * r ^ (-p)) :=
      lintegral_const_mul _ (measurable_lintegral_normal_increment hf.continuous p)
    _ ≤ _ := mul_le_mul_right (lintegral_normal_increment_le hp hf hfc) _

end SobolevSpace.Trace.HalfSpace
