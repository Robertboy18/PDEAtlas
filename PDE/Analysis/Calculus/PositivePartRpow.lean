/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real powers of the positive part

For every real exponent greater than one, the positive-part power is `C¹`.
Its derivative exists and vanishes at zero, as shown by matching the two
one-sided derivatives. This calculus applies to nonlinear diffusion potentials
and to cutoffs with nonintegral powers.
-/

@[expose] public section

namespace PDE.Analysis

open Set Filter
open scoped Topology

/-- A positive-part real power of exponent greater than one has derivative zero
at the interface, and the usual derivative formula on the whole real line. -/
theorem hasDerivAt_posPart_rpow {q : ℝ} (hq : 1 < q) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y⁺ ^ q) (q * x⁺ ^ (q - 1)) x := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hq1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [posPart_eq_zero.mpr hx.le, Real.zero_rpow hq1, mul_zero]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [posPart_eq_zero.mpr (le_of_lt hy), hq0]
  · have hleft : HasDerivWithinAt (fun y : ℝ ↦ y⁺ ^ q) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr
      · intro y hy
        simp [posPart_eq_zero.mpr hy, hq0]
      · simp [hq0]
    have hright : HasDerivWithinAt (fun y : ℝ ↦ y⁺ ^ q) 0 (Ici 0) 0 := by
      have hp : HasDerivAt (fun y : ℝ ↦ y ^ q) 0 0 := by
        simpa [hq1] using (Real.hasDerivAt_rpow_const (x := 0) (Or.inr hq.le))
      apply hp.hasDerivWithinAt.congr
      · intro y hy
        rw [posPart_eq_self.mpr hy]
      · simp
    simpa [hq1] using hleft.union hright
  · rw [posPart_eq_self.mpr hx.le]
    apply (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [posPart_eq_self.mpr (le_of_lt hy)]

/-- The derivative of the positive-part power is continuous across zero. -/
theorem contDiff_one_posPart_rpow {q : ℝ} (hq : 1 < q) :
    ContDiff ℝ 1 (fun x : ℝ ↦ x⁺ ^ q) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_posPart_rpow hq x).differentiableAt, ?_⟩
  have heq : deriv (fun x : ℝ ↦ x⁺ ^ q) = fun x ↦ q * x⁺ ^ (q - 1) :=
    funext fun x ↦ (hasDerivAt_posPart_rpow hq x).deriv
  rw [heq]
  exact continuous_const.mul
    ((Real.continuous_rpow_const (sub_nonneg.mpr hq.le)).comp continuous_posPart)

end PDE.Analysis
