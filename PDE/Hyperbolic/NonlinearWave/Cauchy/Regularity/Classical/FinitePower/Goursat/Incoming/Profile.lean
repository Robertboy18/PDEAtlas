/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import CAS.ExactTactic

/-!
# A compact incoming radial profile

The smooth profile has an exact early zero segment, a negative middle segment and a prescribed
linear jet near the initial sphere.
-/

@[expose] public noncomputable section

section

open Set Filter
open scoped ContDiff Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The incoming transition vanishes up to minus one half and equals one
from minus one quarter onward. -/
def incomingCutoff (s : ℝ) : ℝ := Real.smoothTransition (4 * s + 2)

/-- A compact profile agreeing with `s - 1` near the initial unit sphere. -/
def incomingProfile (s : ℝ) : ℝ :=
  (s - 1) * incomingCutoff s * (1 - Real.smoothTransition (2 * s - 3))

/-- The incoming transition is smooth to every order. -/
theorem contDiff_incomingCutoff : ContDiff ℝ ∞ incomingCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- The compact incoming profile is smooth to every order. -/
theorem contDiff_incomingProfile : ContDiff ℝ ∞ incomingProfile :=
  ((contDiff_id.sub contDiff_const).mul contDiff_incomingCutoff).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)))

/-- The transition takes values in the unit interval. -/
theorem incomingCutoff_mem_Icc (s : ℝ) : incomingCutoff s ∈ Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The incoming transition has exactly the prescribed zero half-line. -/
theorem incomingCutoff_eq_zero_iff (s : ℝ) : incomingCutoff s = 0 ↔ s ≤ -1 / 2 := by
  rw [incomingCutoff, Real.smoothTransition.zero_iff_nonpos]
  constructor <;> intro h <;> linarith

/-- At a zero of the nonnegative transition, its ordinary derivative is zero. -/
theorem deriv_incomingCutoff_eq_zero {s : ℝ} (hs : incomingCutoff s = 0) :
    deriv incomingCutoff s = 0 := by
  have hmin : IsLocalMin incomingCutoff s := by
    filter_upwards [] with t
    rw [hs]
    exact (incomingCutoff_mem_Icc t).1
  exact hmin.deriv_eq_zero

/-- The final cutoff does not alter the relevant incoming interval. -/
theorem incomingProfile_eq_of_le_one {s : ℝ} (hs : s ≤ 1) :
    incomingProfile s = (s - 1) * incomingCutoff s := by
  have hright : Real.smoothTransition (2 * s - 3) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [incomingProfile, hright, sub_zero, mul_one]

/-- The profile agrees with the required linear germ near the initial unit sphere. -/
theorem incomingProfile_eq_linear {s : ℝ} (hs : s ∈ Icc (3 / 4) (5 / 4)) :
    incomingProfile s = s - 1 := by
  have hleft : incomingCutoff s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith [hs.1])
  have hright : Real.smoothTransition (2 * s - 3) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith [hs.2])
  simp only [incomingProfile, hleft, hright, sub_zero, mul_one]

/-- The profile is supported in the fixed compact interval. -/
theorem hasCompactSupport_incomingProfile : HasCompactSupport incomingProfile := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1 / 2) (b := 2))
  intro s hs
  change incomingProfile s ≠ 0 at hs
  by_contra hmem
  rcases not_and_or.mp hmem with hleft | hright
  · have hzero := (incomingCutoff_eq_zero_iff s).mpr (lt_of_not_ge hleft).le
    exact hs (by simp only [incomingProfile, hzero, mul_zero, zero_mul])
  · have hone : Real.smoothTransition (2 * s - 3) = 1 :=
      Real.smoothTransition.one_of_one_le (by have := lt_of_not_ge hright; linarith)
    exact hs (by simp only [incomingProfile, hone, sub_self, mul_zero])

/-- The profile vanishes on the initial negative characteristic segment. -/
theorem incomingProfile_eq_zero {s : ℝ} (hs : s ≤ -1 / 2) : incomingProfile s = 0 := by
  simp only [incomingProfile, (incomingCutoff_eq_zero_iff s).mpr hs, mul_zero, zero_mul]

/-- The profile is strictly negative between its zero segment and the final zero. -/
theorem incomingProfile_neg {s : ℝ} (hs : s ∈ Ioo (-1 / 2) 1) : incomingProfile s < 0 := by
  rw [incomingProfile_eq_of_le_one hs.2.le]
  apply mul_neg_of_neg_of_pos (sub_neg.mpr hs.2)
  exact Real.smoothTransition.pos_of_pos (by linarith [hs.1])

/-- The final linear germ has unit derivative at its zero. -/
theorem hasDerivAt_incomingProfile_one : HasDerivAt incomingProfile 1 1 := by
  have hd : HasDerivAt (fun s : ℝ ↦ s - 1) 1 1 := by cas
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (1 : ℝ) ∈ Ioo (3 / 4) (5 / 4) by
    constructor <;> norm_num)] with s hs
  exact incomingProfile_eq_linear ⟨hs.1.le, hs.2.le⟩

/-- At every zero of the initial transition, the profile and its derivative vanish. -/
theorem incomingProfile_zero_jet {s : ℝ} (hs : incomingCutoff s = 0) :
    incomingProfile s = 0 ∧ deriv incomingProfile s = 0 := by
  have hsle := (incomingCutoff_eq_zero_iff s).mp hs
  have hzero := incomingProfile_eq_zero hsle
  refine ⟨hzero, ?_⟩
  have hmax : IsLocalMax incomingProfile s := by
    filter_upwards [isOpen_Iio.mem_nhds (show s < (1 : ℝ) by linarith)] with t ht
    rw [hzero, incomingProfile_eq_of_le_one ht.le]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.le) (incomingCutoff_mem_Icc t).1
  exact hmax.deriv_eq_zero

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
