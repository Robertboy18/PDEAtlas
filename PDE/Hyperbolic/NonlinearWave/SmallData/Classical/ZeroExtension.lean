/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Matching a forward curve to a backward initial jet

A right derivative on a closed positive interval and a matching derivative of
a backward extension give an ordinary derivative at zero. This supplies genuine
two-sided initial regularity when a forward Sobolev construction is observed
as a classical spacetime field.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {E : Type*} [NormedAddCommGroup E]

/-- Use the prescribed backward field below zero and the forward field from zero. -/
def pasteZero (f g : ℝ → E) (t : ℝ) : E :=
  if 0 ≤ t then f t else g t

/-- Matching values suffice for continuity of the pasted curve. -/
theorem continuous_pasteZero {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) (heq : f 0 = g 0) :
    Continuous (pasteZero f g) := by
  apply hf.if_le hg continuous_const continuous_id
  intro t ht
  change (0 : ℝ) = t at ht
  simpa only [← ht] using heq

variable [NormedSpace ℝ E]

/-- A matching right and left derivative is an ordinary derivative at zero. -/
theorem hasDerivAt_pasteZero_zero {f g : ℝ → E} {v : E} {b : ℝ} (hb : 0 < b)
    (hf : HasDerivWithinAt f v (Icc 0 b) 0) (hg : HasDerivAt g v 0) (heq : f 0 = g 0) :
    HasDerivAt (pasteZero f g) v 0 := by
  have hright : HasDerivWithinAt (pasteZero f g) v (Icc 0 b) 0 := by
    apply hf.congr_of_mem _ ⟨le_rfl, hb.le⟩
    intro t ht
    simp only [pasteZero, ite_eq_left ht.1]
  have hleft : HasDerivWithinAt (pasteZero f g) v (Iic 0) 0 := by
    apply (hg.hasDerivWithinAt (s := Iic 0)).congr_of_mem _ (show (0 : ℝ) ∈ Iic 0 from le_rfl)
    intro t ht
    by_cases htz : t = 0
    · subst t
      simpa only [pasteZero, ite_eq_left le_rfl] using heq
    · simp only [pasteZero, ite_eq_right (not_le.mpr (lt_of_le_of_ne ht htz))]
  have hnhds : Iic 0 ∪ Icc 0 b ∈ 𝓝 (0 : ℝ) := by
    apply mem_of_superset (Iic_mem_nhds hb)
    intro t ht
    by_cases ht0 : t ≤ 0
    · exact Or.inl ht0
    · exact Or.inr ⟨(lt_of_not_ge ht0).le, ht⟩
  exact (hleft.union hright).hasDerivAt hnhds

/-- Before the positive endpoint the pasted derivative is the pasted pair of
derivative fields, including the initial slice. -/
theorem hasDerivAt_pasteZero {f g df dg : ℝ → E} {b t : ℝ} (hb : 0 < b) (heq : f 0 = g 0)
    (hdeq : df 0 = dg 0) (hf : ∀ s ∈ Icc 0 b, HasDerivWithinAt f (df s) (Icc 0 b) s)
    (hg : ∀ s, HasDerivAt g (dg s) s) (ht : t < b) :
    HasDerivAt (pasteZero f g) (pasteZero df dg t) t := by
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · have he : pasteZero f g =ᶠ[𝓝 t] g := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      simp only [pasteZero, ite_eq_right (not_le.mpr hs)]
    simpa only [pasteZero, ite_eq_right (not_le.mpr hneg)] using (hg t).congr_of_eventuallyEq he
  · subst t
    simp only [pasteZero, ite_eq_left le_rfl]
    exact hasDerivAt_pasteZero_zero hb (hf 0 ⟨le_rfl, hb.le⟩) (hdeq.symm ▸ hg 0) heq
  · have he : pasteZero f g =ᶠ[𝓝 t] f := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      simp only [pasteZero, ite_eq_left hs.le]
    simpa only [pasteZero, ite_eq_left hpos.le] using
      ((hf t ⟨hpos.le, ht.le⟩).hasDerivAt (Icc_mem_nhds hpos ht)).congr_of_eventuallyEq he

end WaveEquation.SmallData.Classical
