/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Gronwall
import CAS.ExactTactic

/-!
# Grönwall comparison from interior derivatives

Continuity at the two endpoints and a differential inequality in the interior
give the same Grönwall bound on the whole closed interval. The integrating
factor never differentiates the endpoint traces.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution

/-- Grönwall comparison with derivatives only in the interior and continuous
endpoint traces. The integrating factor avoids any one-sided endpoint derivative. -/
theorem le_gronwallBound_of_deriv_le_interior
    {e : ℝ → ℝ} {a b δ K ε : ℝ}
    (he : ContinuousOn e (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ e t)
    (ha : e a ≤ δ)
    (hbound : ∀ t ∈ Ioo a b, deriv e t ≤ K * e t + ε) :
    ∀ t ∈ Icc a b, e t ≤ gronwallBound δ K ε (t - a) := by
  let g := fun t ↦ gronwallBound δ K ε (t - a)
  let h := fun t ↦ (e t - g t) * Real.exp (-K * (t - a))
  have hg (t : ℝ) : HasDerivAt g (K * g t + ε) t :=
    hasDerivAt_gronwallBound_shift δ K ε t a
  have hexp (t : ℝ) : HasDerivAt (fun s ↦ Real.exp (-K * (s - a)))
      (-K * Real.exp (-K * (t - a))) t := by
    cas
  have hh (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt h ((deriv e t - (K * e t + ε)) * Real.exp (-K * (t - a))) t := by
    convert ((hd t ht).hasDerivAt.sub (hg t)).mul (hexp t) using 1
    cas
  have hanti : AntitoneOn h (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      ((he.sub (fun t _ ↦ (hg t).continuousAt.continuousWithinAt)).mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn)
    · intro t ht
      exact (hh t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hbound t (by simpa only [interior_Icc] using ht)))
        (Real.exp_nonneg _)
  intro t ht
  have hle := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hzero : h a ≤ 0 := by
    simpa only [h, g, sub_self, gronwallBound_x0, mul_zero, Real.exp_zero, mul_one]
      using sub_nonpos.mpr ha
  have hsub : e t - g t ≤ 0 :=
    nonpos_of_mul_nonpos_left (hle.trans hzero) (Real.exp_pos _)
  exact sub_nonpos.mp hsub

/-- A nonnegative energy with zero initial trace vanishes throughout the
closed interval if its interior derivative is bounded by a constant times itself. -/
theorem eq_zero_on_Icc_of_deriv_le_mul {E : ℝ → ℝ} {a b K : ℝ}
    (hcont : ContinuousOn E (Icc a b)) (hnonneg : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ E t)
    (hbound : ∀ t ∈ Ioo a b, deriv E t ≤ K * E t) (hzero : E a = 0) :
    ∀ t ∈ Icc a b, E t = 0 := by
  have hle := le_gronwallBound_of_deriv_le_interior hcont hdiff
    (δ := 0) (ε := 0) hzero.le (fun t ht ↦ by simpa only [add_zero] using hbound t ht)
  intro t ht
  apply le_antisymm _ (hnonneg t ht)
  simpa only [gronwallBound_ε0_δ0] using hle t ht

end PDE.Analysis.Evolution
