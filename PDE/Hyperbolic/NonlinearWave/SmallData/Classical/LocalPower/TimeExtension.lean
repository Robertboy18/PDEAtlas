/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Extending a field from a time strip

A smooth time map into the strip gives a globally C² representative which
agrees with the original field on a smaller strip.
-/

@[expose] public noncomputable section

open Set

namespace WaveEquation.SmallData.Classical.LocalPower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C² function on an open time strip has a global C² representative agreeing
with it on a smaller strip, uniformly in the spatial variable. -/
theorem exists_time_extension {T : ℝ} (hT : 0 < T) {v : ℝ × E → ℝ}
    (hv : ContDiffOn ℝ 2 v {p | |p.1| < T}) :
    ∃ S : ℝ, 0 < S ∧ S < T ∧ ∃ V : ℝ × E → ℝ, ContDiff ℝ 2 V ∧ ∀ p, |p.1| < S → V p = v p := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨T / 4, T / 2, by positivity, by linarith⟩
  let c : ℝ → ℝ := fun t ↦ t * b t
  have hc : ContDiff ℝ 2 c := contDiff_id.mul b.contDiff
  have hbound (t : ℝ) : |c t| < T := by
    by_cases ht : |t| < T / 2
    · calc
        |c t| = |t| * b t := by
          dsimp only [c]
          rw [abs_mul, abs_of_nonneg b.nonneg]
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left b.le_one (abs_nonneg t)
        _ < T := by linarith
    · have hb : b t = 0 := b.zero_of_le_dist (by
        simpa only [b, dist_zero_right, Real.norm_eq_abs] using le_of_not_gt ht)
      simpa only [c, hb, mul_zero, abs_zero] using hT
  refine ⟨T / 4, by positivity, by linarith, fun p ↦ v (c p.1, p.2), ?_, ?_⟩
  · exact hv.comp_contDiff ((hc.comp contDiff_fst).prodMk contDiff_snd) (fun p ↦ hbound p.1)
  · intro p hp
    have hb : b p.1 = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, b] using hp.le)
    simp only [c, hb, mul_one]

end WaveEquation.SmallData.Classical.LocalPower
