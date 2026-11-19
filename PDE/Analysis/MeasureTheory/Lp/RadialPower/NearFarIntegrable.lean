/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Integrability from near-origin and far-field power bounds

On a finite-dimensional real space of dimension `d ≥ 1` with an additive Haar measure, a function
bounded on a measurable set `s` by `A ‖x‖^(-a)` near the origin and by `C ‖x‖^(-b)` away from it
is integrable on `s` when `a < d < b`: the singularity at the origin and the tail are both
integrable.

## Main results

* `MeasureTheory.integrableOn_of_norm_le_rpow_near_far`: `‖f x‖ ≤ A ‖x‖^(-a)` on `s` inside the
  unit ball and `‖f x‖ ≤ C ‖x‖^(-b)` on `s` outside it, with `a < d < b`, make `f` integrable on
  `s`.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Metric Set Filter

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Integrability from radial power bounds.** If `‖f x‖ ≤ A ‖x‖^(-a)` on `s` inside the unit
ball (off the origin) and `‖f x‖ ≤ C ‖x‖^(-b)` on `s` outside it, with `a < d < b` for the
dimension `d ≥ 1`, then `f` is integrable on `s`. -/
theorem integrableOn_of_norm_le_rpow_near_far {f : E → G} {s : Set E} (hs : MeasurableSet s)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hd : 1 ≤ Module.finrank ℝ E) {a b A C : ℝ}
    (ha : a < Module.finrank ℝ E) (hb : (Module.finrank ℝ E : ℝ) < b)
    (hnear : ∀ x ∈ s, x ≠ 0 → ‖x‖ < 1 → ‖f x‖ ≤ A * ‖x‖ ^ (-a))
    (hfar : ∀ x ∈ s, 1 ≤ ‖x‖ → ‖f x‖ ≤ C * ‖x‖ ^ (-b)) :
    IntegrableOn f s μ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set g : E → G := s.indicator f with hg
  have hgm : AEStronglyMeasurable g μ := (aestronglyMeasurable_indicator_iff hs).2 hf
  have hnear' : IntegrableOn g (ball 0 1) μ := by
    refine integrableOn_ball_of_norm_le_rpow (C := max A 0) hd ha ?_ hgm
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae (μ.ae_ne (0 : E))] with x hx hx0
    have hx1 : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    by_cases hxs : x ∈ s
    · rw [hg, indicator_of_mem hxs]
      exact (hnear x hxs hx0 hx1).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
    · rw [hg, indicator_of_notMem hxs, norm_zero]
      positivity
  have hfar' : IntegrableOn g (ball (0 : E) 1)ᶜ μ := by
    refine (((integrable_one_add_norm (μ := μ) hb).const_mul
      (max C 0 * 2 ^ b)).integrableOn).mono' hgm.restrict ?_
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet.compl] with x hx
    have hx1 : 1 ≤ ‖x‖ := by simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
    have hx0 : 0 < ‖x‖ := by linarith
    have hb0 : 0 < b := lt_of_le_of_lt (Nat.cast_nonneg _) hb
    have hpow : ‖x‖ ^ (-b) ≤ 2 ^ b * (1 + ‖x‖) ^ (-b) := by
      have h1 : (2 * ‖x‖) ^ (-b) ≤ (1 + ‖x‖) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have h2 : (2 * ‖x‖) ^ (-b) = 2 ^ (-b) * ‖x‖ ^ (-b) := Real.mul_rpow (by norm_num) hx0.le
      calc ‖x‖ ^ (-b) = 2 ^ b * (2 * ‖x‖) ^ (-b) := by
            rw [h2, ← mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero,
              one_mul]
        _ ≤ 2 ^ b * (1 + ‖x‖) ^ (-b) := by gcongr
    by_cases hxs : x ∈ s
    · rw [hg, indicator_of_mem hxs]
      calc ‖f x‖ ≤ C * ‖x‖ ^ (-b) := hfar x hxs hx1
        _ ≤ max C 0 * ‖x‖ ^ (-b) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
        _ ≤ max C 0 * (2 ^ b * (1 + ‖x‖) ^ (-b)) :=
          mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
        _ = _ := by ring
    · rw [hg, indicator_of_notMem hxs, norm_zero]
      positivity
  have hall : IntegrableOn g univ μ := by
    simpa only [union_compl_self] using hnear'.union hfar'
  rw [integrableOn_univ, hg, integrable_indicator_iff hs] at hall
  exact hall

end MeasureTheory
