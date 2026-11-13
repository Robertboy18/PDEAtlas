/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.PositivePart
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Smooth approximation in the nonnegative `Lᵖ` cone

For a finite regular measure on a finite-dimensional real normed space, every
nonnegative `Lᵖ` function, `1 ≤ p < ∞`, is a norm limit of globally nonnegative
smooth functions. Continuous compact approximants are first truncated at zero,
then uniformly smoothed and raised by the approximation error.

The approximating functions need not have compact support.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open Filter Set
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] [μ.Regular]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [μ.Regular] in
/-- Nonnegative smooth representatives approximate every nonnegative `Lᵖ`
element for a finite regular measure. -/
theorem exists_nonneg_contDiff_dist_lt (hp : p ≠ ∞)
    (u : Lp ℝ p μ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, 0 ≤ g x) ∧
      ∃ hg : MemLp g p μ, dist (hg.toLp g) u < ε := by
  let C : ℝ := (measureUnivNNReal μ : ℝ) ^ p.toReal⁻¹
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  let δ : ℝ := ε / (8 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (8 * (C + 1)) = ε :=
    div_mul_cancel₀ ε (by positivity)
  obtain ⟨f, hfcs, hfu, hfcont, hfp⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le hp
      (ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε)))
  let fpos : E → ℝ := fun x ↦ max (f x) 0
  have hfposcont : Continuous fpos := hfcont.max continuous_const
  have hfposcs : HasCompactSupport fpos :=
    hfcs.comp_left (g := fun y : ℝ ↦ max y 0) (by simp)
  have hfposp : MemLp fpos p μ := by
    apply hfp.of_le hfposcont.aestronglyMeasurable
    exact Eventually.of_forall fun x ↦ by
      change |max (f x) 0| ≤ |f x|
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hfposu : dist (hfposp.toLp fpos) u ≤ ε / 2 := by
    have hnorm : ‖hfposp.toLp fpos - u‖ ≤ ‖hfp.toLp f - u‖ := by
      apply norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_sub (hfposp.toLp fpos) u,
        Lp.coeFn_sub (hfp.toLp f) u, hfposp.coeFn_toLp, hfp.coeFn_toLp, hu]
        with x hsubpos hsub hfpos hf hx
      rw [hsubpos, hsub, Pi.sub_apply, Pi.sub_apply, hfpos, hf]
      change |max (f x) 0 - u x| ≤ |f x - u x|
      by_cases hfx : 0 ≤ f x
      · rw [max_eq_left hfx]
      · rw [max_eq_right (le_of_not_ge hfx), zero_sub, abs_neg, abs_of_nonneg hx]
        exact (by linarith : u x ≤ -(f x - u x)).trans (neg_le_abs _)
    have hdist : dist (hfp.toLp f) u ≤ ε / 2 := by
      rw [dist_comm, Lp.dist_def]
      have heq : eLpNorm (⇑u - ⇑(hfp.toLp f)) p μ = eLpNorm (⇑u - f) p μ :=
        eLpNorm_congr_ae (EventuallyEq.rfl.sub hfp.coeFn_toLp)
      rw [heq]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfu).trans_eq
        (ENNReal.toReal_ofReal (half_pos hε).le)
    have hdistle : dist (hfposp.toLp fpos) u ≤ dist (hfp.toLp f) u := by
      simpa only [_root_.dist_eq_norm] using hnorm
    exact hdistle.trans hdist
  obtain ⟨h, hhsmooth, hh⟩ :=
    hfposcs.uniformContinuous_of_continuous hfposcont |>.exists_contDiff_dist_le hδ
  let g : E → ℝ := fun x ↦ h x + δ
  have hgcont : Continuous g := hhsmooth.continuous.add continuous_const
  have hg0 (x : E) : 0 ≤ g x := by
    have hbound := (abs_lt.mp (show |h x - fpos x| < δ from hh x)).1
    have hpos : 0 ≤ fpos x := le_max_right _ _
    dsimp only [g]
    linarith
  have hgf (x : E) : ‖g x - fpos x‖ ≤ 2 * δ := by
    have hbound := abs_lt.mp (show |h x - fpos x| < δ from hh x)
    change |h x + δ - fpos x| ≤ 2 * δ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdiff : MemLp (g - fpos) p μ :=
    MemLp.of_bound (hgcont.sub hfposcont).aestronglyMeasurable (2 * δ)
      (Eventually.of_forall hgf)
  have hgp : MemLp g p μ := by
    simpa only [sub_add_cancel] using hdiff.add hfposp
  refine ⟨g, hhsmooth.add contDiff_const, hg0, hgp, ?_⟩
  have hnorm : ‖hgp.toLp g - hfposp.toLp fpos‖ ≤ C * (2 * δ) := by
    apply norm_le_of_ae_bound (by positivity)
    filter_upwards [Lp.coeFn_sub (hgp.toLp g) (hfposp.toLp fpos),
      hgp.coeFn_toLp, hfposp.coeFn_toLp] with x hsub hg hf
    simpa only [hsub, Pi.sub_apply, hg, hf] using hgf x
  have hsmall : C * (2 * δ) + ε / 2 < ε := by nlinarith
  have hdist : dist (hgp.toLp g) (hfposp.toLp fpos) ≤ C * (2 * δ) := by
    simpa only [_root_.dist_eq_norm] using hnorm
  exact (dist_triangle (hgp.toLp g) (hfposp.toLp fpos) u).trans_lt
    ((add_le_add hdist hfposu).trans_lt hsmall)

end MeasureTheory.Lp
