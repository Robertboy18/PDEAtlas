/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SignedPower
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Equation
import CAS.ExactTactic

/-!
# An exact signed-quadratic characteristic branch

The characteristic zero and transverse derivative determine a negative branch at each
sufficiently small positive amplitude.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The incoming characteristic retains the prescribed transverse derivative. -/
theorem hasDerivAt_polynomial_goursat_zero_characteristic {c : ℝ → ℝ} {W : Parameter → ℝ}
    {δ b ε : ℝ} (hc : ContDiff ℝ 1 c) (hW : ContDiff ℝ 1 W)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2)
    (hp : ((0 : ℝ), b, ε) ∈ Metric.ball 0 δ) :
    HasDerivAt (fun s : ℝ ↦ W (s, b, ε)) ε 0 := by
  have hint : (∫ t in (0 : ℝ)..b, c (0 - t) * W (0, t, ε) ^ 2) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..b, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht ↦ ?_
        have ht' : |t| ≤ |b| := by
          simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
        have hmem : ((0 : ℝ), t, ε) ∈ Metric.ball 0 δ := by
          rw [Metric.mem_ball, dist_zero_right] at hp ⊢
          apply lt_of_le_of_lt _ hp
          simp only [Prod.norm_def, Real.norm_eq_abs]
          exact max_le_max le_rfl (max_le_max ht' le_rfl)
        change c (0 - t) * W (0, t, ε) ^ 2 = 0
        rw [polynomial_goursat_zero_characteristic heq hmem]
        simp
      _ = 0 := by simp
  simpa only [hint, add_zero] using hasDerivAt_polynomial_goursat_first hc hW heq hp

/-- The coordinate derivative is the corresponding evaluation of the full derivative. -/
theorem deriv_polynomial_goursat_first_eq_fderiv {W : Parameter → ℝ} (hW : ContDiff ℝ 1 W)
    (a b ε : ℝ) :
    deriv (fun s : ℝ ↦ W (s, b, ε)) a = fderiv ℝ W (a, b, ε) (1, 0, 0) := by
  have hpath : HasDerivAt (fun s : ℝ ↦ (s, b, ε)) (1, 0, 0) a :=
    (hasDerivAt_id a).prodMk ((hasDerivAt_const a b).prodMk (hasDerivAt_const a ε))
  exact ((hW.differentiable one_ne_zero (a, b, ε)).hasFDerivAt.comp_hasDerivAt a hpath).deriv

/-- Positive incoming slope forces a negative field on the adjacent negative side. -/
theorem polynomial_goursat_neg_of_first_neg {c : ℝ → ℝ} {W : Parameter → ℝ} {δ ε : ℝ}
    (hc : ContDiff ℝ 1 c) (hW : ContDiff ℝ 1 W)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2)
    (hε : 0 < ε) (hεδ : ε < δ) :
    ∃ η : ℝ, 0 < η ∧ η < δ ∧ ∀ a ∈ Ioo (-η) 0, ∀ b ∈ Ioo (-η) η, W (a, b, ε) < 0 := by
  have hp : ((0 : ℝ), (0 : ℝ), ε) ∈ Metric.ball 0 δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, norm_zero,
      Real.norm_eq_abs, abs_of_pos hε, max_eq_right hε.le] using hεδ
  have hA : Continuous (fun p : Parameter ↦ fderiv ℝ W p (1, 0, 0)) :=
    (hW.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hA0 : fderiv ℝ W (0, 0, ε) (1, 0, 0) = ε := by
    rw [← deriv_polynomial_goursat_first_eq_fderiv hW]
    exact (hasDerivAt_polynomial_goursat_zero_characteristic hc hW heq hp).deriv
  have hnear : ∀ᶠ p : Parameter in 𝓝 (0, 0, ε),
      p ∈ Metric.ball 0 δ ∧ 0 < fderiv ℝ W p (1, 0, 0) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp,
      hA.continuousAt.eventually (Ioi_mem_nhds (hA0 ▸ hε))] with p hmem hpos
    exact ⟨hmem, hpos⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let η := min r δ / 2
  have hδ : 0 < δ := hε.trans hεδ
  have hη : 0 < η := half_pos (lt_min hr hδ)
  have hηr : η < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left _ _)
  have hηδ : η < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right _ _)
  have hmem (a b : ℝ) (ha : a ∈ Ioo (-η) η) (hb : b ∈ Ioo (-η) η) :
      (a, b, ε) ∈ Metric.ball (0, 0, ε) r := by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, dist_self, max_lt_iff,
      max_lt_iff, dist_zero_right, dist_zero_right]
    exact ⟨(abs_lt.mpr ha).trans hηr, (abs_lt.mpr hb).trans hηr, hr⟩
  refine ⟨η, hη, hηδ, fun a ha b hb ↦ ?_⟩
  have hmono : StrictMonoOn (fun s : ℝ ↦ W (s, b, ε)) (Ioo (-η) η) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (hW.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    intro s hs
    rw [interior_Ioo] at hs
    change 0 < deriv (fun a : ℝ ↦ W (a, b, ε)) s
    rw [deriv_polynomial_goursat_first_eq_fderiv hW]
    exact (hball (hmem s b hs hb)).2
  have hzero : (0 : ℝ) ∈ Ioo (-η) η := ⟨neg_neg_of_pos hη, hη⟩
  have hlt := hmono ⟨ha.1, ha.2.trans hη⟩ hzero ha.2
  change W (a, b, ε) < W (0, b, ε) at hlt
  rw [polynomial_goursat_zero_characteristic heq (hball (hmem 0 b hzero hb)).1] at hlt
  exact hlt

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter MeasureTheory
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- Each positive amplitude in the construction ball has an exact signed quadratic
branch, with the same Goursat field and its prescribed transverse derivative. -/
theorem exists_signed_quadratic_goursat_branch_of_amplitude {δ ε : ℝ} {W : Parameter → ℝ}
    {c : ℝ → ℝ} (hW : ContDiff ℝ 5 W) (hc : ContDiff ℝ 5 c)
    (heq : ∀ p : Parameter, p ∈ Metric.ball 0 δ → W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1,
      ∫ t in (0 : ℝ)..p.2.1, c (s - t) * W (s, t, p.2.2) ^ 2)
    (hrad : ∀ p : Parameter, p ∈ Metric.ball 0 δ → 0 < 1 + (p.1 - p.2.1) / 2 ∧ c (p.1 - p.2.1) =
      1 / (4 * (1 + (p.1 - p.2.1) / 2)))
    (hε : 0 < ε) (hεδ : ε < δ) :
    ∃ η : ℝ, 0 < η ∧
      (∀ b ∈ Ioo (-η) η, W (0, b, ε) = 0 ∧
        HasDerivAt (fun a : ℝ ↦ W (a, b, ε)) ε 0) ∧
      (∀ a ∈ Ioo (-η) 0, ∀ b ∈ Ioo (-η) η,
        W (a, b, ε) < 0 ∧ 0 < 1 + (a - b) / 2 ∧
        HasDerivAt (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a)
          (-Real.signedPower 2 (W (a, b, ε)) / (4 * (1 + (a - b) / 2))) b) := by
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by norm_num)
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  obtain ⟨η, hη, hηδ, hneg⟩ := polynomial_goursat_neg_of_first_neg hc1 hW1 heq hε hεδ
  have hmem (a b : ℝ) (ha : |a| < η) (hb : |b| < η) :
      (a, b, ε) ∈ Metric.ball 0 δ := by
    simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff,
      Real.norm_eq_abs, abs_of_pos hε]
    exact ⟨ha.trans hηδ, hb.trans hηδ, hεδ⟩
  refine ⟨η, hη, ?_, ?_⟩
  · intro b hb
    have hp := hmem 0 b (by simpa using hη) (abs_lt.mpr hb)
    exact ⟨polynomial_goursat_zero_characteristic heq hp,
      hasDerivAt_polynomial_goursat_zero_characteristic hc1 hW1 heq hp⟩
  · intro a ha b hb
    have hwa := hneg a ha b hb
    have hp := hmem a b (abs_lt.mpr ⟨ha.1, ha.2.trans hη⟩) (abs_lt.mpr hb)
    refine ⟨hwa, (hrad _ hp).1, ?_⟩
    convert hasDerivAt_polynomial_goursat_mixed hc1 hW1 heq hp using 1
    rw [(hrad _ hp).2, Real.signedPower, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, abs_of_neg hwa]
    generalize W (a, b, ε) = z
    cas

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
