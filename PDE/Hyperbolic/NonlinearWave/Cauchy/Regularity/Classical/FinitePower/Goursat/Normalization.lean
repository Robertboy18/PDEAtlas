/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Construction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Linearization
import CAS.ExactTactic

/-!
# Smooth normalization of a Goursat family

Divided slopes extend amplitude division smoothly at zero. The same radial family retains its
exact normalization and zero-time derivative traces.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE.Analysis
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The zero-amplitude normalized field has unit time velocity after the
characteristic change of variables, throughout its linear rectangle. -/
theorem hasDerivAt_normalized_goursat_zero_time {Z : Parameter → ℝ} {η a b : ℝ}
    (hzero : ∀ s t : ℝ, |s| < η → |t| < η → Z (s, t, 0) = s) (ha : |a| < η) (hb : |b| < η) :
    HasDerivAt (fun t : ℝ ↦ Z (t + a, t + b, 0)) 1 0 := by
  have hd : HasDerivAt (fun t : ℝ ↦ t + a) 1 0 := by cas
  apply hd.congr_of_eventuallyEq
  have hca : Continuous (fun t : ℝ ↦ |t + a|) := (continuous_id.add continuous_const).abs
  have hcb : Continuous (fun t : ℝ ↦ |t + b|) := (continuous_id.add continuous_const).abs
  filter_upwards [hca.continuousAt.eventually (gt_mem_nhds (by simpa using ha)),
    hcb.continuousAt.eventually (gt_mem_nhds (by simpa using hb))] with t hta htb
  exact hzero (t + a) (t + b) hta htb

/-- The full characteristic derivative in the time direction is one on
the zero-amplitude slice. -/
theorem normalized_goursat_zero_time_fderiv {Z : Parameter → ℝ} (hZ : ContDiff ℝ 1 Z) {η a b : ℝ}
    (hzero : ∀ s t : ℝ, |s| < η → |t| < η → Z (s, t, 0) = s) (ha : |a| < η) (hb : |b| < η) :
    fderiv ℝ Z (a, b, 0) (1, 1, 0) = 1 := by
  have hpath : HasDerivAt (fun t : ℝ ↦ (t + a, t + b, (0 : ℝ))) (1, 1, 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).add_const a).prodMk
      (((hasDerivAt_id (0 : ℝ)).add_const b).prodMk (hasDerivAt_const (0 : ℝ) 0))
  have hd' : HasDerivAt (fun t : ℝ ↦ Z (t + a, t + b, 0))
      (fderiv ℝ Z (a, b, 0) (1, 1, 0)) 0 := by
    simpa only [Function.comp_def, zero_add] using
      ((hZ.differentiable one_ne_zero) (0 + a, 0 + b, 0)).hasFDerivAt
        |>.comp_hasDerivAt (0 : ℝ) hpath
  exact hd'.unique (hasDerivAt_normalized_goursat_zero_time hzero ha hb)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter MeasureTheory PDE.Analysis
open scoped Topology ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- One smooth coefficient agrees with the radial reciprocal near zero. -/
theorem exists_smooth_radial_goursat_coefficient :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧ ∃ η : ℝ, 0 < η ∧ ∀ z, |z| < η → c z = 1 / (4 * (1 + z / 2)) := by
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ 1 / (4 * (1 + z / 2))) (Ioo (-1) 1) :=
    fun z hz ↦ (contDiffAt_const.div
      (contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_id.div_const 2)))
      (by have hpos : 0 < 4 * (1 + z / 2) := by linarith [hz.1]
          exact hpos.ne')).contDiffWithinAt
  obtain ⟨c, hreg, _, heq⟩ :=
    hc.exists_contDiff_compactSupport_eventuallyEq_finiteDimensional isOpen_Ioo
      (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  obtain ⟨η, hη, hηeq⟩ := Metric.mem_nhds_iff.mp heq
  refine ⟨c, hreg, η, hη, fun z hz ↦ ?_⟩
  exact (hηeq (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz)).symm

/-- One smooth local field solves the radial polynomial Goursat problem. -/
theorem exists_smooth_radial_polynomial_goursat :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : Parameter → ℝ, ContDiff ℝ ∞ W ∧
      ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧
      (∀ (p : Parameter), p ∈ Metric.ball 0 δ →
        W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
          c (s - t) * W (s, t, p.2.2) ^ 2) ∧
      (∀ (p : Parameter), p ∈ Metric.ball 0 δ →
        0 < 1 + (p.1 - p.2.1) / 2 ∧ c (p.1 - p.2.1) =
          1 / (4 * (1 + (p.1 - p.2.1) / 2))) := by
  obtain ⟨c, hc, η, hη, hceq⟩ := exists_smooth_radial_goursat_coefficient
  obtain ⟨δ, hδ, W, hW, heq⟩ := exists_smooth_polynomial_goursat_equation hc
  let r := min δ (min (η / 4) (1 / 4))
  have hr : 0 < r := lt_min hδ (lt_min (by positivity) (by norm_num))
  have hrδ : r ≤ δ := min_le_left _ _
  have hrη : r ≤ η / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr, W, hW, c, hc, ?_, ?_⟩
  · exact fun p hp ↦ heq p (Metric.ball_subset_ball hrδ hp)
  · intro p hp
    have hnorm : ‖p‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hp
    have ha : |p.1| < r := (norm_fst_le p).trans_lt hnorm
    have hb : |p.2.1| < r := ((norm_fst_le p.2).trans (norm_snd_le p)).trans_lt hnorm
    have hab : |p.1 - p.2.1| < 2 * r := (abs_sub _ _).trans_lt (by linarith)
    have hpos : 0 < 1 + (p.1 - p.2.1) / 2 := by
      have hlow := (abs_lt.mp hab).1
      linarith
    exact ⟨hpos, hceq _ (hab.trans_le (by linarith))⟩

/-- The same divided-slope normalization is jointly smooth through amplitude zero. -/
theorem contDiff_infty_goursat_amplitude_dslope {W : Parameter → ℝ} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun p : Parameter ↦ dslope (fun ε : ℝ ↦ W (p.1, p.2.1, ε)) 0 p.2.2) := by
  have hF : ContDiff ℝ ((∞ : ℕ∞ω) + 1)
      (fun q : (ℝ × ℝ) × ℝ ↦ W (q.1.1, q.1.2, q.2)) := by
    simpa [Function.comp_def] using hW.comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have h := contDiff_dslope_snd (n := (⊤ : ℕ∞)) hF 0
  exact h.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)

/-- A polynomial Goursat field admits a globally smooth normalization whose
zero-amplitude profile is linear on a fixed characteristic rectangle. -/
theorem exists_smooth_normalized_polynomial_goursat {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    {W : Parameter → ℝ} (hW : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∃ Z : Parameter → ℝ, ContDiff ℝ ∞ Z ∧
      ∀ a b : ℝ, |a| < η → |b| < η → Z (a, b, 0) = a ∧ ∀ ε : ℝ, ε * Z (a, b, ε) = W (a, b, ε) := by
  obtain ⟨η, hη, hηδ, hzero⟩ :=
    exists_pos_polynomial_goursat_zero_amplitude (k := 0) (hc.of_le (by simp)) hW.continuous hδ heq
  let Z : Parameter → ℝ := fun p ↦ dslope (fun ε : ℝ ↦ W (p.1, p.2.1, ε)) 0 p.2.2
  refine ⟨η, hη, hηδ, Z, contDiff_infty_goursat_amplitude_dslope hW, fun a b ha hb ↦ ?_⟩
  constructor
  · change dslope (fun ε : ℝ ↦ W (a, b, ε)) 0 0 = a
    rw [dslope_same]
    exact (hasDerivAt_polynomial_goursat_amplitude_zero
      (hc.of_le (by norm_num)) (hW.of_le (by norm_num)) hδ hηδ heq hzero ha hb).deriv
  · intro ε
    simpa only [Z, sub_zero, smul_eq_mul, hzero a b ha hb] using
      sub_smul_dslope (fun e : ℝ ↦ W (a, b, e)) 0 ε

/-- The radial polynomial construction has a global normalized family
with the exact free linearization. -/
theorem exists_smooth_normalized_radial_polynomial_goursat :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : Parameter → ℝ, ContDiff ℝ ∞ W ∧
      ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧
      (∀ (p : Parameter), p ∈ Metric.ball 0 δ →
        W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
          c (s - t) * W (s, t, p.2.2) ^ 2) ∧
      (∀ (p : Parameter), p ∈ Metric.ball 0 δ →
        0 < 1 + (p.1 - p.2.1) / 2 ∧ c (p.1 - p.2.1) =
          1 / (4 * (1 + (p.1 - p.2.1) / 2))) ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∃ Z : Parameter → ℝ, ContDiff ℝ ∞ Z ∧
        ∀ a b : ℝ, |a| < η → |b| < η →
          Z (a, b, 0) = a ∧ ∀ ε : ℝ, ε * Z (a, b, ε) = W (a, b, ε) := by
  obtain ⟨δ, hδ, W, hW, c, hc, heq, hrad⟩ := exists_smooth_radial_polynomial_goursat
  exact ⟨δ, hδ, W, hW, c, hc, heq, hrad, exists_smooth_normalized_polynomial_goursat hc hW hδ heq⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
