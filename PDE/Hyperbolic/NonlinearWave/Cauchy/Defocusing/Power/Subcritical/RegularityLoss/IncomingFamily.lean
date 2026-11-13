/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.WeakCoupling.FamilyData
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Data
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Incoming.Data
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Matching
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Quadratic waves from a smooth incoming family

Weak coupling constructs coefficient-one waves from the same smooth compact family. Narrow-cone
uniqueness preserves exact zeros and the positive transverse derivative.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped ContDiff Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

/-- One jointly smooth compact Goursat-data family feeds the coefficient-one
signed quadratic wave theorem. The same family has exact branch Cauchy traces
and normalized full first-jet convergence. -/
theorem exists_smooth_incoming_quadratic_goursat_wave_family :
    ∃ W : Parameter → ℝ, ContDiff ℝ ∞ W ∧
      ∃ σ : ℝ, 0 < σ ∧ ∃ g h : ℝ → ℝ^3 → ℝ,
        ContDiff ℝ ∞ (Function.uncurry g) ∧ ContDiff ℝ ∞ (Function.uncurry h) ∧
        g 0 = incomingDisplacement ∧ h 0 = incomingVelocity ∧
        (∃ K : Set (ℝ^3), IsCompact K ∧
          ∀ κ : ℝ, ∀ x ∉ K, g κ x = 0 ∧ h κ x = 0) ∧
        (∀ κ : ℝ, ∀ x : ℝ^3, |‖x‖ - 1| < σ →
          κ ^ 2 * g κ x = W (‖x‖ - 1, 1 - ‖x‖, κ ^ 2) / ‖x‖ ∧
          HasDerivAt (fun t : ℝ ↦
            W (t + ‖x‖ - 1, t - ‖x‖ + 1, κ ^ 2) / ‖x‖) (κ ^ 2 * h κ x) 0) ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∃ v : ℝ → (ℝ × ℝ^3) → ℝ,
          (∀ κ : ℝ, |κ| < d →
            ContDiffOn ℝ 1 (fun p ↦ κ ^ 2 * v κ p) {p | |p.1| < 3} ∧
            (∀ x : ℝ^3, κ ^ 2 * v κ (0, x) = κ ^ 2 * g κ x) ∧
            (∀ x : ℝ^3, HasDerivAt (fun t ↦ κ ^ 2 * v κ (t, x))
              (κ ^ 2 * h κ x) 0) ∧
            (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 2 →
              κ ^ 2 * v κ p =
                cauchyFreeField (fun x ↦ κ ^ 2 * g κ x) (fun x ↦ κ ^ 2 * h κ x) p +
                  oddDuhamelSolution 0
                    (fun z : ℝ^4 ↦ -Real.signedPower 2
                      (κ ^ 2 * v κ (timeSpaceContinuousLinearEquiv 3 z)))
                    (timeSpaceCons p.1 p.2)) ∧
            ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 2,
              HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, κ ^ 2 * v κ (s, x) * φ x))
                ((∫ x : ℝ^3, κ ^ 2 * v κ (t, x) * laplacian φ x) -
                  ∫ x : ℝ^3, Real.signedPower 2 (κ ^ 2 * v κ (t, x)) * φ x) t) ∧
          (∀ κ : ℝ, 0 < κ → κ < d →
            ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ T ∈ Ioo 0 δ, ∀ x : ℝ^3, T + ‖x‖ = 1 →
              κ ^ 2 * v κ (T, x) = 0 ∧
              fderiv ℝ (fun p ↦ κ ^ 2 * v κ p) (T, x) (T, x) = κ ^ 2 / ‖x‖) ∧
          TendstoLocallyUniformly v (cauchyFreeField incomingDisplacement incomingVelocity) (𝓝 0) ∧
          TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p)
            (fderiv ℝ (cauchyFreeField incomingDisplacement incomingVelocity)) (𝓝 0) := by
  obtain ⟨a, ha, W, hW, c, hc, hpoly, hrad, η, hη, _, Z, hZ, hnorm⟩ :=
    exists_smooth_normalized_radial_polynomial_goursat
  let σ := min (η / 2) (1 / 4)
  have hσ : 0 < σ := lt_min (half_pos hη) (by norm_num)
  have hσsmall : σ ≤ 1 / 4 := min_le_right _ _
  have hση : σ < η := (min_le_left _ _).trans_lt (half_lt_self hη)
  have hbdata (x : ℝ^3) (hx : |‖x‖ - 1| < σ) :
      incomingDisplacement x = (‖x‖ - 1) / ‖x‖ ∧ incomingVelocity x = 1 / ‖x‖ :=
    incoming_data_on_annulus (hx.trans_le hσsmall)
  obtain ⟨G, H, hG, hH, hG0, hH0, K, hK, hs, hdata⟩ :=
    exists_smooth_compact_goursat_data_with_baseline hZ hσsmall hση
      (fun a b ha hb ↦ (hnorm a b ha hb).1)
      (fun a b ha hb ↦ (hnorm a b ha hb).2) contDiff_infty_incomingDisplacement
      contDiff_infty_incomingVelocity hasCompactSupport_incoming_data.1
      hasCompactSupport_incoming_data.2 hbdata
  let g : ℝ → ℝ^3 → ℝ := fun κ ↦ G (κ ^ 2)
  let h : ℝ → ℝ^3 → ℝ := fun κ ↦ H (κ ^ 2)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := hG.comp ((contDiff_fst.pow 2).prodMk contDiff_snd)
  have hh : ContDiff ℝ ∞ (Function.uncurry h) := hH.comp ((contDiff_fst.pow 2).prodMk contDiff_snd)
  have hgs : ∀ κ : ℝ, |κ| ≤ 1 → ∀ x ∉ K, g κ x = 0 := fun κ _ x hx ↦ (hs (κ ^ 2) x hx).1
  have hhs : ∀ κ : ℝ, |κ| ≤ 1 → ∀ x ∉ K, h κ x = 0 := fun κ _ x hx ↦ (hs (κ ^ 2) x hx).2
  obtain ⟨d₀, hd₀, _, v, _, hactual, hlim, hdlim⟩ :=
    exists_smallAmplitude_tested_trajectory_of_compact_family
      (r := 2) (S := 2) (by norm_num) (by norm_num)
      (hg.of_le (by simp)) (hh.of_le (by simp)) hK hgs hhs
  have hg0 : g 0 = incomingDisplacement := by
    simpa only [g, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hG0
  have hh0 : h 0 = incomingVelocity := by
    simpa only [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hH0
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, inv_one, Real.rpow_one,
    show (2 : ℝ) + 1 = 3 by norm_num] at hactual
  rw [hg0, hh0] at hlim hdlim
  let d := min d₀ (min 1 a)
  have hd : 0 < d := lt_min hd₀ (lt_min zero_lt_one ha)
  have hdd₀ : d ≤ d₀ := min_le_left _ _
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hda : d ≤ a := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨W, hW, σ, hσ, g, h, hg, hh, hg0, hh0, ⟨K, hK, fun κ ↦ hs (κ ^ 2)⟩,
    fun κ ↦ hdata (κ ^ 2), d, hd, hd1, v,
    (fun κ hκ ↦ hactual κ (hκ.trans_le hdd₀)), ?_, hlim, hdlim⟩
  intro κ hκpos hκd
  have hκd₀ : |κ| < d₀ := by rw [abs_of_pos hκpos]; exact hκd.trans_le hdd₀
  have hκsmall : κ < 1 := hκd.trans_le hd1
  have hεpos : 0 < κ ^ 2 := sq_pos_of_pos hκpos
  have hεa : κ ^ 2 < a := by nlinarith [hκd.trans_le hda]
  obtain ⟨η₁, hη₁, hzero, hbranch⟩ := exists_signed_quadratic_goursat_branch_of_amplitude
      (hW.of_le (by simp)) (hc.of_le (by simp)) hpoly hrad hεpos hεa
  have hact := hactual κ hκd₀
  have hu : ContDiffOn ℝ 1 (fun p ↦ κ ^ 2 * v κ p) {p | |p.1| < 2} :=
    hact.1.mono (fun p hp ↦ lt_trans (show |p.1| < 2 from hp) (by norm_num))
  have hcg : ContDiff ℝ 3 (fun x ↦ κ ^ 2 * g κ x) :=
    contDiff_const.mul ((hg.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id))
  have hch : ContDiff ℝ 2 (fun x ↦ κ ^ 2 * h κ x) :=
    contDiff_const.mul ((hh.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id))
  obtain ⟨δ, hδ, hδquarter, hδtwo, htrace⟩ := exists_pos_local_goursat_nodal_trace
    (hW.of_le (by norm_num)) hη₁ hσ (by norm_num : (0 : ℝ) < 2) hzero
    (fun a ha b hb ↦ (hbranch a ha b hb).2.2) hcg hch (hdata (κ ^ 2)) hu
    (fun p hp ↦ hact.2.2.2.1 p ⟨hp.1, hp.2.le⟩)
  refine ⟨δ, hδ, hδquarter, fun T hT x hx ↦ ?_⟩
  refine ⟨(htrace T hT x hx).1, ?_⟩
  have hut : DifferentiableAt ℝ (fun p ↦ κ ^ 2 * v κ p) (T, x) :=
    (hu.contDiffAt ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds
      (by change |T| < 2; rw [abs_of_pos hT.1]; exact hT.2.trans hδtwo))).differentiableAt
        one_ne_zero
  exact fderiv_cone_direction_of_zero_characteristic (by linarith) hT hx hut
    (fun s hs y hy ↦ (htrace s hs y hy).1) (htrace T hT x hx).2

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

end
