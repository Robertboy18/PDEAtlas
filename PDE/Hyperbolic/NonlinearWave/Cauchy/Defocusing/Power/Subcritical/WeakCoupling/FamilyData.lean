/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.WeakCoupling.Data

/-!
# Small-amplitude waves with varying compact profiles

Joint regularity and a common compact spatial support give the regularity and
uniform bound needed by weak coupling. The resulting coefficient-one signed-power
waves have both ordinary Cauchy traces and the tested PDE. Their normalized first
jets converge to the free wave of the parameter-zero profiles.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE.Analysis PDE.Common WaveEquation
open scoped Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A common compact support and joint C³/C² regularity construct the
amplitude-scaled signed-power family. The normalized full first jet converges
to the free field of the parameter-zero profiles. -/
theorem exists_smallAmplitude_tested_trajectory_of_compact_family {r S : ℝ} (hr : 1 < r)
    (hS : 0 < S) {g h : ℝ → ℝ^3 → ℝ} (hg : ContDiff ℝ 3 (Function.uncurry g))
    (hh : ContDiff ℝ 2 (Function.uncurry h)) {K : Set (ℝ^3)} (hK : IsCompact K)
    (hgs : ∀ κ : ℝ, |κ| ≤ 1 → ∀ x ∉ K, g κ x = 0) (hhs : ∀ κ : ℝ, |κ| ≤ 1 → ∀ x ∉ K, h κ x = 0) :
    let ε : ℝ → ℝ := fun κ ↦ (κ ^ 2) ^ (r - 1)⁻¹
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ v : ℝ → (ℝ × ℝ^3) → ℝ,
      ContDiffOn ℝ 1 (Function.uncurry v) {z | |z.1| < δ ∧ |z.2.1| < S + 1} ∧
      (∀ κ : ℝ, |κ| < δ →
        ContDiffOn ℝ 1 (fun p ↦ ε κ * v κ p) {p | |p.1| < S + 1} ∧
        (∀ x : ℝ^3, ε κ * v κ (0, x) = ε κ * g κ x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ ε κ * v κ (t, x)) (ε κ * h κ x) 0) ∧
        (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S →
          ε κ * v κ p = cauchyFreeField (fun x ↦ ε κ * g κ x) (fun x ↦ ε κ * h κ x) p +
            oddDuhamelSolution 0
              (fun z : ℝ^4 ↦ -Real.signedPower r
                (ε κ * v κ (timeSpaceContinuousLinearEquiv 3 z)))
              (timeSpaceCons p.1 p.2)) ∧
        ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 S,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, ε κ * v κ (s, x) * φ x))
            ((∫ x : ℝ^3, ε κ * v κ (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (ε κ * v κ (t, x)) * φ x) t) ∧
      TendstoLocallyUniformly v (cauchyFreeField (g 0) (h 0)) (𝓝 0) ∧
      TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p)
        (fderiv ℝ (cauchyFreeField (g 0) (h 0))) (𝓝 0) := by
  intro ε
  have hg2 : ContDiff ℝ 2 (Function.uncurry g) := hg.of_le (by norm_num)
  have hh1 : ContDiff ℝ 1 (Function.uncurry h) := hh.of_le (by norm_num)
  have hH := contDiff_cauchyFreeField_family (k := 1) hg2 hh1
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ^3)
  have hzero (f : ℝ → ℝ^3 → ℝ) (hf : ∀ κ : ℝ, |κ| ≤ 1 → ∀ x ∉ K, f κ x = 0)
      (κ : ℝ) (hκ : κ ∈ Icc (-1) 1) (x : ℝ^3) (hx : R < ‖x‖) : f κ x = 0 := by
    refine hf κ (abs_le.mpr hκ) x fun hxK ↦ ?_
    have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hxK
    exact hx.not_ge hn
  obtain ⟨B, hB, hbound⟩ := exists_bound_cauchyFreeField_family_of_common_support
    (g := Function.uncurry g) (h := Function.uncurry h) hg2 hh1 isCompact_Icc
    (hzero g hgs) (hzero h hhs) S
  obtain ⟨δ, hδ, v, hv, hactual, hlim, hdlim⟩ :=
    exists_smallAmplitude_tested_trajectory_of_bounded_free_family hr hS (g := g) (h := h)
      (fun κ ↦ hg.comp (contDiff_const.prodMk contDiff_id))
      (fun κ ↦ hh.comp (contDiff_const.prodMk contDiff_id)) hH hB
      (fun κ hκ p hp ↦ hbound κ (abs_le.mp hκ) p hp)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, v, ?_, ?_, hlim, hdlim⟩
  · exact hv.mono (fun z hz ↦ ⟨hz.1.trans_le (min_le_left _ _), hz.2⟩)
  · exact fun κ hκ ↦ hactual κ (hκ.trans_le (min_le_left _ _))

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
