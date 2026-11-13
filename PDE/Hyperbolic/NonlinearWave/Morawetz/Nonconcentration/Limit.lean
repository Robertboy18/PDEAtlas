/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.SliceBound

/-!
# Vanishing quintic slice and cone-energy tails

The integrable cone densities have vanishing integrals on shrinking balls. The quantitative slice
bound therefore rules out sixth-power concentration at the terminal cone vertex, without terminal
regularity or a support hypothesis.

This is the limit (18) that step 3 of the proof of Evans, §12.4, Theorem 3, derives from the
estimate (5) of Theorem 2 and the vanishing of the flux `φ(s)` as `s → T`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Notation, Theorem 2, equation (5), and Theorem 3,
  step 3 of its proof, equation (18).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

private theorem tendsto_integral_shrinking_ball {n : ℕ} [Nontrivial (ℝ^n)] {f : ℝ^n → ℝ} {c : ℝ^n}
    {r T : ℝ} (hr : 0 < r) (hf : IntegrableOn f (Metric.ball c r)) :
    Tendsto (fun t ↦ ∫ x in Metric.ball c (T - t), f x) (𝓝[<] T) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Metric.ball c r)) (l := 𝓝[<] T)
    (f := fun _ ↦ (0 : ℝ)) (F := fun t ↦ (Metric.ball c (T - t)).indicator f) (fun x ↦ ‖f x‖)
    (Eventually.of_forall fun t ↦ hf.aestronglyMeasurable.indicator measurableSet_ball)
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self f x)
    hf.norm ?_
  · have he : ∀ᶠ t in 𝓝[<] T, T - r < t :=
      (eventually_gt_nhds (sub_lt_self T hr)).filter_mono nhdsWithin_le_nhds
    simp only [integral_zero] at h
    apply h.congr'
    filter_upwards [he] with t ht
    rw [integral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (Metric.ball_subset_ball (by linarith : T - t ≤ r))]
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne c)] with x hx
    have hpos : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have he : ∀ᶠ t in 𝓝[<] T, T - ‖x - c‖ < t :=
      (eventually_gt_nhds (sub_lt_self T hpos)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with t ht using (indicator_of_notMem (by
      change ¬ dist x c < T - t
      rw [dist_eq_norm]
      linarith) f).symm

private theorem tendsto_cone_densities_zero_of_wave {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    Tendsto (fun s ↦ ∫ x in Metric.ball c (T - s), ‖coneProfileGradient T c u x‖ ^ 2) (𝓝[<] T)
      (𝓝 0) ∧
      Tendsto (fun s ↦ ∫ x in Metric.ball c (T - s), coneProfile T c u x ^ 6) (𝓝[<] T) (𝓝 0) := by
  obtain ⟨hG, hW⟩ := ConeProfile.integrable_densities_of_wave hu c (half_pos hT)
    (fun t (ht : t ∈ Ico (T / 2) T) ↦ hwave t ⟨(half_pos hT).trans_le ht.1, ht.2⟩)
  exact ⟨tendsto_integral_shrinking_ball (sub_pos.mpr (half_lt_self hT)) hG,
    tendsto_integral_shrinking_ball (sub_pos.mpr (half_lt_self hT)) hW⟩

/-- The normalized lateral energy remaining above a time slice tends to zero.
The two cone densities are supplied by local conservation and the area formula. -/
theorem tendsto_integral_quinticConeEnergy_zero_of_wave {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    Tendsto (fun s ↦ ∫ x in Metric.ball c (T - s), (1 / 2 : ℝ) * ‖coneProfileGradient T c u x‖ ^ 2 +
      coneProfile T c u x ^ 6 / 6) (𝓝[<] T) (𝓝 0) := by
  obtain ⟨hG, hW⟩ := ConeProfile.integrable_densities_of_wave hu c (half_pos hT)
    (fun t (ht : t ∈ Ico (T / 2) T) ↦ hwave t ⟨(half_pos hT).trans_le ht.1, ht.2⟩)
  exact tendsto_integral_shrinking_ball (sub_pos.mpr (half_lt_self hT))
    ((hG.const_mul (1 / 2 : ℝ)).add (hW.div_const 6))

/-- A classical quintic wave on the open forward band has no sixth-power
concentration in a backward cone at its terminal time. -/
theorem tendsto_integral_quinticSlice_zero_of_wave {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    Tendsto (fun s ↦ ∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) (𝓝[<] T) (𝓝 0) := by
  obtain ⟨hG, hW⟩ := tendsto_cone_densities_zero_of_wave hT hu c hwave
  have hroot := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).tendsto 0 |>.comp hW
  rw [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] at hroot
  have hupper := (hG.const_mul 12).add (hroot.const_mul
    (12 * (∫ x in Metric.ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ)))
  simp only [mul_zero, add_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun s ↦ integral_nonneg fun x ↦ by positivity) ?_ hupper
  have he : ∀ᶠ s in 𝓝[<] T, 0 < s := (eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, self_mem_nhdsWithin] with s hs hsT
  exact integral_quinticSlice_le_coneDensities_of_wave hu c hs hsT hwave

end WaveEquation
