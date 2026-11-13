/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.Bootstrap
public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.Localization
public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.Limit

/-!
# Critical nonlinear bootstrap on backward cones

Quintic-wave nonconcentration supplies uniformly small L⁶ section norms on a late cone tail.
Measurable localization then applies the fixed-measure quartic bootstrap, giving L⁴-time/L¹²-space
membership up to the terminal time.

The linear Strichartz prefix estimate remains an explicit hypothesis. The small L⁶ norms are the
limit (18) of step 3 of the proof of Evans, §12.4, Theorem 3, and the bootstrap is the derivation
of (20) from (18) and (21) in step 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, steps 3-4 of its proof, equations (18),
  (20) and (21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Nonconcentration gives small L6 section norms for the fixed-measure cone field. -/
theorem tendsto_lpNorm_six_movingConeField {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    Tendsto (fun t ↦ lpNorm (fun x ↦ movingConeField u c T (t, x)) 6 volume) (𝓝[<] T) (𝓝 0) := by
  have h := tendsto_integral_quinticSlice_zero_of_wave hT hu c hwave
  have hr := h.rpow_const_nhds_zero (p := (6 : ℝ)⁻¹) (by positivity)
  apply hr.congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  rw [lpNorm_movingConeField ht]
  have hm := memLp_movingConeField hu.continuousOn c ht 6
  rw [movingConeField_section ht,
    memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet] at hm
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  simp [Real.norm_eq_abs, Real.rpow_ofNat, (by decide : Even (6 : ℕ)).pow_abs]

/-- Moving-ball data discharge all nonlinear localization hypotheses of the bootstrap. -/
theorem memLp_four_twelve_cone_of_strichartz {u : ℝ^4 → ℝ} {T s C K M : ℝ}
    (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T) (hC : 0 < C)
    (hK : 0 ≤ K) (hsmall : (K * M) * (2 * C) ^ 4 < C)
    (hM : ∀ t ∈ Ico s T,
      lpNorm (fun x ↦ u (timeSpaceCons t x)) 6 (volume.restrict (Metric.ball c (T - t))) ≤ M)
    (hlinear : ∀ t ∈ Ico s T, lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc
      s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (T - r)))) :
    MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Ico s T)) := by
  have hband : Ico s T ⊆ Ioo 0 T := fun _ ht ↦ ⟨hs.trans_le ht.1, ht.2⟩
  apply (mixed_memLp_movingConeField_iff (u := u) (c := c) hband measurableSet_Ico 12 4).mp
  apply memLp_four_twelve_of_quintic_strichartz_bound hsT
    (measurable_movingConeField hu c) hC hK hsmall
    (fun t ht ↦ memLp_movingConeField hu c (hband ht) 12)
    (fun t ht ↦ memLp_movingConeField hu c (hband ht) 6)
    (fun t ht ↦ by rw [lpNorm_movingConeField (hband ht)]; exact hM t ht)
    (fun t ht ↦ memLp_four_twelve_movingConeField_local hu c hs ht.2)
  intro t ht
  have hsub : Icc s t ⊆ Ioo 0 T := fun _ hr ↦ ⟨hs.trans_le hr.1, hr.2.trans_lt ht.2⟩
  rw [mixed_lpNorm_movingConeField hsub measurableSet_Icc]
  have he : (∫ r in Icc s t, lpNorm (fun x ↦ movingConeField u c T (r, x) ^ 5) 2 volume) =
      ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
        (volume.restrict (Metric.ball c (T - r))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact lpNorm_quintic_movingConeField (hsub hr)
  rw [he]
  exact hlinear t ht

/-- On a sufficiently late cone tail, only the linear estimate remains an input. -/
theorem exists_cone_tail_bootstrap_of_wave {u : ℝ^4 → ℝ} {T C K : ℝ}
    (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hC : 0 < C) (hK : 0 ≤ K) :
    ∃ a ∈ Ioo 0 T, ∀ s ∈ Ico a T,
      (∀ t ∈ Ico s T,
        lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
          (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Icc s t)) ≤
        C + K * ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
          (volume.restrict (Metric.ball c (T - r)))) →
      MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
        (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Ico s T)) := by
  have hlim := tendsto_lpNorm_six_movingConeField hT hu c hwave
  -- Choose the uniform L6 threshold first, then a tail on which it holds.
  have hε : ∃ ε > (0 : ℝ), (K * ε) * (2 * C) ^ 4 < C := by
    have hc : Continuous (fun ε : ℝ ↦ (K * ε) * (2 * C) ^ 4) := by fun_prop
    have hn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (K * ε) * (2 * C) ^ 4 < C := by
      have hc0 : Tendsto (fun ε : ℝ ↦ (K * ε) * (2 * C) ^ 4)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa only [ContinuousAt, mul_zero, zero_mul] using hc.continuousAt (x := 0)
      exact (hc0.eventually (eventually_lt_nhds hC)).filter_mono nhdsWithin_le_nhds
    have hboth : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ (K * ε) * (2 * C) ^ 4 < C :=
      Filter.Eventually.and self_mem_nhdsWithin hn
    exact hboth.exists
  obtain ⟨ε, hεpos, hεsmall⟩ := hε
  have htail : ∀ᶠ t in 𝓝[<] T,
      t ∈ Ioo 0 T ∧ lpNorm (fun x ↦ movingConeField u c T (t, x)) 6 volume < ε :=
    Filter.Eventually.and (Ioo_mem_nhdsLT hT) (hlim.eventually (eventually_lt_nhds hεpos))
  obtain ⟨a, haT, ha⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp htail
  have ha0 : 0 < a := (ha ⟨le_rfl, haT⟩).1.1
  refine ⟨a, ⟨ha0, haT⟩, fun s hs hlinear ↦ ?_⟩
  apply memLp_four_twelve_cone_of_strichartz hu.continuousOn c
    (ha0.trans_le hs.1) hs.2 hC hK hεsmall ?_ hlinear
  intro t ht
  have hat : t ∈ Ico a T := ⟨hs.1.trans ht.1, ht.2⟩
  rw [← lpNorm_movingConeField (ha hat).1]
  exact (ha hat).2.le

end WaveEquation.Critical
