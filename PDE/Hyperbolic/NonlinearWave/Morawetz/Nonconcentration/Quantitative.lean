/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.EnergyBound
public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.Flux
import PDE.Analysis.Calculus.LocalExtension.HalfSpace
import PDE.Hyperbolic.Classical.ForwardLocalization
import CAS.ExactTactic

/-!
# Quantitative quintic nonconcentration from initial cone energy

The cone flux is bounded by the initial cap energy. Absorbing its linear term yields the
one-third-power estimate, uniformly in the time slice. Continuity and dominated convergence include
the initial slice without any regularity at the terminal vertex. The upper-band representative is
removed in `Forward`.

This proves the estimate (5) of Evans, §12.4, Theorem 2, for solutions that are C² only below the
terminal time. The last line of (15) bounds the slice integral by a linear and a one-third-power
term in the flux, and Evans passes directly to (5). We absorb the linear term using the bound of the
flux by the initial cone energy, so our constant depends on that energy.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 2 and its proof, equations (5) and (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis Metric
open scoped Topology

namespace WaveEquation

/-- A bounded nonnegative flux absorbs the linear term in the Morawetz estimate. -/
private theorem morawetz_flux_absorption {φ E K : ℝ} (hφ : 0 ≤ φ) (hbound : φ ≤ E) :
    24 * φ + 12 * K * (6 * φ) ^ (1 / 3 : ℝ) ≤ (24 * E ^ (2 / 3 : ℝ) + 12 * K * (6 : ℝ) ^
      (1 / 3 : ℝ)) * φ ^ (1 / 3 : ℝ) := by
  rcases hφ.eq_or_lt with hzero | hpos
  · subst φ
    norm_num
  have hroot : 0 ≤ φ ^ (1 / 3 : ℝ) := Real.rpow_nonneg hφ _
  have hmono := Real.rpow_le_rpow hφ hbound (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hfactor : φ ^ (2 / 3 : ℝ) * φ ^ (1 / 3 : ℝ) = φ := by
    cas using hpos
  have hlin : φ ≤ E ^ (2 / 3 : ℝ) * φ ^ (1 / 3 : ℝ) := by
    exact hfactor.symm.trans_le (mul_le_mul_of_nonneg_right hmono hroot)
  have hsix : (6 * φ) ^ (1 / 3 : ℝ) =
      (6 : ℝ) ^ (1 / 3 : ℝ) * φ ^ (1 / 3 : ℝ) := by
    cas using hpos
  rw [hsix]
  nlinarith

/-- Continuous forward data have the expected initial shrinking-ball integral. -/
private theorem tendsto_ballIntegral_shrinking_initial {n : ℕ} [Fact (0 < n)] {P : ℝ^(n + 1) → ℝ}
    {T : ℝ} (hT : 0 < T) (hP : ContinuousOn P {p | 0 ≤ p 0 ∧ p 0 < T}) (c : ℝ^n) :
    Tendsto (fun t ↦ ballIntegral n (fun x ↦ P (timeSpaceCons t x)) c (T - t)) (𝓝[>] 0)
      (𝓝 (ballIntegral n (fun x ↦ P (timeSpaceCons 0 x)) c T)) := by
  let q (p : ℝ^(n + 1)) := timeSpaceCons (min (max (p 0) 0) (T / 2)) (spatialPart p)
  have hq : Continuous q := (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
    ((((EuclideanSpace.proj 0).continuous.max continuous_const).min continuous_const).prodMk
      (spatialPartCLM n).continuous)
  have hmap : ∀ p, q p ∈ {p : ℝ^(n + 1) | 0 ≤ p 0 ∧ p 0 < T} := by
    intro p
    change 0 ≤ min (max (p 0) 0) (T / 2) ∧ min (max (p 0) 0) (T / 2) < T
    exact ⟨le_min (le_max_right _ _) (half_pos hT).le,
      (min_le_right _ _).trans_lt (half_lt_self hT)⟩
  have hcont : Continuous (P ∘ q) := hP.comp_continuous hq hmap
  have he (t : ℝ) (ht : t ∈ Icc 0 (T / 2)) (x : ℝ^n) :
      (P ∘ q) (timeSpaceCons t x) = P (timeSpaceCons t x) := by
    simp only [Function.comp_apply, q, timeSpaceCons_zero, spatialPart_timeSpaceCons,
      max_eq_left ht.1, min_eq_left ht.2]
  have hc := (continuousOn_ballIntegral_shrinking hcont c T).continuousAt (Iic_mem_nhds hT)
  have hi := hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hzero : ballIntegral n (fun x ↦ (P ∘ q) (timeSpaceCons 0 x)) c (T - 0) =
      ballIntegral n (fun x ↦ P (timeSpaceCons 0 x)) c T := by
    simp only [he 0 ⟨le_rfl, (half_pos hT).le⟩, sub_zero]
  rw [hzero] at hi
  apply hi.congr'
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < T / 2 :=
    (eventually_lt_nhds (half_pos hT)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hevent, self_mem_nhdsWithin] with t ht htpos
  simp only [he t ⟨htpos.le, ht.le⟩]

/-- The quintic equation extends to the lower face by continuity. -/
private theorem quintic_wave_on_closed_base {v : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hv : ContDiffOn ℝ 2 v {p | p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator v (timeSpaceCons t x) +
      v (timeSpaceCons t x) ^ 5 = 0) :
    ∀ t ∈ Ico 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator v (timeSpaceCons t x) +
      v (timeSpaceCons t x) ^ 5 = 0 := by
  intro t ht x hx
  rcases ht.1.eq_or_lt with he | hpos
  · subst t
    obtain ⟨g, hg, heq⟩ := hv.exists_contDiff_eventuallyEq_on_halfSpace
      (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ) (half_lt_self hT)
    simp only [EuclideanSpace.coe_proj] at heq
    have hx' : 0 < T - dist x c := by
      have := Metric.mem_ball.mp hx
      linarith
    let ε := min (T / 2) (T - dist x c)
    have hε : 0 < ε := lt_min (half_pos hT) hx'
    have hc : Continuous (fun r : ℝ ↦ waveOperator g (timeSpaceCons r x) +
        g (timeSpaceCons r x) ^ 5) :=
      ((continuous_waveOperator_of_contDiff_two hg).add (hg.continuous.pow 5)).comp
        ((contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous.comp
          (continuous_id.prodMk continuous_const))
    have hz : EqOn (fun r : ℝ ↦ waveOperator g (timeSpaceCons r x) +
        g (timeSpaceCons r x) ^ 5) (fun _ ↦ 0) (Ioo 0 ε) := by
      intro r hr
      have hrhalf : r < T / 2 := hr.2.trans_le (min_le_left _ _)
      have hgerm := heq (timeSpaceCons r x) (by simpa using hrhalf.le)
      dsimp only
      rw [← waveOperator_congr_nhds hgerm, ← hgerm.eq_of_nhds]
      exact hwave r ⟨hr.1, hrhalf.trans (half_lt_self hT)⟩ x
        (Metric.mem_ball.mpr (by
          have := hr.2.trans_le (min_le_right _ _)
          linarith))
    have hz0 := hz.closure hc continuous_const
    rw [closure_Ioo hε.ne] at hz0
    have hgerm := heq (timeSpaceCons 0 x) (by simpa using (half_pos hT).le)
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hz0 ⟨le_rfl, hε.le⟩
  · exact hwave t ⟨hpos, ht.2⟩ x hx

/-- Integrable cone densities recover the complete initial ball
as the lower time decreases to zero. -/
private theorem tendsto_integral_initial_ball {n : ℕ} {f : ℝ^n → ℝ} {c : ℝ^n} {T : ℝ}
    (hf : IntegrableOn f (ball c T)) :
    Tendsto (fun t ↦ ∫ x in ball c (T - t), f x) (𝓝[>] 0) (𝓝 (∫ x in ball c T, f x)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (ball c T)) (l := 𝓝[>] (0 : ℝ))
    (f := f) (F := fun t ↦ (ball c (T - t)).indicator f) (fun x ↦ ‖f x‖)
    (Eventually.of_forall fun t ↦ hf.aestronglyMeasurable.indicator measurableSet_ball)
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self f x)
    hf.norm ?_
  · apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [integral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball (sub_le_self T ht.le))]
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hpos : 0 < T - dist x c := sub_pos.mpr (mem_ball.mp hx)
    have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < T - dist x c :=
      (eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with t ht
    exact (indicator_of_mem (mem_ball.mpr (by linarith)) f).symm

/-- The quantitative one-third-power bound, uniformly above any fixed interior
initial cap. Both the flux bound and energy bound follow from the PDE. -/
theorem integral_quinticSlice_le_initialEnergy_flux_rpow_of_wave {u : ℝ^4 → ℝ} {a s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (ha : 0 < a) (has : a ≤ s)
    (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    let E := ballIntegral 3 (fun x ↦
      semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u (timeSpaceCons a x)) c (T - a)
    let φ := (1 / Real.sqrt 2) * (∫ p in
      {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
        semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
          ∂Measure.euclideanHausdorffMeasure 3)
    (∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) ≤
      (24 * E ^ (2 / 3 : ℝ) +
        12 * (∫ x in Metric.ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) *
          (6 : ℝ) ^ (1 / 3 : ℝ)) * φ ^ (1 / 3 : ℝ) := by
  dsimp only
  have hs : 0 < s := ha.trans_le has
  have hb := integral_quinticSlice_le_actualFlux_of_wave hu c hs hsT hwave
  apply hb.trans
  apply morawetz_flux_absorption
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (semilinearWaveConeDissipation_nonneg
      (fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z) u c)
  · have hflux := normalized_integral_quinticConeDissipation_le_energy hu c hs hsT
      (fun t ht ↦ hwave t ⟨hs.trans_le ht.1, ht.2⟩)
    exact hflux.trans (quintic_ballIntegral_energy_antitoneOn hu c hwave
      ⟨ha, has.trans_lt hsT⟩ ⟨hs, hsT⟩ has)

/-- The quantitative estimate includes the initial cap for a representative
smooth below the terminal time. The initial endpoint follows by continuity. -/
theorem integral_quinticSlice_le_initialEnergy_flux_rpow_of_upper_band {v : ℝ^4 → ℝ} {T : ℝ}
    (hT : 0 < T) (hv : ContDiffOn ℝ 2 v {p | p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ ball c (T - t), waveOperator v (timeSpaceCons t x) +
      v (timeSpaceCons t x) ^ 5 = 0) :
    let E := ballIntegral 3 (fun x ↦
      semilinearWaveEnergyDensity (Real.signedPowerPotential 5) v (timeSpaceCons 0 x)) c T
    ∀ s ∈ Ico 0 T,
      let φ := (1 / Real.sqrt 2) * (∫ p in
        {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
          semilinearWaveConeDissipation (Real.signedPowerPotential 5) v c p
            ∂Measure.euclideanHausdorffMeasure 3)
      (∫ x in ball c (T - s), v (timeSpaceCons s x) ^ 6) ≤
        (24 * E ^ (2 / 3 : ℝ) +
          12 * (∫ x in ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) *
            (6 : ℝ) ^ (1 / 3 : ℝ)) * φ ^ (1 / 3 : ℝ) := by
  let E := ballIntegral 3 (fun x ↦
    semilinearWaveEnergyDensity (Real.signedPowerPotential 5) v (timeSpaceCons 0 x)) c T
  let K := (∫ x in ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ)
  let C := 24 * E ^ (2 / 3 : ℝ) + 12 * K * (6 : ℝ) ^ (1 / 3 : ℝ)
  let φ (s : ℝ) := (1 / Real.sqrt 2) * (∫ p in
    {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
      semilinearWaveConeDissipation (Real.signedPowerPotential 5) v c p
        ∂Measure.euclideanHausdorffMeasure 3)
  let ρ (x : ℝ^3) := (1 / 2 : ℝ) * ‖coneProfileGradient T c v x‖ ^ 2 + coneProfile T c v x ^ 6 / 6
  have hvband : ContDiffOn ℝ 2 v {p | (-1 : ℝ) < p 0 ∧ p 0 < T} := hv.mono (fun _ hp ↦ hp.2)
  have hvpos : ContDiffOn ℝ 2 v {p | 0 < p 0 ∧ p 0 < T} := hv.mono (fun _ hp ↦ hp.2)
  have hwclosed := quintic_wave_on_closed_base hT hv c hwave
  obtain ⟨hG, hW⟩ := ConeProfile.integrable_densities_of_wave hvband c
    (by norm_num : (-1 : ℝ) < 0) hwclosed
  simp only [sub_zero] at hG hW
  have hρ : IntegrableOn ρ (ball c T) := (hG.const_mul (1 / 2 : ℝ)).add (hW.div_const 6)
  have hρpos : ∀ x, 0 ≤ ρ x := fun x ↦ by dsimp only [ρ]; positivity
  have hφeq (s : ℝ) (hs : 0 ≤ s) : φ s = ∫ x in ball c (T - s), ρ x := by
    exact normalized_integral_quinticConeDissipation_eq_profile hvband c (by linarith)
      (fun t ht ↦ hwclosed t ⟨hs.trans ht.1, ht.2⟩)
  have hφ0 : φ 0 ≤ E := by
    simpa only [φ, E, sub_zero] using normalized_integral_quinticConeDissipation_le_energy
      hvband c (by norm_num : (-1 : ℝ) < 0) hT hwclosed
  have hφbound (s : ℝ) (hs : 0 ≤ s) : φ s ≤ E := by
    apply le_trans ?_ hφ0
    rw [hφeq s hs, hφeq 0 le_rfl, sub_zero]
    exact setIntegral_mono_set hρ (ae_of_all _ hρpos)
      (Eventually.of_forall (ball_subset_ball (sub_le_self T hs)))
  have hpositive (s : ℝ) (hs : 0 < s) (hsT : s < T) :
      (∫ x in ball c (T - s), v (timeSpaceCons s x) ^ 6) ≤ C * φ s ^ (1 / 3 : ℝ) := by
    have hφpos : 0 ≤ φ s := by
      rw [hφeq s hs.le]
      exact integral_nonneg hρpos
    exact (integral_quinticSlice_le_actualFlux_of_wave hvpos c hs hsT hwave).trans
      (morawetz_flux_absorption hφpos (hφbound s hs.le))
  have hzero : (∫ x in ball c T, v (timeSpaceCons 0 x) ^ 6) ≤ C * φ 0 ^ (1 / 3 : ℝ) := by
    have hslicelim := tendsto_ballIntegral_shrinking_initial hT
      ((hv.continuousOn.mono (fun _ hp ↦ hp.2)).pow 6) c
    have hφlim : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) := by
      have h := tendsto_integral_initial_ball hρ
      have he0 : φ 0 = ∫ x in ball c T, ρ x := by
        simpa only [sub_zero] using hφeq 0 le_rfl
      rw [← he0] at h
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hφeq s hs.le).symm
    have hroot := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).tendsto
      (φ 0) |>.comp hφlim
    apply le_of_tendsto_of_tendsto hslicelim (hroot.const_mul C)
    have he : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < T := (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
    filter_upwards [he, self_mem_nhdsWithin] with s hsT hs
    exact hpositive s hs hsT
  dsimp only
  intro s hs
  change (∫ x in ball c (T - s), v (timeSpaceCons s x) ^ 6) ≤ C * φ s ^ (1 / 3 : ℝ)
  rcases hs.1.eq_or_lt with he | hpos
  · subst s
    simpa only [sub_zero] using hzero
  · exact hpositive s hpos hs.2

end WaveEquation
