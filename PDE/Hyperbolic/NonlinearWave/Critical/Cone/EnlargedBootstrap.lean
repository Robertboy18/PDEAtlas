/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.QuinticEnergy
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Analysis.Calculus.PowerPotential.Classical
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Hyperbolic.NonlinearWave.Critical.Bootstrap
import CAS.ExactTactic

/-!
# Critical bootstrap beyond the regularity band

The cone tip and the regularity endpoint are independent. Small energy closes the nonlinear
bootstrap before the endpoint. Constants are fixed before the late cone is chosen.

These are the nonlinear estimates of step 5 of the proof of Evans, §12.4, Theorem 3, which give (22)
on a cone enlarged by `δ` from the small energy (23)-(24). The physical linear prefix estimates
remain explicit hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 5 of its proof, equations (22)-(24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Critical bootstrap on a cone whose geometric tip is beyond the regularity band. -/
theorem memLp_four_twelve_enlarged_cone_of_strichartz {u : ℝ^4 → ℝ} {B T s C K M : ℝ}
    (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < B}) (c : ℝ^3) (hs : 0 < s) (hsB : s < B) (hBT : B ≤ T)
    (hC : 0 < C) (hK : 0 ≤ K) (hsmall : (K * M) * (2 * C) ^ 4 < C)
    (hM : ∀ t ∈ Ico s B, lpNorm (fun x ↦ u (timeSpaceCons t x)) 6
      (volume.restrict (Metric.ball c (T - t))) ≤ M)
    (hlinear : ∀ t ∈ Ico s B, lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Icc s t)) ≤
      C + K * ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
      (volume.restrict (Metric.ball c (T - r)))) :
    MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Ico s B)) := by
  classical
  let v : ℝ^4 → ℝ := {p | 0 < p 0 ∧ p 0 < B}.indicator u
  have hb : MeasurableSet {p : ℝ^4 | 0 < p 0 ∧ p 0 < B} :=
    ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)).measurableSet
  have hv : Measurable v := by
    simpa only [v, piecewise_eq_indicator] using
      hu.measurable_piecewise continuous_zero.continuousOn hb
  have hc : Continuous (fun q : ℝ × ℝ^3 ↦ timeSpaceCons q.1 q.2) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous
  have hmask : Measurable (movingConeField v c T) := by
    apply (hv.comp hc.measurable).indicator
    exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
        (isOpen_lt (continuous_snd.dist continuous_const)
          (continuous_const.sub continuous_fst)).measurableSet)
  have he (t : ℝ) (ht : t ∈ Ico s B) :
      (fun x ↦ v (timeSpaceCons t x)) = fun x ↦ u (timeSpaceCons t x) := by
    funext x
    exact indicator_of_mem (by simpa using And.intro (hs.trans_le ht.1) ht.2) u
  have hn (t : ℝ) (ht : t ∈ Ico s B) (p : ℝ≥0∞) :
      lpNorm (fun x ↦ movingConeField v c T (t, x)) p volume =
        lpNorm (fun x ↦ u (timeSpaceCons t x)) p
          (volume.restrict (Metric.ball c (T - t))) := by
    rw [lpNorm_movingConeField ⟨hs.trans_le ht.1, ht.2.trans_le hBT⟩, he t ht]
  have hm (t : ℝ) (ht : t ∈ Ico s B) (p : ℝ≥0∞) :
      MemLp (fun x ↦ movingConeField v c T (t, x)) p volume := by
    rw [movingConeField_section ⟨hs.trans_le ht.1, ht.2.trans_le hBT⟩,
      memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet, he t ht]
    apply ContinuousOn.memLp_of_subset_isCompact (s := Metric.closedBall c (T - t))
      ?_ (isCompact_closedBall _ _) measurableSet_ball Metric.ball_subset_closedBall
    exact hu.comp (hc.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun x _ ↦ by simpa using And.intro (hs.trans_le ht.1) ht.2)
  have hloc (t : ℝ) (ht : t ∈ Ico s B) :
      MemLp (fun r ↦ lpNorm (fun x ↦ movingConeField v c T (r, x)) 12 volume)
        4 (volume.restrict (Icc s t)) := by
    obtain ⟨g, hg, hge⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
      (k := 0) (f := u) (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ)
      (by simpa using (contDiffOn_zero.mpr hu : ContDiffOn ℝ 0 u _)) hs ht.2
    have hgmem := memLp_four_twelve_movingConeField_local hg.continuous.continuousOn c
      hs (ht.2.trans_le hBT)
    apply MemLp.ae_eq ?_ hgmem
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hrB : r ∈ Ico s B := ⟨hr.1, hr.2.trans_lt ht.2⟩
    rw [hn r hrB 12, lpNorm_movingConeField
      (u := g) ⟨hs.trans_le hr.1, (hr.2.trans_lt ht.2).trans_le hBT⟩]
    congr 1
    funext x
    exact (hge (timeSpaceCons r x) (by simpa using hr)).eq_of_nhds.symm
  have hboot : MemLp (fun r ↦ lpNorm (fun x ↦ movingConeField v c T (r, x)) 12 volume) 4
      (volume.restrict (Ico s B)) := by
    apply memLp_four_twelve_of_quintic_strichartz_bound hsB hmask hC hK hsmall
      (fun t ht ↦ hm t ht 12) (fun t ht ↦ hm t ht 6)
      (fun t ht ↦ by rw [hn t ht 6]; exact hM t ht) hloc
    intro t ht
    have hsub : Icc s t ⊆ Ico s B := fun _ hr ↦ ⟨hr.1, hr.2.trans_lt ht.2⟩
    have hnorm : lpNorm (fun r ↦ lpNorm (fun x ↦ movingConeField v c T (r, x)) 12 volume) 4
        (volume.restrict (Icc s t)) = lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
          (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Icc s t)) := by
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hn r (hsub hr) 12
    rw [hnorm]
    have hf : (∫ r in Icc s t, lpNorm (fun x ↦ movingConeField v c T (r, x) ^ 5) 2 volume) =
        ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
          (volume.restrict (Metric.ball c (T - r))) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      dsimp only
      rw [lpNorm_quintic_movingConeField ⟨hs.trans_le hr.1, (hr.2.trans_lt ht.2).trans_le hBT⟩]
      have hpow : (fun x ↦ v (timeSpaceCons r x) ^ 5) =
          fun x ↦ u (timeSpaceCons r x) ^ 5 := by
        funext x
        rw [congrFun (he r (hsub hr)) x]
      rw [hpow]
    rw [hf]
    exact hlinear t ht
  apply MemLp.ae_eq ?_ hboot
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  exact hn t ht 12

/-- Small enlarged-cone energy gives the critical mixed norm through the original
regularity endpoint; the linear prefix estimate is the only remaining analytic input. -/
theorem memLp_four_twelve_enlarged_cone_of_energy {u : ℝ^4 → ℝ} {B T s C K M : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < B}) (c : ℝ^3) (hs : 0 < s) (hsB : s < B)
    (hBT : B ≤ T) (hC : 0 < C) (hK : 0 ≤ K) (hM : 0 ≤ M) (hsmall : (K * M) * (2 * C) ^ 4 < C)
    (henergy : ∀ t ∈ Ico s B, ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) c (T - t) ≤ M ^ 6 / 6)
    (hlinear : ∀ t ∈ Ico s B, lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Icc s t)) ≤
      C + K * ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
      (volume.restrict (Metric.ball c (T - r)))) :
    MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Ico s B)) := by
  apply memLp_four_twelve_enlarged_cone_of_strichartz hu.continuousOn c
    hs hsB hBT hC hK hsmall ?_ hlinear
  intro t ht
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < B} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hpow := lpNorm_six_pow_le_quintic_ball_energy (fun x ↦ hu.contDiffAt (hopen.mem_nhds
      (by simpa using And.intro (hs.trans_le ht.1) ht.2))) c (T - t)
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hM
  linarith [henergy t ht]

/-- Vanishing energy supplies a strictly enlarged cone where the nonlinear
critical bootstrap closes. Constants are chosen before the late cone. -/
theorem exists_enlarged_cone_bootstrap_of_energy_decay {u : ℝ^4 → ℝ} {B C K : ℝ} (hB : 0 < B)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < B}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 B, ∀ x : ℝ^3, semilinearWaveOperator (Real.signedPowerPotential 5) u
      (timeSpaceCons t x) = 0)
    (henergy : Tendsto (fun t ↦ ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) c (B - t)) (𝓝[<] B) (𝓝 0))
    (hC : 0 < C) (hK : 0 ≤ K) :
    ∃ s ∈ Ioo 0 B, ∃ δ > 0,
      (∀ t ∈ Ico s B,
        lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
          (volume.restrict (Metric.ball c (B + δ - r)))) 4 (volume.restrict (Icc s t)) ≤
        C + K * ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
          (volume.restrict (Metric.ball c (B + δ - r)))) →
      MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
        (volume.restrict (Metric.ball c (B + δ - r)))) 4 (volume.restrict (Ico s B)) := by
  have hc : Continuous (fun M : ℝ ↦ (K * M) * (2 * C) ^ 4) := by fun_prop
  have hzero : Tendsto (fun M : ℝ ↦ (K * M) * (2 * C) ^ 4) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨M, hsmall, hM⟩ := ((hzero.eventually (eventually_lt_nhds hC)).and
    self_mem_nhdsWithin).exists
  obtain ⟨s, hs, δ, hδ, hbound⟩ := exists_enlarged_cone_energy_lt
    (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5))
    (fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z)
    hB hu c hwave henergy (show 0 < M ^ 6 / 6 by positivity)
  refine ⟨s, hs, δ, hδ, ?_⟩
  intro hlinear
  exact memLp_four_twelve_enlarged_cone_of_energy hu c hs.1 hs.2
    (le_add_of_nonneg_right hδ.le) hC hK hM.le hsmall (fun t ht ↦ (hbound t ht).le) hlinear

/-- Quintic waves admit an enlarged critical cone from the two base-cone
linear estimates, conditional only on the new cone's linear prefix bound. -/
theorem exists_enlarged_cone_bootstrap_of_wave_strichartz {u : ℝ^4 → ℝ} {T C K L C' K' : ℝ}
    (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^
      5 = 0)
    (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T, lpNorm (fun r ↦
      lpNorm (fun x ↦ u (timeSpaceCons r x)) 12 (volume.restrict (Metric.ball c (T - r)))) 4
      (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc s t, lpNorm
      (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (T - r))))
    (hderivative : ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q))))
    (hC' : 0 < C') (hK' : 0 ≤ K') :
    ∃ s ∈ Ioo 0 T, ∃ δ > 0,
      (∀ t ∈ Ico s T,
        lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
          (volume.restrict (Metric.ball c (T + δ - r)))) 4 (volume.restrict (Icc s t)) ≤
        C' + K' * ∫ r in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2
          (volume.restrict (Metric.ball c (T + δ - r)))) →
      MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
        (volume.restrict (Metric.ball c (T + δ - r)))) 4 (volume.restrict (Ico s T)) := by
  have henergy := tendsto_quintic_localEnergy_of_wave_strichartz hT hu c
    (fun t ht x _ ↦ hwave t ht x) hC hK hL hlinear hderivative
  apply exists_enlarged_cone_bootstrap_of_energy_decay hT hu c ?_ henergy hC' hK'
  intro t ht x
  have he : semilinearWaveOperator (Real.signedPowerPotential 5) u (timeSpaceCons t x) =
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 := by
    unfold semilinearWaveOperator
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    unfold Real.signedPower
    rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
      (show Even 4 by decide).pow_abs]
    cas
  rw [he]
  exact hwave t ht x

end WaveEquation.Critical
