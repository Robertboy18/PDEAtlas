/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.TruncatedCone
public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeEnergy
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Removing the terminal cap from the quintic Morawetz identity

The off-shell divergence identity on truncated cones has a nonpositive volume term for the quintic
equation. Local energy control makes the terminal cap vanish. The area formula and dominated
convergence then bound the full lateral current by the initial cap, assuming the pulled-back current
is integrable.

This is step 1 of the proof of Evans, §12.4, Theorem 2: integrating (6) over the truncated cone, the
volume term `-u⁶/3` is nonpositive and the top term vanishes as `τ → T`, which gives (9). Regularity
is only on the open time band below the tip.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, step 1, equations (6)-(9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped RealInnerProductSpace Topology

namespace WaveEquation

private theorem normalized_truncated_current_eq_annulus {n : ℕ} [Fact (0 < n)] {P : ℝ^(n + 1) → ℝ}
    {Q : ℝ^(n + 1) → ℝ^n} {s₀ s τ T : ℝ} (hP : ContDiffOn ℝ 1 P {p | s₀ < p 0 ∧ p 0 < T})
    (hQ : ContDiffOn ℝ 1 Q {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s) (hτ : τ < T) :
    (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
      (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
        ∂Measure.euclideanHausdorffMeasure n) =
      ∫ x in Metric.ball c (T - s) \ Metric.ball c (T - τ),
        P (backwardConeGraph c T x) -
          ⟪Q (backwardConeGraph c T x), NormedSpace.normalize (x - c)⟫ := by
  obtain ⟨P', hP', heP⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 1) (f := P) (EuclideanSpace.proj 0 : ℝ^(n + 1) →L[ℝ] ℝ)
    (by simpa using hP) hs hτ
  obtain ⟨Q', hQ', heQ⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 1) (f := Q) (EuclideanSpace.proj 0 : ℝ^(n + 1) →L[ℝ] ℝ)
    (by simpa using hQ) hs hτ
  simp only [EuclideanSpace.coe_proj] at heP heQ
  have hsurface : (∫ p in truncatedConeLateralSurface c T s τ,
      (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
        ∂Measure.euclideanHausdorffMeasure n) = ∫ p in truncatedConeLateralSurface c T s τ,
        coneNormalTrace (coneCurrentNormalFlux P' Q') c p
          ∂Measure.euclideanHausdorffMeasure n := by
    apply setIntegral_congr_fun (isCompact_truncatedConeLateralSurface c T s τ).measurableSet
    intro p hp
    dsimp only [coneNormalTrace, coneCurrentNormalFlux]
    rw [(heP p ⟨hp.1, hp.2.1⟩).eq_of_nhds, (heQ p ⟨hp.1, hp.2.1⟩).eq_of_nhds]
  rw [hsurface, integral_truncatedConeLateralSurface c hτ.le _
    (measurable_coneNormalTrace (continuous_coneCurrentNormalFlux hP'.continuous hQ'.continuous) c),
    ← mul_assoc, one_div_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))),
    one_mul]
  apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
  intro x hx
  have ht : (backwardConeGraph c T x) 0 ∈ Icc s τ := by
    have hx1 : ‖x - c‖ < T - s := by simpa only [Metric.mem_ball, dist_eq_norm] using hx.1
    have hx2 : T - τ ≤ ‖x - c‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx.2
    change s ≤ T - ‖x - c‖ ∧ T - ‖x - c‖ ≤ τ
    constructor <;> linarith
  simp only [coneNormalTrace, coneCurrentNormalFlux, backwardConeGraph, spatialPart_timeSpaceCons]
  have hp := (heP _ ht).eq_of_nhds
  have hq := (heQ _ ht).eq_of_nhds
  simp only [backwardConeGraph] at hp hq
  rw [← hp, ← hq]

private theorem tendsto_integral_annulus {n : ℕ} [Nontrivial (ℝ^n)] {f : ℝ^n → ℝ} {c : ℝ^n}
    {r T : ℝ} (hf : IntegrableOn f (Metric.ball c r)) :
    Tendsto (fun τ ↦ ∫ x in Metric.ball c r \ Metric.ball c (T - τ), f x) (𝓝[<] T)
      (𝓝 (∫ x in Metric.ball c r, f x)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Metric.ball c r)) (l := 𝓝[<] T)
    (f := f) (F := fun τ ↦ (Metric.ball c (T - τ))ᶜ.indicator f) (fun x ↦ ‖f x‖)
    (Eventually.of_forall fun τ ↦ hf.aestronglyMeasurable.indicator measurableSet_ball.compl)
    (Eventually.of_forall fun τ ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self f x)
    hf.norm ?_
  · simpa only [integral_indicator measurableSet_ball.compl,
      Measure.restrict_restrict measurableSet_ball.compl, inter_comm _ (Metric.ball c r),
      ← sdiff_eq] using h
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne c)] with x hx
    have hpos : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have he : ∀ᶠ τ in 𝓝[<] T, T - ‖x - c‖ < τ :=
      (eventually_gt_nhds (sub_lt_self T hpos)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with τ hτ
    exact (indicator_of_mem (by
      change ¬ dist x c < T - τ
      rw [dist_eq_norm]
      linarith) f).symm

/-- The entire lateral scaling current is bounded above by its initial cap.
This intermediate result assumes integrability of the pulled-back current;
the terminal cap and the nonpositive volume term follow from the quintic equation. -/
theorem integral_scalingFlux_le_initialCap_of_integrable {u : ℝ^(3 + 1) → ℝ} {s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0)
    (hflux : IntegrableOn (fun x ↦ coneCurrentNormalFlux (scalingCurrentDensity
      (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u)
      (fun p ↦ WithLp.toLp 2 (fun i ↦ scalingCurrentFlux (Real.signedPowerPotential 5) 1
      (timeSpaceCons T c) u i p)) (backwardConeGraph c T x, NormedSpace.normalize (x - c)))
      (Metric.ball c (T - s))) :
    (∫ x in Metric.ball c (T - s),
      coneCurrentNormalFlux
        (scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u)
        (fun p ↦ WithLp.toLp 2 (fun i ↦
          scalingCurrentFlux (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u i p))
        (backwardConeGraph c T x, NormedSpace.normalize (x - c))) ≤
      ballIntegral 3 (fun x ↦
        scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
          (timeSpaceCons s x)) c (T - s) := by
  let P := scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
  let Q (p : ℝ^(3 + 1)) : ℝ^3 := WithLp.toLp 2 (fun i ↦
    scalingCurrentFlux (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u i p)
  let F (x : ℝ^3) := coneCurrentNormalFlux P Q
    (backwardConeGraph c T x, NormedSpace.normalize (x - c))
  let C (t : ℝ) := ballIntegral 3 (fun x ↦ P (timeSpaceCons t x)) c (T - t)
  have hopen : IsOpen {p : ℝ^(3 + 1) | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hV := Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)
  have hP : ContDiffOn ℝ 1 P {p | 0 < p 0 ∧ p 0 < T} := by
    intro p hp
    exact (contDiffAt_scalingCurrentDensity 1 (timeSpaceCons T c) hV.contDiffAt
      (hu.contDiffAt (hopen.mem_nhds hp))).contDiffWithinAt
  have hQ : ContDiffOn ℝ 1 Q {p | 0 < p 0 ∧ p 0 < T} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_piLp 2).mpr
    exact fun i ↦ contDiffAt_scalingCurrentFlux 1 (timeSpaceCons T c) hV.contDiffAt
      (hu.contDiffAt (hopen.mem_nhds hp)) i
  have hcap : Tendsto C (𝓝[<] T) (𝓝 0) :=
    tendsto_quintic_ballIntegral_scalingCurrentDensity_zero_of_wave hu c hs hsT hwave
  have hbound : ∀ᶠ τ in 𝓝[<] T,
      (∫ x in Metric.ball c (T - s) \ Metric.ball c (T - τ), F x) ≤ C s - C τ := by
    have he : ∀ᶠ τ in 𝓝[<] T, s < τ := (eventually_gt_nhds hsT).filter_mono nhdsWithin_le_nhds
    filter_upwards [he, self_mem_nhdsWithin] with τ hsτ hτ
    have hid := integral_morawetzCurrent_balance_quintic_of_wave c hs hsτ.le hτ hu
      (fun t ht ↦ hwave t ⟨hs.trans_le ht.1, ht.2.trans_lt hτ⟩)
    have harea := normalized_truncated_current_eq_annulus hP hQ c hs hτ
    change _ = C τ - C s + _ at hid
    change _ = ∫ x in Metric.ball c (T - s) \ Metric.ball c (T - τ), F x at harea
    rw [harea] at hid
    have hneg : (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
        -(u (timeSpaceCons t x) ^ 6 / 3)) ≤ 0 := by
      rw [intervalIntegral.integral_of_le hsτ.le]
      exact integral_nonpos fun t ↦ integral_nonpos fun x ↦ neg_nonpos.mpr (by positivity)
    linarith
  have h := le_of_tendsto_of_tendsto (tendsto_integral_annulus hflux)
    (tendsto_const_nhds.sub hcap) hbound
  simpa only [sub_zero] using h

end WaveEquation
