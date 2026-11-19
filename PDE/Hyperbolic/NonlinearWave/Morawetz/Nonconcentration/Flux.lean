/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.Limit
import CAS.ExactTactic

/-!
# Normalized cone flux in the quintic estimate

The graph area formula identifies Hausdorff-normalized null energy with the two
spatial cone-profile densities. Their integrability and the quintic estimate give
both the flux bound and its terminal limit, without regularity at the tip.

The normalized flux is the `φ(s)` of the Notation of Evans, §12.4, before Theorem 2; its vanishing
as `s → T` is the step from (5) to (18) in step 3 of the proof of Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Notation, Theorem 2, and Theorem 3, step 3 of its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter PDE PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

/-- The open lateral cone has the normalized spatial graph integral. -/
private theorem normalized_integral_openCone_eq_graph {n : ℕ} [Fact (0 < n)] (c : ℝ^n) (s T : ℝ)
    (g : ℝ^(n + 1) → ℝ)
    (hg : AEStronglyMeasurable g ((Measure.euclideanHausdorffMeasure n).restrict
      {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0})) :
    (1 / Real.sqrt 2) * (∫ p in {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
      g p ∂Measure.euclideanHausdorffMeasure n) = ∫ x in ball c (T - s),
      g (backwardConeGraph c T x) := by
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa using (Fact.out : 0 < n))
  have himage : backwardConeGraph c T '' (ball c (T - s) \ {c}) =
      {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hρ : ‖x - c‖ < T - s := by simpa only [mem_ball, dist_eq_norm] using hx.1
      have hpos : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.2)
      change s < T - ‖x - c‖ ∧ T - ‖x - c‖ < T ∧ ‖x - c‖ = T - (T - ‖x - c‖)
      exact ⟨by linarith, by linarith, (sub_sub_cancel T _).symm⟩
    · intro hp
      refine ⟨spatialPart p, ⟨?_, ?_⟩, ?_⟩
      · change dist (spatialPart p) c < T - s
        rw [dist_eq_norm, hp.2.2]
        linarith [hp.1]
      · change spatialPart p ≠ c
        intro he
        have hz : ‖spatialPart p - c‖ = 0 := by simp [he]
        rw [hp.2.2] at hz
        linarith [hp.2.1]
      · simp only [backwardConeGraph, hp.2.2, sub_sub_cancel, timeSpaceCons_spatialPart]
  rw [← himage] at hg ⊢
  rw [integral_backwardConeGraph_image c T (isOpen_ball.sdiff isClosed_singleton)
    (by simp) g hg, ← mul_assoc,
    one_div_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))), one_mul]
  exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton c))



/-- The normalized energy flux on the open lateral cone is exactly the
spatial integral of the profile's gradient and quintic potential. -/
theorem normalized_integral_quinticConeDissipation_eq_profile {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    (1 / Real.sqrt 2) * (∫ p in
      {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
        semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
          ∂Measure.euclideanHausdorffMeasure 3) =
      ∫ x in ball c (T - s),
        (1 / 2 : ℝ) * ‖coneProfileGradient T c u x‖ ^ 2 + coneProfile T c u x ^ 6 / 6 := by
  have hV := Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)
  have hnonneg := fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z
  have hD := integrableOn_cone_dissipation hV hnonneg hu c hs (by
    intro t ht x hx
    unfold semilinearWaveOperator
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    unfold Real.signedPower
    rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
      (show Even 4 by decide).pow_abs]
    have heq : u (timeSpaceCons t x) ^ 4 * u (timeSpaceCons t x) =
        u (timeSpaceCons t x) ^ 5 := by cas
    rw [heq]
    exact hwave t ht x hx)
  have hsmall := hD.mono_set (show {p : ℝ^4 | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0} ⊆
      {p : ℝ^4 | s ≤ p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0} from fun _ hp ↦ ⟨hp.1.le, hp.2⟩)
  rw [normalized_integral_openCone_eq_graph c s T _ hsmall.aestronglyMeasurable]
  apply setIntegral_congr_fun measurableSet_ball
  intro x _
  dsimp only
  rw [ConeProfile.cone_dissipation_graph_eq]
  norm_num [Real.signedPowerPotential, Real.rpow_ofNat, (show Even 6 by decide).pow_abs]

/-- The Hausdorff-normalized energy flux above a late slice tends to zero. -/
theorem tendsto_normalized_integral_quinticConeDissipation_zero_of_wave {u : ℝ^4 → ℝ} {T : ℝ}
    (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    Tendsto (fun s ↦ (1 / Real.sqrt 2) * (∫ p in {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ =
      T - p 0}, semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
      ∂Measure.euclideanHausdorffMeasure 3)) (𝓝[<] T) (𝓝 0) := by
  apply (tendsto_integral_quinticConeEnergy_zero_of_wave hT hu c hwave).congr'
  have he : ∀ᶠ s in 𝓝[<] T, 0 < s := (eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with s hs
  exact (normalized_integral_quinticConeDissipation_eq_profile hu c hs
    (fun t ht ↦ hwave t ⟨hs.trans_le ht.1, ht.2⟩)).symm

/-- The slice estimate in terms of the normalized cone flux.
This precedes absorption of its linear term into the one-third power. -/
theorem integral_quinticSlice_le_actualFlux_of_wave {u : ℝ^4 → ℝ} {s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    let φ := (1 / Real.sqrt 2) * (∫ p in
      {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
        semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
          ∂Measure.euclideanHausdorffMeasure 3)
    (∫ x in ball c (T - s), u (timeSpaceCons s x) ^ 6) ≤
      24 * φ + 12 * (∫ x in ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) *
        (6 * φ) ^ (1 / 3 : ℝ) := by
  dsimp only
  let φ := (1 / Real.sqrt 2) * (∫ p in {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
      semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
        ∂Measure.euclideanHausdorffMeasure 3)
  let K := (∫ x in ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ)
  have hwave' := fun t (ht : t ∈ Ico s T) ↦ hwave t ⟨hs.trans_le ht.1, ht.2⟩
  obtain ⟨hG, hW⟩ := ConeProfile.integrable_densities_of_wave hu c hs hwave'
  have hφ := normalized_integral_quinticConeDissipation_eq_profile hu c hs hwave'
  rw [integral_add (hG.const_mul (1 / 2 : ℝ)) (hW.div_const 6),
    integral_const_mul, integral_div] at hφ
  change φ = _ at hφ
  have hgpos : 0 ≤ ∫ x in ball c (T - s), ‖coneProfileGradient T c u x‖ ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hwpos : 0 ≤ ∫ x in ball c (T - s), coneProfile T c u x ^ 6 :=
    integral_nonneg fun x ↦ by positivity
  have hg : (∫ x in ball c (T - s), ‖coneProfileGradient T c u x‖ ^ 2) ≤ 2 * φ := by
    linarith
  have hw : (∫ x in ball c (T - s), coneProfile T c u x ^ 6) ≤ 6 * φ := by linarith
  have hK : 0 ≤ K := Real.rpow_nonneg (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) _
  have hr := Real.rpow_le_rpow hwpos hw (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hb := integral_quinticSlice_le_coneDensities_of_wave hu c hs hsT hwave
  change _ ≤ 12 * _ + 12 * K * _ at hb
  change _ ≤ 24 * φ + 12 * K * (6 * φ) ^ (1 / 3 : ℝ)
  have hcoeff : 0 ≤ 12 * K := mul_nonneg (by norm_num) hK
  nlinarith [mul_le_mul_of_nonneg_left hr hcoeff]

end WaveEquation
