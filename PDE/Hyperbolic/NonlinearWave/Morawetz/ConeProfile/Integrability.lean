/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.RadialFlux

/-!
# Integrability of the cone-profile square terms

Hardy's inequality, transported from the zero-centered ball, supplies the singular
weight. The tangential gradient controls its radial component in L².
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter PDE PDE.Common NormedSpace
open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.RadialSquareFlux
open scoped RealInnerProductSpace Sobolev

namespace WaveEquation.ConeProfile

private theorem memLp_div_dist_of_h1 {n : ℕ} (hn : 3 ≤ n) {c : ℝ^n} {r : ℝ} (hr : 0 < r)
    (U : H¹(ball c r)) {w : ℝ^n → ℝ} (hU : baseRepresentative U =ᵐ[domainMeasure n (ball c r)] w) :
    MemLp (fun x ↦ w x / ‖x - c‖) 2 (domainMeasure n (ball c r)) := by
  obtain ⟨V, hV⟩ := exists_h1_translate U hU
  have hH : MemLp (fun x ↦ w (c + x) / ‖x‖) 2 (domainMeasure n (ball 0 r)) :=
    (memLp_congr_ae (hV.mono fun x hx ↦ by rw [hx])).mp
      (SobolevSpace.Hardy.memLp_div_norm_h1_ball hn hr V)
  have hpre : (fun x : ℝ^n ↦ -c + x) ⁻¹' ball 0 r = ball c r := by
    ext x
    simp [mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm]
  have hm : MeasurePreserving (fun x : ℝ^n ↦ -c + x)
      (domainMeasure n (ball c r)) (domainMeasure n (ball 0 r)) := by
    have h := (measurePreserving_add_left (volume : Measure (ℝ^n)) (-c)).restrict_preimage
      (s := ball 0 r) isOpen_ball.measurableSet
    rwa [hpre] at h
  simpa only [Function.comp_def, neg_add_eq_sub, ← add_sub_assoc, add_sub_cancel_left] using
    hH.comp_measurePreserving hm

private theorem memLp_inner_normalize {n : ℕ} {c : ℝ^n} {r : ℝ} {G : ℝ^n → ℝ^n}
    (hG : MemLp G 2 (domainMeasure n (ball c r))) :
    MemLp (fun x ↦ ⟪G x, normalize (x - c)⟫) 2 (domainMeasure n (ball c r)) := by
  have hν : AEStronglyMeasurable (fun x : ℝ^n ↦ normalize (x - c)) (domainMeasure n (ball c r)) :=
    (((measurable_id.sub measurable_const).norm.inv).smul
      (measurable_id.sub measurable_const)).aestronglyMeasurable
  apply hG.of_le (hG.aestronglyMeasurable.inner (𝕜 := ℝ) hν)
  refine Eventually.of_forall fun x ↦ ?_
  have hnorm : ‖normalize (x - c)‖ ≤ 1 := by
    by_cases hx : x = c
    · simp [hx]
    · exact (norm_normalize (sub_ne_zero.mpr hx)).le
  exact (norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hnorm)

/-- Every term in the radial completed square is integrable from the cone densities. -/
theorem integrable_radial_terms {n : ℕ} (hn : 3 ≤ n) {T r : ℝ} {c : ℝ^n} {u : ℝ^(n + 1) → ℝ}
    (hr : 0 < r) (hu : ∀ x ∈ ball c r, x ≠ c → ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x))
    (hgradient : IntegrableOn (fun x ↦ ‖coneProfileGradient T c u x‖ ^ 2) (ball c r))
    (hpotential : IntegrableOn (fun x ↦ coneProfile T c u x ^ 6) (ball c r)) :
    IntegrableOn (fun x ↦ ‖x - c‖ * ⟪coneProfileGradient T c u x, normalize (x - c)⟫ ^ 2)
        (ball c r) ∧
      IntegrableOn (fun x ↦ coneProfile T c u x *
        ⟪coneProfileGradient T c u x, normalize (x - c)⟫) (ball c r) ∧
      IntegrableOn (fun x ↦ coneProfile T c u x ^ 2 / ‖x - c‖) (ball c r) := by
  obtain ⟨U, hU, hDU⟩ := exists_h1_of_integrable_densities (by omega : 2 ≤ n)
    hu hgradient hpotential
  have hw : MemLp (coneProfile T c u) 2 (domainMeasure n (ball c r)) :=
    (memLp_congr_ae hU).mp (Lp.memLp (wkpBaseCoordinateCLM U))
  have hG : MemLp (coneProfileGradient T c u) 2 (domainMeasure n (ball c r)) :=
    (memLp_congr_ae hDU).mp (Lp.memLp (∇ U))
  have hD := memLp_inner_normalize hG
  have hH := memLp_div_dist_of_h1 hn hr U hU
  have hρ : AEStronglyMeasurable (fun x : ℝ^n ↦ ‖x - c‖) (domainMeasure n (ball c r)) :=
    (continuous_id.sub continuous_const).norm.aestronglyMeasurable
  have hb : ∀ᵐ x ∂domainMeasure n (ball c r), ‖‖x - c‖‖ ≤ r := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    have hx' : ‖x - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hx
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hx'.le
  refine ⟨hD.integrable_sq.bdd_mul hρ hb, hw.integrable_mul hD, ?_⟩
  simpa only [IntegrableOn, pow_two, div_eq_mul_inv, mul_assoc, domainMeasure] using!
    hw.integrable_mul hH

end WaveEquation.ConeProfile
