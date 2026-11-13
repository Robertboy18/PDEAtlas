/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.PotentialBound
public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.Weight
import CAS.ExactTactic

/-!
# The quintic slice estimate from cone densities

Weighted Hölder on the three-dimensional ball controls the inverse-radius term
in the radial square. Local energy conservation supplies all integrability
hypotheses through the cone profile. The resulting constant is independent of
the interior time slice.

This is the Hölder step of (15) in the proof of Evans, §12.4, Theorem 2, which Evans carries out on
the cone with `∫_Γ |x|^{-3/2} dS = C T^{3/2}` and which we carry out on the ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, step 4, equation (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis NormedSpace Metric
open scoped RealInnerProductSpace Topology

namespace WaveEquation

private theorem weighted_square_le {w : ℝ^3 → ℝ} {G : ℝ^3 → ℝ^3} {c : ℝ^3} {r : ℝ} (hr : 0 < r)
    (hG : IntegrableOn (fun x ↦ ‖G x‖ ^ 2) (ball c r))
    (hweight : IntegrableOn (fun x ↦ w x ^ 2 / ‖x - c‖) (ball c r)) :
    (∫ x in ball c r, ‖x - c‖ * (⟪G x, normalize (x - c)⟫ + w x / ‖x - c‖) ^ 2) ≤
      2 * r * (∫ x in ball c r, ‖G x‖ ^ 2) + 2 * (∫ x in ball c r, w x ^ 2 / ‖x - c‖) := by
  have hbound : ∀ᵐ x ∂volume.restrict (ball c r), ‖x - c‖ *
      (⟪G x, normalize (x - c)⟫ + w x / ‖x - c‖) ^ 2 ≤
        2 * r * ‖G x‖ ^ 2 + 2 * (w x ^ 2 / ‖x - c‖) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne c)] with x hx hne
    have hρ : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hρr : ‖x - c‖ ≤ r := (by simpa only [mem_ball, dist_eq_norm] using hx : ‖x - c‖ < r).le
    have hi := abs_real_inner_le_norm (G x) (normalize (x - c))
    rw [norm_normalize (sub_ne_zero.mpr hne), mul_one] at hi
    have hd : ⟪G x, normalize (x - c)⟫ ^ 2 ≤ ‖G x‖ ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hi
    calc
      _ ≤ ‖x - c‖ * (2 * (⟪G x, normalize (x - c)⟫ ^ 2 +
          (w x / ‖x - c‖) ^ 2)) := mul_le_mul_of_nonneg_left add_sq_le hρ.le
      _ = 2 * ‖x - c‖ * ⟪G x, normalize (x - c)⟫ ^ 2 +
          2 * (w x ^ 2 / ‖x - c‖) := by
        generalize ‖x - c‖ = ρ at hρ ⊢
        generalize ⟪G x, normalize (x - c)⟫ = d
        generalize w x = z
        cas using ne_of_gt hρ
      _ ≤ _ := by gcongr
  have h := integral_mono_of_nonneg (ae_of_all _ fun x ↦ mul_nonneg (norm_nonneg _) (sq_nonneg _))
    ((hG.const_mul (2 * r)).add (hweight.const_mul 2)) hbound
  simpa only [Pi.add_apply, integral_add (hG.const_mul (2 * r)) (hweight.const_mul 2),
    integral_const_mul] using h

/-- The shrinking-ball sixth-power integral is bounded by the two
integrable cone densities. The constant is independent of the time slice. -/
theorem integral_quinticSlice_le_coneDensities_of_wave {u : ℝ^4 → ℝ} {s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    (∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) ≤
      12 * (∫ x in Metric.ball c (T - s), ‖coneProfileGradient T c u x‖ ^ 2) +
        12 * (∫ x in Metric.ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) *
          (∫ x in Metric.ball c (T - s), coneProfile T c u x ^ 6) ^ (1 / 3 : ℝ) := by
  have hr : 0 < T - s := sub_pos.mpr hsT
  have hwave' := fun t (ht : t ∈ Ico s T) ↦ hwave t ⟨hs.trans_le ht.1, ht.2⟩
  obtain ⟨hG, hW⟩ := ConeProfile.integrable_densities_of_wave hu c hs hwave'
  obtain ⟨_, _, hweight⟩ := ConeProfile.integrable_radial_terms (by omega : 3 ≤ 3) hr
    (fun _ hx hne ↦ ConeProfile.contDiffAt_cone_of_band hu hs c
      (Metric.ball_subset_closedBall hx) hne) hG hW
  have hholder := ConeProfile.integral_sq_div_dist_le_of_wave hu c hs hsT hwave'
  simp only [(show Even 6 by decide).pow_abs] at hholder
  have hsquare := weighted_square_le hr hG hweight
  have hpotential := ballIntegral_quinticPotential_le_weightedSquare_of_wave hu c hs hsT hwave
  have hbound := hpotential.trans (hsquare.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hholder (by norm_num : (0 : ℝ) ≤ 2))))
  have hfactor (a b k : ℝ) : 2 * (T - s) * a + 2 * (b * (k * (T - s))) =
        (T - s) / 6 * (12 * a + 12 * k * b) := by cas
  rw [hfactor] at hbound
  have hleft (a : ℝ) : (T - s) * a / 6 = (T - s) / 6 * a := by cas
  rw [hleft] at hbound
  exact le_of_mul_le_mul_left hbound (div_pos hr (by norm_num : (0 : ℝ) < 6))

end WaveEquation
