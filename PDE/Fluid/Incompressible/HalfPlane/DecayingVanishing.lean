/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.DecayingVorticity
import PDE.Fluid.Incompressible.HalfPlane.OriginGradient
import PDE.Analysis.Calculus.HalfSpaceGluing
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Vanishing at the origin of the velocity of a decaying vorticity

For `Ψ = GreenFunction.quadrantPotential ω` with `ω` in the decaying class
(`IncompressibleFlow.IsDecayingVorticity`) we prove the vanishing statements of Chen and Hou,
Part I, after (4.8), with bounds in terms of weighted tails of `ω`. The hypotheses are
sufficient conditions on the source.

## Main results

* `abs_partialDeriv_quadrantPotential_sub_le`: if `|ω(y)| ≤ M |y|³` near the origin, then
  `|∂ⱼΨ(x) - (4/π) x_k ∫_{ℝ²₊₊} K₁ ω| ≤ (32/π) |x|³ ∫_{ℝ²₊₊, |y| ≥ 2|x|} |ω|/|y|⁴ + 128 M |x|⁴`
  for `(j, k) = (1, 0), (0, 1)`.
* `partialDeriv_quadrantPotential_sub_isBigO`: the tail stays bounded, so the velocity with the
  linear part removed is `O(|x|³)`.
* `partialDeriv_partialDeriv_quadrantPotential_sub_isBigO`: if the tangential derivative of `ω`
  within the closed half-plane vanishes to second order, then `∂₀∂₁Ψ - (4/π) ∫ K₁ ω` is
  `O(|x|²)` from the open half-plane: the compact part by the compact estimates, the far part by
  the Hessian remainder `GreenFunction.abs_partialDeriv_partialDeriv_quadrantPotential_ball_sub_le`.
* `partialDeriv_zero_partialDeriv_zero_quadrantPotential_isBigO`: under the same hypothesis,
  `∂₀²Ψ = O(|x|²)` from the open half-plane.
* `isBigO_closedUpper_of_isBigO_upper`: such bounds extend from the open to the closed half-plane
  for functions continuous there.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2, (4.8) and the display
  after it, pp. 39-40.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

section Cubic

variable {ω : ℝ^2 → ℝ} (hD : IsDecayingVorticity ω)
include hD


/-- The weighted tail `|ω(y)|/|y|⁴` is integrable on the quadrant outside `B(0, a)`. -/
private theorem integrableOn_abs_div_pow_four {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y ↦ |ω y| / ‖y‖ ^ 4) (GreenFunction.quadrant ∩ {y | a ≤ ‖y‖}) := by
  have hS : MeasurableSet (GreenFunction.quadrant ∩ {y : ℝ^2 | a ≤ ‖y‖}) :=
    measurableSet_quadrant.inter (measurableSet_le measurable_const measurable_norm)
  have h := (hD.integrableOn_abs_div_sq ha).const_mul (1 / a ^ 2)
  refine Integrable.mono' h ?_ ?_
  · exact (((((hD.contDiffOn.continuousOn.mono fun _ hy ↦ (le_of_lt hy.2 : (0 : ℝ) ≤ _)) :
      ContinuousOn ω GreenFunction.quadrant).mono inter_subset_left).abs.div
      (continuous_norm.pow 4).continuousOn fun y hy ↦ pow_ne_zero 4
        (norm_ne_zero_iff.mpr (by rintro rfl; simpa using hy.1.1))).aestronglyMeasurable hS)
  · filter_upwards [ae_restrict_mem hS] with y hy
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le ha hy.2
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 4)]
    have hya : a ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ ha.le hy.2 2
    rw [show ‖y‖ ^ 4 = ‖y‖ ^ 2 * ‖y‖ ^ 2 by ring, div_mul_eq_div_div,
      show 1 / a ^ 2 * (|ω y| / ‖y‖ ^ 2) = |ω y| / ‖y‖ ^ 2 / a ^ 2 by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hya

/-- **Part I, after (4.8), with a weighted tail, the estimate.** If `|ω(y)| ≤ M |y|³` on the
quadrant inside `B(0, 2|x|)`, then
`|∂ⱼΨ(x) - (4/π) x_k ∫_{ℝ²₊₊} K₁ ω| ≤ (32/π) |x|³ ∫_{ℝ²₊₊, |y| ≥ 2|x|} |ω|/|y|⁴ + 128 M |x|⁴`,
for `(j, k) = (1, 0)` and `(0, 1)` (the hypothesis `hker` is the far-field expansion of the
grouped velocity kernel). The tail replaces the `L¹` norm of the compact case. -/
theorem abs_partialDeriv_quadrantPotential_sub_le (j k : Fin 2)
    (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4)
    {M : ℝ} (hM0 : 0 ≤ M) {x : ℝ^2} (hx : 0 < ‖x‖)
    (hM : ∀ y ∈ GreenFunction.quadrant, ‖y‖ < 2 * ‖x‖ → |ω y| ≤ M * ‖y‖ ^ 3) :
    |(∂[j] (quadrantPotential ω)) x -
        4 / Real.pi * x k * ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y| ≤
      32 / Real.pi * ‖x‖ ^ 3 *
          (∫ y in GreenFunction.quadrant ∩ {y | 2 * ‖x‖ ≤ ‖y‖}, |ω y| / ‖y‖ ^ 4) +
        128 * M * ‖x‖ ^ 4 := by
  set r := ‖x‖ with hr_def
  have hπ : 0 < Real.pi := Real.pi_pos
  set Q := GreenFunction.quadrant
  set inv : ℝ^2 → ℝ := fun y ↦ ‖x - y‖⁻¹ + ‖x - 𝐑 0 y‖⁻¹ + ‖x - 𝐑 1 y‖⁻¹ + ‖x - -y‖⁻¹
  set b1 : ℝ^2 → ℝ := (Metric.ball 0 (2 * r)).indicator fun y ↦
    8 * M * r ^ 3 * (1 / (2 * Real.pi) * inv y) + 8 / Real.pi * M * r ^ 3 * ‖y‖⁻¹
  set b2 : ℝ^2 → ℝ := {y : ℝ^2 | 2 * r ≤ ‖y‖}.indicator fun y ↦
    32 / Real.pi * r ^ 3 * (|ω y| / ‖y‖ ^ 4)
  have hmb : MeasurableSet (Metric.ball (0 : ℝ^2) (2 * r)) := measurableSet_ball
  have hmF : MeasurableSet {y : ℝ^2 | 2 * r ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  have hpoles := fun (e : ℝ^2 ≃ₗᵢ[ℝ] ℝ^2) ↦ setIntegral_ball_norm_sub_comp_le e hx
  obtain ⟨i1, v1⟩ := hpoles (LinearIsometryEquiv.refl ℝ (ℝ^2))
  obtain ⟨i2, v2⟩ := hpoles (PDE.Common.coordinateReflectionLinearIsometryEquiv 0)
  obtain ⟨i3, v3⟩ := hpoles (PDE.Common.coordinateReflectionLinearIsometryEquiv 1)
  obtain ⟨i4, v4⟩ := hpoles (LinearIsometryEquiv.neg ℝ)
  simp only [LinearIsometryEquiv.coe_refl, id_eq, LinearIsometryEquiv.coe_neg] at i1 v1 i4 v4
  have v2' : ∫ y in Metric.ball 0 (2 * r), ‖x - 𝐑 0 y‖⁻¹ ≤ 6 * Real.pi * r := v2
  have v3' : ∫ y in Metric.ball 0 (2 * r), ‖x - 𝐑 1 y‖⁻¹ ≤ 6 * Real.pi * r := v3
  have i2' : IntegrableOn (fun y ↦ ‖x - 𝐑 0 y‖⁻¹) (Metric.ball 0 (2 * r)) := i2
  have i3' : IntegrableOn (fun y ↦ ‖x - 𝐑 1 y‖⁻¹) (Metric.ball 0 (2 * r)) := i3
  have hinv_int : IntegrableOn inv (Metric.ball 0 (2 * r)) := ((i1.add i2').add i3').add i4
  -- `|y|⁻¹` on the ball centred at the origin
  have h0int : IntegrableOn (fun y : ℝ^2 ↦ ‖y‖⁻¹) (Metric.ball 0 (2 * r)) := by
    simpa only [zero_sub, norm_neg] using integrableOn_ball_norm_sub_inv (0 : ℝ^2) (2 * r)
  have h0val : ∫ y in Metric.ball (0 : ℝ^2) (2 * r), ‖y‖⁻¹ = 2 * Real.pi * (2 * r) := by
    simpa only [zero_sub, norm_neg] using
      integral_ball_norm_sub_inv (0 : ℝ^2) (by positivity : (0 : ℝ) < 2 * r)
  have hb1int : IntegrableOn (fun y ↦ 8 * M * r ^ 3 * (1 / (2 * Real.pi) * inv y) +
      8 / Real.pi * M * r ^ 3 * ‖y‖⁻¹) (Metric.ball 0 (2 * r)) :=
    ((hinv_int.const_mul _).const_mul _).add (h0int.const_mul _)
  have hb1 : IntegrableOn b1 Q := (hb1int.integrable_indicator hmb).integrableOn
  have hb2 : IntegrableOn b2 Q := by
    refine (integrable_indicator_iff hmF).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict hmF]
    exact IntegrableOn.mono_set ((integrableOn_abs_div_pow_four hD (a := 2 * r)
      (by positivity)).const_mul _) fun y hy ↦ ⟨hy.2, hy.1⟩
  -- the pointwise bound
  have hpt : ∀ y ∈ Q, |(symmetrizedKernel (gradientKernel j) x y -
      4 / Real.pi * x k * hessianKernel 0 1 y) * ω y| ≤ b1 y + b2 y := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simpa using hy.1
    have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hb1n : 0 ≤ b1 y := indicator_nonneg (fun z _ ↦ by
      have : 0 ≤ inv z := by simp only [inv]; positivity
      positivity) y
    have hb2n : 0 ≤ b2 y := indicator_nonneg (fun _ _ ↦ by positivity) y
    rw [abs_mul]
    rcases lt_or_ge ‖y‖ (2 * r) with h1 | h1
    · have hb : b1 y = 8 * M * r ^ 3 * (1 / (2 * Real.pi) * inv y) +
          8 / Real.pi * M * r ^ 3 * ‖y‖⁻¹ := indicator_of_mem (mem_ball_zero_iff.mpr h1) _
      have hω := hM y hy h1
      have hK : |4 / Real.pi * x k * hessianKernel 0 1 y| ≤ 2 / Real.pi * r / ‖y‖ ^ 2 := by
        have hK1 : |hessianKernel 0 1 y| ≤ 1 / (2 * ‖y‖ ^ 2) := abs_hessianKernel_le 0 1 y
        have hcoord : |x k| ≤ r := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p := 2) x k
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
        exact (by gcongr : _ ≤ 4 / Real.pi * r * (1 / (2 * ‖y‖ ^ 2))).trans_eq (by field_simp; ring)
      have hsum := abs_symmetrizedKernel_gradientKernel_le_sum j x y
      have hy3 : ‖y‖ ^ 3 ≤ 8 * r ^ 3 :=
        (pow_le_pow_left₀ (norm_nonneg _) h1.le 3).trans_eq (by ring)
      have hyr : ‖y‖ ≤ 4 * r ^ 2 * ‖y‖⁻¹ := by
        rw [le_mul_inv_iff₀ hy']
        nlinarith
      calc |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| *
            |ω y|
          ≤ (1 / (2 * Real.pi) * inv y + 2 / Real.pi * r / ‖y‖ ^ 2) * (M * ‖y‖ ^ 3) := by
            gcongr
            exact (abs_sub _ _).trans (add_le_add hsum hK)
          _ = 1 / (2 * Real.pi) * inv y * M * ‖y‖ ^ 3 + 2 / Real.pi * M * r * ‖y‖ := by
            field_simp
          _ ≤ 1 / (2 * Real.pi) * inv y * M * (8 * r ^ 3) +
              2 / Real.pi * M * r * (4 * r ^ 2 * ‖y‖⁻¹) := by
            have : 0 ≤ inv y := by simp only [inv]; positivity
            gcongr
          _ = b1 y := by rw [hb]; ring
          _ ≤ b1 y + b2 y := by linarith
    · have hb : b2 y = 32 / Real.pi * r ^ 3 * (|ω y| / ‖y‖ ^ 4) :=
        indicator_of_mem (show y ∈ {y : ℝ^2 | 2 * r ≤ ‖y‖} from h1) _
      calc |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| *
            |ω y| ≤ 32 / Real.pi * r ^ 3 / ‖y‖ ^ 4 * |ω y| := by
            gcongr
            exact hker x y hy0 h1
        _ = b2 y := by rw [hb]; ring
        _ ≤ b1 y + b2 y := by linarith
  -- integrate
  have hg := integrableOn_symmetrizedKernel_gradientKernel hD j x
  have hK := (integrableOn_hessianKernel_mul_quadrant_of_decay hD).const_mul (4 / Real.pi * x k)
  have hdiff : (∂[j] (quadrantPotential ω)) x -
      4 / Real.pi * x k * ∫ y in Q, hessianKernel 0 1 y * ω y =
      ∫ y in Q, (symmetrizedKernel (gradientKernel j) x y -
        4 / Real.pi * x k * hessianKernel 0 1 y) * ω y := by
    rw [partialDeriv_quadrantPotential hD j x, ← integral_const_mul, ← integral_sub hg hK]
    refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
    ring
  rw [hdiff]
  have hsum : IntegrableOn (fun y ↦ b1 y + b2 y) Q := hb1.add hb2
  calc |∫ y in Q, (symmetrizedKernel (gradientKernel j) x y -
          4 / Real.pi * x k * hessianKernel 0 1 y) * ω y|
      ≤ ∫ y in Q, |(symmetrizedKernel (gradientKernel j) x y -
          4 / Real.pi * x k * hessianKernel 0 1 y) * ω y| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Q, (b1 y + b2 y) := integral_mono_of_nonneg (.of_forall fun y ↦ abs_nonneg _)
        hsum ((ae_restrict_mem measurableSet_quadrant).mono hpt)
    _ = (∫ y in Q, b1 y) + ∫ y in Q, b2 y := integral_add hb1 hb2
    _ ≤ _ := by
        have e2 : ∫ y in Q, b2 y = 32 / Real.pi * r ^ 3 *
            ∫ y in Q ∩ {y | 2 * r ≤ ‖y‖}, |ω y| / ‖y‖ ^ 4 := by
          rw [setIntegral_indicator hmF, integral_const_mul]
        have hinv_le : ∫ y in Metric.ball 0 (2 * r), inv y ≤ 24 * Real.pi * r := by
          have h1 := integral_add ((i1.add i2').add i3') i4
          have h2 := integral_add (i1.add i2') i3'
          have h3 := integral_add i1 i2'
          simp only [Pi.add_apply] at h1 h2 h3
          linarith
        have e1 : ∫ y in Q, b1 y ≤ 128 * M * r ^ 4 := by
          rw [setIntegral_indicator hmb]
          have hnn : ∀ z, 0 ≤ 8 * M * r ^ 3 * (1 / (2 * Real.pi) * inv z) +
              8 / Real.pi * M * r ^ 3 * ‖z‖⁻¹ := fun z ↦ by
            have : 0 ≤ inv z := by simp only [inv]; positivity
            positivity
          calc ∫ y in Q ∩ Metric.ball 0 (2 * r), (8 * M * r ^ 3 * (1 / (2 * Real.pi) * inv y) +
                8 / Real.pi * M * r ^ 3 * ‖y‖⁻¹)
              ≤ ∫ y in Metric.ball 0 (2 * r), (8 * M * r ^ 3 * (1 / (2 * Real.pi) * inv y) +
                8 / Real.pi * M * r ^ 3 * ‖y‖⁻¹) :=
                setIntegral_mono_set hb1int (Eventually.of_forall hnn)
                  (Eventually.of_forall inter_subset_right)
            _ = 8 * M * r ^ 3 * (1 / (2 * Real.pi) * ∫ y in Metric.ball 0 (2 * r), inv y) +
                8 / Real.pi * M * r ^ 3 * ∫ y in Metric.ball (0 : ℝ^2) (2 * r), ‖y‖⁻¹ := by
                rw [integral_add ((hinv_int.const_mul _).const_mul _) (h0int.const_mul _),
                  integral_const_mul, integral_const_mul, integral_const_mul]
            _ ≤ 8 * M * r ^ 3 * (1 / (2 * Real.pi) * (24 * Real.pi * r)) +
                8 / Real.pi * M * r ^ 3 * (2 * Real.pi * (2 * r)) := by
                rw [h0val]
                gcongr
            _ = 128 * M * r ^ 4 := by field_simp; ring
        rw [e2]
        linarith

/-- The weighted tail `∫_{ℝ²₊₊, |y| ≥ 2|x|} |ω|/|y|⁴` stays bounded as `x → 0` when
`|ω(y)| ≤ M |y|³` on the quadrant inside `B(0, δ)`. -/
private theorem exists_tail_four_le {M δ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ)
    (hM : ∀ y ∈ GreenFunction.quadrant, ‖y‖ < δ → |ω y| ≤ M * ‖y‖ ^ 3) :
    ∃ K, ∀ x : ℝ^2, 0 < ‖x‖ →
      ∫ y in GreenFunction.quadrant ∩ {y | 2 * ‖x‖ ≤ ‖y‖}, |ω y| / ‖y‖ ^ 4 ≤ K := by
  set T := ∫ y in GreenFunction.quadrant ∩ {y | δ ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2
  refine ⟨M * (2 * Real.pi * δ) + T / δ ^ 2, fun x hx ↦ ?_⟩
  set S := GreenFunction.quadrant ∩ {y : ℝ^2 | 2 * ‖x‖ ≤ ‖y‖}
  have hS : MeasurableSet S :=
    measurableSet_quadrant.inter (measurableSet_le measurable_const measurable_norm)
  have hmδ : MeasurableSet (Metric.ball (0 : ℝ^2) δ) := measurableSet_ball
  have hmF : MeasurableSet {y : ℝ^2 | δ ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  have h0int : IntegrableOn (fun y : ℝ^2 ↦ ‖y‖⁻¹) (Metric.ball 0 δ) := by
    simpa only [zero_sub, norm_neg] using integrableOn_ball_norm_sub_inv (0 : ℝ^2) δ
  have h0val : ∫ y in Metric.ball (0 : ℝ^2) δ, ‖y‖⁻¹ = 2 * Real.pi * δ := by
    simpa only [zero_sub, norm_neg] using integral_ball_norm_sub_inv (0 : ℝ^2) hδ
  set c1 : ℝ^2 → ℝ := (Metric.ball 0 δ).indicator fun y ↦ M * ‖y‖⁻¹
  set c2 : ℝ^2 → ℝ := {y : ℝ^2 | δ ≤ ‖y‖}.indicator fun y ↦ 1 / δ ^ 2 * (|ω y| / ‖y‖ ^ 2)
  have hc1 : IntegrableOn c1 S :=
    (IntegrableOn.integrable_indicator (h0int.const_mul M) hmδ).integrableOn
  have hc2 : IntegrableOn c2 S := by
    refine (integrable_indicator_iff hmF).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict hmF]
    exact IntegrableOn.mono_set ((hD.integrableOn_abs_div_sq hδ).const_mul _)
      fun y hy ↦ ⟨hy.2.1, hy.1⟩
  have hpt : ∀ y ∈ S, |ω y| / ‖y‖ ^ 4 ≤ c1 y + c2 y := by
    intro y hy
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hy.2
    have hc1n : 0 ≤ c1 y := indicator_nonneg (fun _ _ ↦ by positivity) y
    have hc2n : 0 ≤ c2 y := indicator_nonneg (fun _ _ ↦ by positivity) y
    rcases lt_or_ge ‖y‖ δ with h | h
    · have hb : c1 y = M * ‖y‖⁻¹ := indicator_of_mem (mem_ball_zero_iff.mpr h) _
      have := hM y hy.1 h
      calc |ω y| / ‖y‖ ^ 4 ≤ M * ‖y‖ ^ 3 / ‖y‖ ^ 4 := by gcongr
        _ = M * ‖y‖⁻¹ := by field_simp
        _ = c1 y := hb.symm
        _ ≤ c1 y + c2 y := by linarith
    · have hb : c2 y = 1 / δ ^ 2 * (|ω y| / ‖y‖ ^ 2) :=
        indicator_of_mem (show y ∈ {y : ℝ^2 | δ ≤ ‖y‖} from h) _
      have hδy : δ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hδ.le h 2
      calc |ω y| / ‖y‖ ^ 4 = |ω y| / ‖y‖ ^ 2 / ‖y‖ ^ 2 := by
            rw [div_div, ← pow_add]
        _ ≤ |ω y| / ‖y‖ ^ 2 / δ ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hδy
        _ = c2 y := by rw [hb]; ring
        _ ≤ c1 y + c2 y := by linarith
  calc ∫ y in S, |ω y| / ‖y‖ ^ 4 ≤ ∫ y in S, (c1 y + c2 y) :=
        integral_mono_of_nonneg (.of_forall fun y ↦ by positivity) (hc1.add hc2)
          ((ae_restrict_mem hS).mono hpt)
    _ = (∫ y in S, c1 y) + ∫ y in S, c2 y := integral_add hc1 hc2
    _ ≤ M * (2 * Real.pi * δ) + T / δ ^ 2 := by
        have e1 : ∫ y in S, c1 y ≤ M * (2 * Real.pi * δ) := by
          rw [setIntegral_indicator hmδ, ← h0val, ← integral_const_mul]
          exact setIntegral_mono_set (h0int.const_mul M)
            (Eventually.of_forall fun y ↦ by positivity)
            (Eventually.of_forall inter_subset_right)
        have e2 : ∫ y in S, c2 y ≤ T / δ ^ 2 := by
          rw [setIntegral_indicator hmF, integral_const_mul]
          have hsub : S ∩ {y : ℝ^2 | δ ≤ ‖y‖} ⊆ GreenFunction.quadrant ∩ {y | δ ≤ ‖y‖} :=
            fun y hy ↦ ⟨hy.1.1, hy.2⟩
          have hmono : ∫ y in S ∩ {y : ℝ^2 | δ ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2 ≤ T :=
            setIntegral_mono_set (hD.integrableOn_abs_div_sq hδ)
              (Eventually.of_forall fun y ↦ by positivity) (Eventually.of_forall hsub)
          exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans_eq (one_div_mul_eq_div _ _)
        linarith

/-- **Part I, after (4.8), for decaying data**: if `|ω(y)| ≤ M |y|³` on the quadrant near the
origin, then `∂ⱼΨ(x) - (4/π) x_k ∫_{ℝ²₊₊} K₁ ω = O(|x|³)` at the origin, `(j, k) = (1, 0)`,
`(0, 1)`. -/
theorem partialDeriv_quadrantPotential_sub_isBigO (j k : Fin 2)
    (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4)
    {M δ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ)
    (hM : ∀ y ∈ GreenFunction.quadrant, ‖y‖ < δ → |ω y| ≤ M * ‖y‖ ^ 3) :
    (fun x ↦ (∂[j] (quadrantPotential ω)) x -
        4 / Real.pi * x k * ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 3 := by
  obtain ⟨K, hK⟩ := exists_tail_four_le hD hM0 hδ hM
  refine Asymptotics.IsBigO.of_bound (32 / Real.pi * K + 128 * M * δ) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^2) (by positivity : (0 : ℝ) < δ / 2)] with x hx
  rw [mem_ball_zero_iff] at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 3)]
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · -- at the origin the grouped kernel vanishes
    have hx0 : x = 0 := norm_eq_zero.mp h0.symm
    subst hx0
    have hz : ∀ y : ℝ^2, y ≠ 0 → symmetrizedKernel (gradientKernel j) 0 y = 0 := fun y hy ↦ by
      simpa using hker 0 y hy (by simp)
    rw [partialDeriv_quadrantPotential hD j 0]
    have hint : ∫ y in GreenFunction.quadrant, symmetrizedKernel (gradientKernel j) 0 y * ω y =
        0 := by
      refine (setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_).trans
        (integral_zero _ _)
      have hy0 : y ≠ 0 := by rintro rfl; simpa using hy.1
      simp [hz y hy0]
    simp [hint]
  · have hM' : ∀ y ∈ GreenFunction.quadrant, ‖y‖ < 2 * ‖x‖ → |ω y| ≤ M * ‖y‖ ^ 3 :=
      fun y hy h ↦ hM y hy (by linarith)
    have h := abs_partialDeriv_quadrantPotential_sub_le hD j k hker hM0 hpos hM'
    have hT := hK x hpos
    have hx4 : ‖x‖ ^ 4 ≤ δ * ‖x‖ ^ 3 := by
      rw [show ‖x‖ ^ 4 = ‖x‖ * ‖x‖ ^ 3 by ring]
      gcongr
      linarith
    exact h.trans ((by gcongr : _ ≤ 32 / Real.pi * ‖x‖ ^ 3 * K + 128 * M * (δ * ‖x‖ ^ 3)).trans_eq
      (by ring))

end Cubic

/-! ### Quadratic vanishing of the velocity gradient -/

section GradientVanishing

/-- A continuous compactly supported field that is `O(|x|ⁿ)` at the origin on the closed upper
half-plane is bounded by `M |y|ⁿ` on the whole closed upper half-plane. -/
theorem exists_abs_le_mul_pow (n : ℕ) {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (h : f =O[𝓝[{x | 0 ≤ x 1}] 0] fun x ↦ ‖x‖ ^ n) :
    ∃ M, ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * ‖y‖ ^ n := by
  obtain ⟨C, hC⟩ := h.bound
  rw [Filter.Eventually, mem_nhdsWithin] at hC
  obtain ⟨U, hU, h0U, hUsub⟩ := hC
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hc
  refine ⟨max |C| (B / (δ / 2) ^ n), fun y hy ↦ ?_⟩
  by_cases hyδ : ‖y‖ < δ / 2
  · have hmem : y ∈ U ∩ {x : ℝ^2 | 0 ≤ x 1} :=
      ⟨hball (by rw [Metric.mem_ball, dist_zero_right]; linarith), hy⟩
    have := hUsub hmem
    simp only [mem_ofPred_eq, Real.norm_eq_abs, norm_pow, abs_norm] at this
    calc |f y| ≤ C * ‖y‖ ^ n := this
      _ ≤ |C| * ‖y‖ ^ n := by gcongr; exact le_abs_self C
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hge : δ / 2 ≤ ‖y‖ := le_of_not_gt hyδ
    have hpos : 0 < (δ / 2) ^ n := by positivity
    calc |f y| ≤ B := by simpa [Real.norm_eq_abs] using hB y
      _ = B / (δ / 2) ^ n * (δ / 2) ^ n := by field_simp
      _ ≤ max |C| (B / (δ / 2) ^ n) * ‖y‖ ^ n := by
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
          gcongr
          exact le_max_right _ _

/-- A bound `O(|x|ⁿ)` from the open upper half-plane extends to the closed half-plane for a
function continuous on the closed half-plane. -/
theorem isBigO_closedUpper_of_isBigO_upper {f : ℝ^2 → ℝ} {n : ℕ}
    (hf : ContinuousOn f {x | 0 ≤ x 1})
    (h : f =O[𝓝[HalfSpace.upper 2] 0] fun x ↦ ‖x‖ ^ n) :
    f =O[𝓝[{x | 0 ≤ x 1}] 0] fun x ↦ ‖x‖ ^ n := by
  obtain ⟨C, hC⟩ := h.bound
  rw [Filter.Eventually, mem_nhdsWithin] at hC
  obtain ⟨U, hU, h0U, hUsub⟩ := hC
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  refine Asymptotics.IsBigO.of_bound C ?_
  rw [Filter.Eventually, mem_nhdsWithin]
  refine ⟨Metric.ball 0 δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun x hx ↦ ?_⟩
  obtain ⟨hxδ, hxH⟩ := hx
  have hxH' : 0 ≤ x 1 := hxH
  -- approach `x` from the open half-plane along `x + t e₁`
  set e : ℝ^2 := EuclideanSpace.single 1 1
  have hcont : Continuous fun t : ℝ ↦ x + t • e := continuous_const.add
    (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun t : ℝ ↦ x + t • e) (𝓝[>] 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hmemH : ∀ t : ℝ, 0 < t → x + t • e ∈ HalfSpace.upper 2 := fun t ht ↦ by
    change 0 < (x + t • e) 1
    have he1 : e 1 = 1 := by simp [e]
    simp only [PiLp.add_apply, PiLp.smul_apply, he1, smul_eq_mul, mul_one]
    linarith
  have hball' : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • e ∈ Metric.ball (0 : ℝ^2) δ :=
    hlim.eventually (Metric.isOpen_ball.mem_nhds hxδ)
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖f (x + t • e)‖ ≤ C * ‖‖x + t • e‖ ^ n‖ := by
    filter_upwards [hball', self_mem_nhdsWithin] with t ht htpos
    exact hUsub ⟨hball ht, hmemH t htpos⟩
  have hfx : Tendsto (fun t : ℝ ↦ f (x + t • e)) (𝓝[>] 0) (𝓝 (f x)) := by
    have hsub : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • e ∈ {y : ℝ^2 | 0 ≤ y 1} :=
      eventually_nhdsWithin_of_forall fun t ht ↦ (le_of_lt (hmemH t ht) : 0 ≤ (x + t • e) 1)
    exact (hf x hxH').tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hsub⟩)
  have hrhs : Tendsto (fun t : ℝ ↦ C * ‖‖x + t • e‖ ^ n‖) (𝓝[>] 0) (𝓝 (C * ‖‖x‖ ^ n‖)) := by
    have hc2 : Continuous fun t : ℝ ↦ C * ‖‖x + t • e‖ ^ n‖ :=
      continuous_const.mul ((continuous_norm.comp hcont).pow n).norm
    simpa only [zero_smul, add_zero] using (hc2.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hfx.norm hrhs hbound

variable {ω : ℝ^2 → ℝ} (hD : IsDecayingVorticity ω)
include hD

omit hD in
/-- The strain value as the sum of the compact and far contributions. -/
private theorem mixed_origin_eq {R : ℝ} (hR : 0 < R) {F G : ℝ^2 → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hFodd : ∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y)
    (hfar : IsQuadrantFarDensity G R) (hFG : ∀ y ∈ GreenFunction.quadrant, F y + G y = ω y) :
    (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential F))) 0 +
        (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential (G)))) 0 =
      4 / Real.pi * ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y := by
  have hxR : ‖(0 : ℝ^2)‖ < R / 2 := by rw [norm_zero]; linarith
  have hk (y : ℝ^2) : symmetrizedKernel (hessianKernel 1 0) 0 y = 4 * hessianKernel 0 1 y := by
    rw [show hessianKernel 1 0 = hessianKernel 0 1 from funext hessianKernel_one_zero,
      symmetrizedKernel_zero_one_origin]
  have hIF := integrableOn_hessianKernel_mul_quadrant (hF.of_le (by norm_num)) hFc hFodd
  have hIfar : IntegrableOn (fun y ↦ hessianKernel 0 1 y * G y)
      GreenFunction.quadrant := by
    have h4 : IntegrableOn (fun y ↦ 1 / 4 *
        (symmetrizedKernel (hessianKernel 1 0) 0 y * G y)) GreenFunction.quadrant :=
      (integrableOn_symmetrizedKernel_hessianKernel_of_far hfar 1 0 hxR).const_mul (1 / 4)
    exact h4.congr_fun (fun y _ ↦ by simp only [hk]; ring) measurableSet_quadrant
  have h1 := pi_mul_partialDeriv_partialDeriv_zero_origin hF hFc hFodd
  have hsplit : ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y =
      (∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * F y) +
        ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * G y := by
    rw [← integral_add hIF hIfar]
    refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
    rw [← hFG y hy]
    ring
  rw [partialDeriv_partialDeriv_quadrantPotential_ball hfar 1 0 hxR]
  simp only [hk]
  simp only [mul_assoc, integral_const_mul]
  rw [hsplit]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  linarith [h1]

omit hD in
/-- The tangential derivative of the compact part is the within derivative of `ω` near the
origin. -/
private theorem partialDeriv_zero_compact_isBigO {R : ℝ} (hR : 0 < R) {F : ℝ^2 → ℝ}
    (hF : ContDiff ℝ 2 F) (hFω : ∀ y, 0 ≤ y 1 → ‖y‖ < R → F y = ω y)
    (h2 : (PDE.partialDerivWithin 0 ω {y | 0 ≤ y 1}) =O[𝓝[{y | 0 ≤ y 1}] 0]
      fun y ↦ ‖y‖ ^ 2) :
    (∂[(0 : Fin 2)] F) =O[𝓝[{y | 0 ≤ y 1}] 0] fun y ↦ ‖y‖ ^ 2 := by
  refine h2.congr' ?_ (EventuallyEq.refl _ _)
  have hU : UniqueDiffOn ℝ {y : ℝ^2 | 0 ≤ y 1} := PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Metric.ball_mem_nhds (0 : ℝ^2) hR)] with y hyH hyB
  have hyB' : ‖y‖ < R := mem_ball_zero_iff.mp hyB
  rw [← (hF.differentiable (by norm_num) y).partialDerivWithin_eq 0 (hU y hyH)]
  unfold PDE.partialDerivWithin
  congr 1
  refine Filter.EventuallyEq.fderivWithin_eq ?_ (hFω y hyH hyB').symm
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Metric.isOpen_ball.mem_nhds hyB)] with z hzH hz
  exact (hFω z hzH (mem_ball_zero_iff.mp hz)).symm

omit hD in
/-- The bound shared by the two second derivatives below:
`A r² + 16 M r³ + c r² T ≤ (A + c T + 16 |M| R) r²` for `0 ≤ r ≤ R`. -/
private theorem add_le_mul_sq {A T M R c r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    A * r ^ 2 + 16 * M * r ^ 3 + c * r ^ 2 * T ≤ (A + c * T + 16 * |M| * R) * r ^ 2 := by
  have h1 : M * r ^ 3 ≤ |M| * r ^ 3 := by gcongr; exact le_abs_self M
  have h2 : |M| * r ^ 3 ≤ |M| * (R * r ^ 2) := by rw [pow_succ']; gcongr
  linarith

/-- **`∇ũ = O(|x|²)`, the mixed derivative, for decaying data**: if the tangential derivative of `ω`
within the closed half-plane vanishes to second order, then `∂₀∂₁Ψ(x) - (4/π) ∫ K₁ ω = O(|x|²)` from
the open upper half-plane. -/
theorem partialDeriv_partialDeriv_quadrantPotential_sub_isBigO
    (h2 : (PDE.partialDerivWithin 0 ω {y | 0 ≤ y 1}) =O[𝓝[{y | 0 ≤ y 1}] 0]
      fun y ↦ ‖y‖ ^ 2) :
    (fun x ↦ (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential ω))) x -
        4 / Real.pi * ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y)
      =O[𝓝[HalfSpace.upper 2] 0] fun x ↦ ‖x‖ ^ 2 := by
  set R : ℝ := 2 with hR_def
  have hR : (0 : ℝ) < R := by norm_num [hR_def]
  obtain ⟨F, G, hF, hFc, hFodd, hFω, hfar, hFG, hdec⟩ := hD.exists_decomposition_ball hR
  obtain ⟨M, hM⟩ := exists_abs_le_mul_pow 2 (ContDiff.continuous_partialDeriv (hF.of_le (by
      norm_num)) (0 : Fin 2))
    (hFc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ)))
    (partialDeriv_zero_compact_isBigO hR hF hFω h2)
  set A := 16 / Real.pi * (2 * Real.pi * M +
    ∫ y, |oddHalfSpaceExtension (∂[(0 : Fin 2)] F) y|)
  set T := ∫ y in GreenFunction.quadrant, |G y| / ‖y‖ ^ 4
  refine Asymptotics.IsBigO.of_bound (A + 104 / (9 * Real.pi) * T + 16 * |M| * R) ?_
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Metric.ball_mem_nhds (0 : ℝ^2) hR2)] with x hxU hxB
  have hxB' : ‖x‖ < R / 2 := mem_ball_zero_iff.mp hxB
  have hloc : quadrantPotential ω =ᶠ[𝓝 x]
      fun z ↦ halfSpaceGreenPotential F z + quadrantPotential (G) z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxB] with z hz
    exact hdec z (mem_ball_zero_iff.mp hz)
  have hGreg := (halfSpaceGreenPotential_local_poisson hF.continuous hFc hxU hF.contDiffAt).1
  have hsum : (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential ω))) x =
      (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential F))) x +
        (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential (G)))) x := by
    rw [PDE.partialDeriv_congr_nhds 0 (hloc.partialDeriv 1),
      partialDeriv_partialDeriv_add 1 0 hGreg (((contDiffOn_quadrantPotential_ball hfar).contDiffAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxB')))),
      PDE.partialDeriv_partialDeriv_comm_at 0 1 hGreg]
  have hc := abs_partialDeriv_one_partialDeriv_zero_sub_le hF hFc hFodd hM x
  have hf := abs_partialDeriv_partialDeriv_quadrantPotential_ball_sub_le hfar 1 0 hxB'
  have hval := mixed_origin_eq hR hF hFc hFodd hfar hFG
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2),
    hsum, ← hval, add_sub_add_comm]
  exact (abs_add_le _ _).trans
    ((add_le_add hc hf).trans (add_le_mul_sq (norm_nonneg x) (by linarith : ‖x‖ ≤ R)))

/-- **`∇ũ = O(|x|²)`, the tangential second derivative, for decaying data**: under the same
hypothesis, `∂₀²Ψ = O(|x|²)` from the open upper half-plane. -/
theorem partialDeriv_zero_partialDeriv_zero_quadrantPotential_isBigO
    (h2 : (PDE.partialDerivWithin 0 ω {y | 0 ≤ y 1}) =O[𝓝[{y | 0 ≤ y 1}] 0]
      fun y ↦ ‖y‖ ^ 2) :
    (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (quadrantPotential ω))) =O[𝓝[HalfSpace.upper 2] 0]
      fun x ↦ ‖x‖ ^ 2 := by
  set R : ℝ := 2 with hR_def
  have hR : (0 : ℝ) < R := by norm_num [hR_def]
  obtain ⟨F, G, hF, hFc, hFodd, hFω, hfar, hFG, hdec⟩ := hD.exists_decomposition_ball hR
  obtain ⟨M, hM⟩ := exists_abs_le_mul_pow 2 (ContDiff.continuous_partialDeriv (hF.of_le (by
      norm_num)) (0 : Fin 2))
    (hFc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ)))
    (partialDeriv_zero_compact_isBigO hR hF hFω h2)
  set A := 16 / Real.pi * (2 * Real.pi * M +
    ∫ y, |oddHalfSpaceExtension (∂[(0 : Fin 2)] F) y|)
  set T := ∫ y in GreenFunction.quadrant, |G y| / ‖y‖ ^ 4
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  have hfar0 : (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (quadrantPotential (G)))) 0 = 0 := by
    rw [partialDeriv_partialDeriv_quadrantPotential_ball hfar 0 0 (by rw [norm_zero]; linarith)]
    simp [symmetrizedKernel_zero_zero_origin]
  refine Asymptotics.IsBigO.of_bound (A + 104 / (9 * Real.pi) * T + 16 * |M| * R) ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Metric.ball_mem_nhds (0 : ℝ^2) hR2)] with x hxU hxB
  have hxB' : ‖x‖ < R / 2 := mem_ball_zero_iff.mp hxB
  have hloc : quadrantPotential ω =ᶠ[𝓝 x]
      fun z ↦ halfSpaceGreenPotential F z + quadrantPotential (G) z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxB] with z hz
    exact hdec z (mem_ball_zero_iff.mp hz)
  have hGreg := (halfSpaceGreenPotential_local_poisson hF.continuous hFc hxU hF.contDiffAt).1
  have hsum : (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (quadrantPotential ω))) x =
      (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential F))) x +
        (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (quadrantPotential (G)))) x := by
    rw [PDE.partialDeriv_congr_nhds 0 (hloc.partialDeriv 0),
      partialDeriv_partialDeriv_add 0 0 hGreg (((contDiffOn_quadrantPotential_ball hfar).contDiffAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxB'))))]
  have hc := abs_partialDeriv_zero_partialDeriv_zero_le hF hFc hFodd hM x
  have hf := abs_partialDeriv_partialDeriv_quadrantPotential_ball_sub_le hfar 0 0 hxB'
  rw [hfar0, sub_zero] at hf
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2),
    hsum]
  exact (abs_add_le _ _).trans
    ((add_le_add hc hf).trans (add_le_mul_sq (norm_nonneg x) (by linarith : ‖x‖ ≤ R)))

end GradientVanishing

end IncompressibleFlow
