/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.BallPullback
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration
import PDE.Elliptic.Regularity.Boundary.ConcreteUnitBallAtlas
import PDE.Spaces.Sobolev.GraphSpace.Norms
import CAS.ExactTactic

/-!
# Radius-uniform Sobolev control for cone traces

The three-dimensional H¹ → L⁶ estimate on the unit ball, followed by the affine weak pullback, gives
the radius-independent estimate `‖u‖₆ ≤ C (‖Du‖₂ + r⁻¹ ‖u‖₂)`. There is no boundary condition. This
is the Sobolev inequality (§5.6.3) in step 3 of the proof of Theorem 3 of Evans, §12.3.3, with a
constant uniform in the radius of the ball `B(x, t)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3; §12.3.3, step 3 of the proof of Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The full H¹ unit ball embeds into L⁶, without a trace restriction. -/
theorem memLp_six_unitBall (U : H¹(ball (0 : ℝ^3) 1)) :
    MemLp (baseRepresentative U) 6 (domainMeasure 3 (ball 0 1)) := by
  let : Boundary.C1ExtensionAtlas 3 (ball (0 : ℝ^3) 1) :=
    (Boundary.Atlas.UnitBall.ConcreteAtlas.c2BoundaryAtlas 3).toC1ExtensionAtlas
  have h := Embedding.base_memLp_iterated (n := 3) (j := 1) (p := 2)
    (by norm_num) (by norm_num) U
  norm_num [baseRepresentative, Inequalities.higherOrderExponent] at h ⊢
  exact h

/-- Translation and dilation give L⁶ membership for every positive-radius ball. -/
theorem memLp_six_ball (x : ℝ^3) {r : ℝ} (hr : 0 < r) (U : H¹(ball x r)) :
    MemLp (baseRepresentative U) 6 (domainMeasure 3 (ball x r)) := by
  obtain ⟨V, hbase, _⟩ := MeanScaling.exists_ballPullback x hr U
  have he : MeasurableEmbedding (MeanScaling.ballHomeomorph x hr) :=
    (MeanScaling.ballHomeomorph x hr).toMeasurableEquiv.measurableEmbedding
  have hmap := he.memLp_map_measure_iff.mpr ((memLp_congr_ae hbase).mp (memLp_six_unitBall V))
  change MemLp (baseRepresentative U) 6
    ((volume.restrict (ball (0 : ℝ^3) 1)).map (MeanScaling.ballHomeomorph x hr)) at hmap
  rw [MeanScaling.map_ball_volume] at hmap
  have hc : ENNReal.ofReal (r ^ 3)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr 3))).ne'
  have hscaled := hmap.smul_measure (c := (ENNReal.ofReal (r ^ 3)⁻¹)⁻¹) (ENNReal.inv_ne_top.mpr hc)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul] using hscaled

/-- A single unit-ball Sobolev constant controls the separate function and gradient norms. -/
theorem exists_sobolev_bound_unitBall :
    ∃ C : ℝ, 0 < C ∧
      ∀ U : H¹(ball (0 : ℝ^3) 1),
        (eLpNorm (baseRepresentative U) 6 (domainMeasure 3 (ball 0 1))).toReal ≤
        C * (‖wkpBaseCoordinateCLM U‖ + ‖∇ U‖) := by
  have : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
  let J := Inequalities.embeddingCLMOfMemLp memLp_six_unitBall
  refine ⟨3 * (‖J‖ + 1), by positivity, fun U ↦ ?_⟩
  have hnorm : ‖U‖ ≤ ‖wkpBaseCoordinateCLM U‖ + 3 * ‖∇ U‖ := by
    apply (ambient_norm_le_base_add_sum_deriv U.val).trans
    apply add_le_add le_rfl
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      norm_derivCoordinate_le_wkpGradientCLM U i
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using hsum
  change ‖J U‖ ≤ _
  have hJ := J.le_opNorm U
  have hmul := mul_le_mul_of_nonneg_left hnorm (norm_nonneg J)
  nlinarith [norm_nonneg (wkpBaseCoordinateCLM U), norm_nonneg (∇ U), norm_nonneg J]

/-- In three dimensions the L² scaling factor is the L⁶ factor divided by the radius. -/
theorem normFactor_two_eq_six_div {r : ℝ} (hr : 0 < r) :
    MeanScaling.normFactor 3 r 2 = MeanScaling.normFactor 3 r 6 / r := by
  simp only [MeanScaling.normFactor, ← ENNReal.toReal_rpow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le 3))]
  cas using hr

/-- The ball Sobolev estimate has one constant for every center and radius.
The affine pullback is constructed from arbitrary weak H¹ data. -/
theorem exists_sobolev_bound_ball :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ℝ^3) (r : ℝ), 0 < r → ∀ U : H¹(ball x r),
        (eLpNorm (baseRepresentative U) 6 (domainMeasure 3 (ball x r))).toReal ≤
        C * (‖∇ U‖ + ‖wkpBaseCoordinateCLM U‖ / r) := by
  obtain ⟨C, hC, hS⟩ := exists_sobolev_bound_unitBall
  refine ⟨C, hC, fun x r hr U ↦ ?_⟩
  obtain ⟨V, hbase, hgrad⟩ := MeanScaling.exists_ballPullback x hr U
  have hB : ‖wkpBaseCoordinateCLM V‖ =
      MeanScaling.normFactor 3 r 2 * ‖wkpBaseCoordinateCLM U‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae hbase, Lp.norm_def]
    exact MeanScaling.eLpNorm_comp_ballHomeomorph x hr 2 _
  have hG : ‖∇ V‖ = MeanScaling.normFactor 3 r 2 * (r * ‖∇ U‖) := by
    rw [Lp.norm_def, eLpNorm_congr_ae hgrad]
    change (eLpNorm (r • (fun y ↦ ∇ U (MeanScaling.ballHomeomorph x hr y)))
      2 (domainMeasure 3 (ball 0 1))).toReal = _
    rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm,
      Real.norm_of_nonneg hr.le, MeanScaling.eLpNorm_comp_ballHomeomorph x hr, ← Lp.norm_def]
    ring
  have hS' := hS V
  change (eLpNorm (wkpBaseCoordinateCLM V : ℝ^3 → ℝ) 6
    (domainMeasure 3 (ball 0 1))).toReal ≤ _ at hS'
  rw [eLpNorm_congr_ae hbase, MeanScaling.eLpNorm_comp_ballHomeomorph x hr,
    hB, hG, normFactor_two_eq_six_div hr] at hS'
  apply (mul_le_mul_iff_right₀ (MeanScaling.normFactor_pos (n := 3) hr 6)).mp
  convert hS' using 1 <;> cas using hr

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
