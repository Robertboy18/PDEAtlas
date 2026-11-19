/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import PDE.Parabolic.Heat.MeanValue.Flux

/-!
# Endpoint decay in Watson's heat-ball argument

The moving-slice identity contains the integral of Watson's density `Q`.
This boundary quantity vanishes at both ends of the
unit heat ball's backward-time interval.

The proof uses only continuity of the transported field.  On a slice of
radius `ρ(τ)`, Watson's density is bounded by a constant times
`ρ(τ)² / τ`; multiplication by the slice volume gives
`ρ(τ)ⁿ⁺² / τ`.  At the earliest time the radius tends to zero.  At
the pole, the elementary limit `τ |log τ|³ → 0` controls the worst
three-dimensional power `ρ(τ)³ / τ`; positive spatial dimension supplies
all remaining powers of the shrinking radius.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, proof of Theorem 3, equations (20)-(21).
  <https://doi.org/10.1090/gsm/019>
* N. A. Watson, "A Theory of Subtemperatures in Several Variables", *Proc. London Math. Soc.*
  (3) 26 (1973), 385-417. <https://doi.org/10.1112/plms/s3-26.3.385>
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open Filter PDE.Analysis
open MeasureTheory
open scoped Topology

variable {n : ℕ}

private theorem norm_watsonQ_le_on_slice
    (hn : 0 < n) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi)))
    (v : ℝ → ℝ^n → ℝ) {y : ℝ^n}
    (hy : y ∈ Metric.ball (0 : ℝ^n)
      (heatBallSliceRadius n 1 τ)) :
    ‖watsonQ n v τ y‖ ≤
      ((n : ℝ) + 2) *
        heatBallSliceRadius n 1 τ ^ 2 / τ * ‖v τ y‖ := by
  have hR2 : heatBallSliceRadius n 1 τ ^ 2 = heatBallSliceRadiusSq n 1 τ := by
    rw [heatBallSliceRadius, Real.sq_sqrt
      ((heatBallSliceRadiusSq_pos_iff hn zero_lt_one hτ.1).2 (by simpa using hτ.2)).le]
  have hy2 : ‖y‖ ^ 2 ≤ heatBallSliceRadius n 1 τ ^ 2 := by
    gcongr
    exact (mem_ball_zero_iff.1 hy).le
  have hτpos : 0 < τ := hτ.1
  have hτ0 := hτpos.ne'
  have hcoeff : 2 * τ * watsonWeight τ y - 4 * (n : ℝ) * watsonLogPhase n τ y =
      (2 * ‖y‖ ^ 2 - n * (heatBallSliceRadius n 1 τ ^ 2 - ‖y‖ ^ 2)) / τ := by
    rw [watsonWeight, watsonLogPhase_eq_sliceRadiusSq_sub n hτ.1 y, ← hR2]
    field_simp
  have hnR : 0 ≤ (n : ℝ) := by positivity
  rw [watsonQ, norm_mul, Real.norm_eq_abs, hcoeff, abs_div, abs_of_pos hτpos]
  gcongr
  have := mul_nonneg hnR (sub_nonneg.2 hy2)
  have := mul_nonneg hnR (sq_nonneg ‖y‖)
  have := sq_nonneg (heatBallSliceRadius n 1 τ)
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

private theorem norm_ballIntegral_watsonQ_le
    (hn : 0 < n) {τ M : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi)))
    (v : ℝ → ℝ^n → ℝ)
    (hM :
      ∀ y ∈ Metric.ball (0 : ℝ^n)
          (heatBallSliceRadius n 1 τ),
        ‖v τ y‖ ≤ M) :
    ‖ballIntegral n (watsonQ n v τ) (0 : ℝ^n)
        (heatBallSliceRadius n 1 τ)‖ ≤
      (((n : ℝ) + 2) * M * unitBallVolume n) *
        (heatBallSliceRadius n 1 τ ^ (n + 2) / τ) := by
  let _ : Fact (0 < n) := ⟨hn⟩
  have hint := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (ℝ^n)))
    (f := watsonQ n v τ) measure_ball_lt_top fun y hy ↦
      (norm_watsonQ_le_on_slice hn hτ v hy).trans
        (mul_le_mul_of_nonneg_left (hM y hy) (by have := hτ.1; positivity))
  change _ ≤ _ * ballVolume n (heatBallSliceRadius n 1 τ) at hint
  rw [ballVolume_eq_unitBallVolume_mul_pow n (heatBallSliceRadius n 1 τ) (Real.sqrt_nonneg _)]
    at hint
  refine hint.trans_eq ?_
  rw [pow_add]
  field_simp [hτ.1.ne']

private theorem eventually_norm_le_on_shrinking_ball
    {v : ℝ → ℝ^n → ℝ} (hv : Continuous (Function.uncurry v))
    {a : ℝ} {ρ : ℝ → ℝ} {l : Filter ℝ}
    (htime : Tendsto (fun τ : ℝ ↦ τ) l (𝓝 a))
    (hradius : Tendsto ρ l (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ τ in l, ∀ y ∈ Metric.ball (0 : ℝ^n) (ρ τ),
        ‖v τ y‖ ≤ M := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((hv.continuousAt (x := (a, (0 : ℝ^n)))).preimage_mem_nhds
      (Metric.ball_mem_nhds _ zero_lt_one))
  refine ⟨‖v a 0‖ + 1, by positivity, ?_⟩
  filter_upwards [htime.eventually (Metric.ball_mem_nhds a hε),
    hradius.eventually (Metric.ball_mem_nhds 0 hε)] with τ hτ hρ y hy
  have hvNear : dist (v τ y) (v a 0) < 1 := @hεsub (τ, y) (by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hτ, ((Metric.mem_ball.1 hy).trans_le (le_abs_self _)).trans
      (by simpa [Metric.mem_ball, Real.dist_eq] using hρ)⟩)
  have := norm_le_norm_add_norm_sub' (v τ y) (v a 0)
  rw [← dist_eq_norm] at this
  linarith

private theorem tendsto_mul_abs_log_cube_four_pi_nhdsGT_zero :
    Tendsto
      (fun τ : ℝ ↦ τ * |Real.log (4 * Real.pi * τ)| ^ 3)
      (𝓝[>] 0) (𝓝 0) := by
  have hraw : Tendsto (fun s : ℝ ↦ s * |Real.log s| ^ 3) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.rpow_neg_one, div_inv_eq_mul, mul_comm] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (s := -1) 3 (by norm_num)).tendsto_div_nhds_zero
  have hscale : Tendsto (fun τ : ℝ ↦ 4 * Real.pi * τ) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id :
      Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] 0) (𝓝 0)).const_mul (4 * Real.pi)),
      eventually_nhdsWithin_of_forall fun τ (hτ : 0 < τ) ↦ show 0 < 4 * Real.pi * τ by positivity⟩
  convert (hraw.comp hscale).const_mul (4 * Real.pi)⁻¹ using 1
  · funext τ
    simp only [Function.comp_apply]
    field_simp [Real.pi_ne_zero]
  · simp

private theorem tendsto_tau_mul_heatBallLog_cube_nhdsGT_zero :
    Tendsto
      (fun τ : ℝ ↦
        τ * Real.log (1 / (4 * Real.pi * τ)) ^ 3)
      (𝓝[>] 0) (𝓝 0) := by
  have htimeCap : 0 < (1 / (4 * Real.pi) : ℝ) := by
    positivity
  refine tendsto_mul_abs_log_cube_four_pi_nhdsGT_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT htimeCap] with τ hτ
  have hfourPiPos : 0 < (4 * Real.pi : ℝ) := by
    positivity
  have hproductPos : 0 < 4 * Real.pi * τ := by
    exact mul_pos hfourPiPos hτ.1
  have hproductLt : 4 * Real.pi * τ < 1 := by
    have h := (lt_div_iff₀ hfourPiPos).mp hτ.2
    nlinarith
  have hlogNonpos :
      Real.log (4 * Real.pi * τ) ≤ 0 :=
    Real.log_nonpos hproductPos.le hproductLt.le
  rw [Real.log_div one_ne_zero hproductPos.ne',
    Real.log_one, zero_sub, abs_of_nonpos hlogNonpos]

private theorem
    tendsto_heatBallSliceRadius_cube_div_nhdsGT_zero
    (hn : 0 < n) :
    Tendsto
      (fun τ : ℝ ↦
        heatBallSliceRadius n 1 τ ^ 3 / τ)
      (𝓝[>] 0) (𝓝 0) := by
  have htimeCap : 0 < (1 / (4 * Real.pi) : ℝ) := by
    positivity
  have hsqBase :
      Tendsto
        (fun τ : ℝ ↦
          (2 * (n : ℝ)) ^ 3 *
            (τ * Real.log (1 / (4 * Real.pi * τ)) ^ 3))
        (𝓝[>] 0) (𝓝 0) := by
    simpa using
      tendsto_tau_mul_heatBallLog_cube_nhdsGT_zero.const_mul
        ((2 * (n : ℝ)) ^ 3)
  have hsq :
      Tendsto
        (fun τ : ℝ ↦
          (heatBallSliceRadius n 1 τ ^ 3 / τ) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
    refine hsqBase.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT htimeCap] with τ hτ
    have hradiusSqPos :
        0 < heatBallSliceRadiusSq n 1 τ :=
      (heatBallSliceRadiusSq_pos_iff hn zero_lt_one hτ.1).2 (by
        simpa using hτ.2)
    have hradiusSq :
        heatBallSliceRadius n 1 τ ^ 2 =
          heatBallSliceRadiusSq n 1 τ := by
      rw [heatBallSliceRadius, Real.sq_sqrt hradiusSqPos.le]
    calc
      (2 * (n : ℝ)) ^ 3 *
          (τ * Real.log (1 / (4 * Real.pi * τ)) ^ 3) =
          (heatBallSliceRadiusSq n 1 τ) ^ 3 / τ ^ 2 := by
        rw [heatBallSliceRadiusSq]
        simp only [one_pow]
        field_simp [hτ.1.ne']
      _ = (heatBallSliceRadius n 1 τ ^ 3 / τ) ^ 2 := by
        rw [← hradiusSq]
        field_simp [hτ.1.ne']
  have hsqrt := hsq.sqrt
  have heventually :
      (fun τ : ℝ ↦
        Real.sqrt
          ((heatBallSliceRadius n 1 τ ^ 3 / τ) ^ 2)) =ᶠ[𝓝[>] 0]
        fun τ ↦
          heatBallSliceRadius n 1 τ ^ 3 / τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [Real.sqrt_sq]
    exact
      div_nonneg
        (pow_nonneg (Real.sqrt_nonneg _) 3) hτ.le
  simpa using hsqrt.congr' heventually

private theorem tendsto_heatBallSliceRadius_pow_div_nhdsGT_zero
    (hn : 0 < n) :
    Tendsto
      (fun τ : ℝ ↦
        heatBallSliceRadius n 1 τ ^ (n + 2) / τ)
      (𝓝[>] 0) (𝓝 0) := by
  have htimeCap : 0 < (1 / (4 * Real.pi) : ℝ) := by positivity
  apply squeeze_zero'
  · exact eventually_nhdsWithin_of_forall fun τ (hτ : 0 < τ) ↦
      div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hτ.le
  · filter_upwards [Ioo_mem_nhdsGT htimeCap,
      (tendsto_heatBallSliceRadius_nhdsGT_zero n).eventually (Iio_mem_nhds zero_lt_one)]
      with τ hτ hR
    exact div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one (Real.sqrt_nonneg _) (le_of_lt hR) (m := 3) (n := n + 2) (by omega))
      hτ.1.le
  · exact tendsto_heatBallSliceRadius_cube_div_nhdsGT_zero hn

/-- Watson's moving-slice boundary quantity vanishes at the heat-ball pole. -/
theorem tendsto_ballIntegral_watsonQ_nhdsGT_zero
    (hn : 0 < n) {v : ℝ → ℝ^n → ℝ}
    (hv : Continuous (Function.uncurry v)) :
    Tendsto
      (fun τ ↦
        ballIntegral n (watsonQ n v τ) 0
          (heatBallSliceRadius n 1 τ))
      (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨M, -, hM⟩ := eventually_norm_le_on_shrinking_ball hv
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) (tendsto_heatBallSliceRadius_nhdsGT_zero n)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (4 * Real.pi)), hM]
      with τ hτ hMτ
    exact norm_ballIntegral_watsonQ_le hn hτ v hMτ
  · simpa using (tendsto_heatBallSliceRadius_pow_div_nhdsGT_zero hn).const_mul
      (((n : ℝ) + 2) * M * unitBallVolume n)

/-- Watson's moving-slice boundary quantity vanishes at the earliest
heat-ball time. -/
theorem tendsto_ballIntegral_watsonQ_nhdsLT_timeCap
    (hn : 0 < n) {v : ℝ → ℝ^n → ℝ}
    (hv : Continuous (Function.uncurry v)) :
    Tendsto
      (fun τ ↦
        ballIntegral n (watsonQ n v τ) 0
          (heatBallSliceRadius n 1 τ))
      (𝓝[<] (1 / (4 * Real.pi))) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hT : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
  have htime : Tendsto (fun τ : ℝ ↦ τ) (𝓝[<] (1 / (4 * Real.pi))) (𝓝 (1 / (4 * Real.pi))) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hradius := tendsto_heatBallSliceRadius_nhdsLT_timeCap n
  obtain ⟨M, -, hM⟩ := eventually_norm_le_on_shrinking_ball hv htime hradius
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsLT hT, hM] with τ hτ hMτ
    exact norm_ballIntegral_watsonQ_le hn hτ v hMτ
  · simpa using ((hradius.pow (n + 2)).div htime hT.ne').const_mul
      (((n : ℝ) + 2) * M * unitBallVolume n)

end HeatEquation
