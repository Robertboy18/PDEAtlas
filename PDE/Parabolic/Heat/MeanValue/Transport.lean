/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.Flux
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import PDE.Analysis.Calculus.EuclideanBall
public import PDE.Analysis.Calculus.MovingBall

/-!
# Moving-slice transport for Watson's heat-ball argument

Watson's density contains `log τ` and inverse powers of `τ`, so it is smooth
only for positive backward time.  At a fixed positive slice, a smooth bump
replaces time by a globally positive parameter that agrees with the identity
near that slice.  This permits direct use of the global moving-ball Reynolds
formula without a regularity hypothesis across `τ = 0`.

The lateral boundary term is then identified explicitly with the normal flux
of Watson's vector field.  Gauss's formula and the pointwise Watson identity
reduce the derivative of the moving-slice integral to the integral of the
transport density.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, proof of Theorem 3, equations (20)-(21).
  <https://doi.org/10.1090/gsm/019>
* N. A. Watson, "A Theory of Subtemperatures in Several Variables", *Proc. London Math. Soc.*
  (3) 26 (1973), 385-417. <https://doi.org/10.1112/plms/s3-26.3.385>
-/

@[expose] public section

open PDE (laplacian divergence advectiveDerivative)

noncomputable section

namespace HeatEquation

open Filter PDE.Analysis PDE.Common
open MeasureTheory
open scoped Topology

variable {n : ℕ}

private theorem exists_contDiff_positive_time_reparam
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ ψ : ℝ → ℝ,
      ContDiff ℝ 1 ψ ∧
        (∀ s, 0 < ψ s) ∧
          ψ =ᶠ[𝓝 τ] fun s : ℝ ↦ s := by
  let b : ContDiffBump τ :=
    { rIn := τ / 4
      rOut := τ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hb : ContDiff ℝ 1 b := b.contDiff
  refine ⟨fun s ↦ b s * s + (1 - b s) * τ, by fun_prop, fun s ↦ ?_, ?_⟩
  · rcases (b.nonneg (x := s)).eq_or_lt with h | h
    · simpa [← h] using hτ
    · have hs : s ∈ Metric.ball τ (τ / 2) := b.support_eq ▸ Function.mem_support.2 h.ne'
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact add_pos_of_pos_of_nonneg (mul_pos h (by linarith [abs_lt.1 hs]))
        (mul_nonneg (sub_nonneg.2 b.le_one) hτ.le)
  · filter_upwards [b.eventuallyEq_one] with s hs
    simp [hs]

private theorem contDiff_uncurry_watsonQ_comp_positive_time
    (v : ℝ → ℝ^n → ℝ)
    (hv : ContDiff ℝ 1 (Function.uncurry v))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψPos : ∀ s, 0 < ψ s) :
    ContDiff ℝ 1
      (fun p : ℝ × ℝ^n ↦ watsonQ n v (ψ p.1) p.2) := by
  have hvψ : ContDiff ℝ 1 fun p : ℝ × ℝ^n ↦ v (ψ p.1) p.2 :=
    hv.comp ((hψ.comp contDiff_fst).prodMk contDiff_snd)
  have hψ0 (p : ℝ × ℝ^n) : ψ p.1 ≠ 0 := (hψPos p.1).ne'
  have hnormSq : ContDiff ℝ 1 fun p : ℝ × ℝ^n ↦ ‖p.2‖ ^ 2 := contDiff_snd.norm_sq ℝ
  unfold watsonQ watsonWeight watsonLogPhase
  fun_prop (disch := simp [hψ0, Real.pi_ne_zero])

private theorem contDiff_watsonF_component
    (v : ℝ → ℝ^n → ℝ)
    {τ : ℝ} (hvSlice : ContDiff ℝ 2 (v τ)) (hτ : τ ≠ 0) (i : Fin n) :
    ContDiff ℝ 1
      (fun y : ℝ^n ↦ watsonF n τ (v τ) y i) := by
  have hv1 : ContDiff ℝ 1 (v τ) := hvSlice.of_le (by norm_num)
  have hpartial : ContDiff ℝ 1 fun y ↦ (∂[i] (v τ)) y :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hvSlice
  have hcoord : ContDiff ℝ 1 fun y : ℝ^n ↦ y i := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hnormSq : ContDiff ℝ 1 fun y : ℝ^n ↦ ‖y‖ ^ 2 := contDiff_norm_sq ℝ
  simp only [watsonF_apply, partialDeriv_watsonLogPhase n hτ]
  unfold watsonLogPhase watsonWeight
  fun_prop (disch := simp [hτ])

private theorem sliceRadiusVelocity_mul_watsonQ_eq_normalFlux
    (hn : 0 < n) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi)))
    (v : ℝ → ℝ^n → ℝ) {y : ℝ^n}
    (hy : y ∈ Metric.sphere (0 : ℝ^n)
      (heatBallSliceRadius n 1 τ)) :
    (heatBallSliceRadius n 1 τ / (2 * τ) -
          (n : ℝ) / heatBallSliceRadius n 1 τ) *
        watsonQ n v τ y =
      ∑ i : Fin n,
        watsonF n τ (v τ) y i *
          (NormedSpace.normalize (y - 0)) i := by
  have hR : 0 < heatBallSliceRadius n 1 τ := by
    rw [heatBallSliceRadius]
    exact Real.sqrt_pos.2
      ((heatBallSliceRadiusSq_pos_iff hn zero_lt_one hτ.1).2 (by simpa using hτ.2))
  have hnorm : ‖y‖ = heatBallSliceRadius n 1 τ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy
  have hphase := watsonLogPhase_eq_zero_of_mem_sphere hn hτ hy
  have hτ0 := hτ.1.ne'
  have hcomponent (i : Fin n) :
      watsonF n τ (v τ) y i * (NormedSpace.normalize (y - 0)) i =
        v τ y * (heatBallSliceRadius n 1 τ)⁻¹ * (watsonWeight τ y - 2 * (n : ℝ) / τ) * y i ^ 2 := by
    rw [watsonF_apply, hphase, partialDeriv_watsonLogPhase n hτ0]
    simp only [mul_zero, zero_mul, zero_add, sub_zero, NormedSpace.normalize, hnorm,
      PiLp.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hcomponent i, ← Finset.mul_sum,
    ← EuclideanSpace.real_norm_sq_eq, watsonQ, hphase, watsonWeight, hnorm]
  field_simp
  ring

/-- Moving-slice transport identity for Watson's density on the unit heat ball.

At a positive backward time `τ`, the derivative of the integral of `Q` over
the corresponding spatial slice is the integral of Watson's transport
density.  The caloric equation is needed only on the fixed slice where the
derivative is evaluated. -/
theorem hasDerivAt_ballIntegral_watsonQ
    (hn : 0 < n)
    (v : ℝ → ℝ^n → ℝ)
    (hv : ContDiff ℝ 1 (Function.uncurry v))
    (hvSpace : ∀ s, ContDiff ℝ 2 (v s))
    {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi)))
    (hcaloric :
      ∀ y ∈ Metric.ball (0 : ℝ^n)
          (heatBallSliceRadius n 1 τ),
        deriv (fun s ↦ v s y) τ +
          laplacian (v τ) y = 0) :
    HasDerivAt
      (fun s ↦
        ballIntegral n (watsonQ n v s) (0 : ℝ^n)
          (heatBallSliceRadius n 1 s))
      (ballIntegral n
        (fun y ↦
          watsonWeight τ y *
            (advectiveDerivative (fun z : ℝ^n ↦ z) (v τ) y +
              2 * τ * deriv (fun s ↦ v s y) τ))
        (0 : ℝ^n) (heatBallSliceRadius n 1 τ))
      τ := by
  let _ : Fact (0 < n) := ⟨hn⟩
  have hradiusPos : 0 < heatBallSliceRadius n 1 τ := by
    rw [heatBallSliceRadius]
    exact Real.sqrt_pos.2
      ((heatBallSliceRadiusSq_pos_iff hn zero_lt_one hτ.1).2 (by simpa using hτ.2))
  obtain ⟨ψ, hψ, hψPos, hψEq⟩ := exists_contDiff_positive_time_reparam hτ.1
  let q : ℝ → ℝ^n → ℝ := fun s y ↦ watsonQ n v (ψ s) y
  have hq : ContDiff ℝ 1 (Function.uncurry q) :=
    contDiff_uncurry_watsonQ_comp_positive_time v hv ψ hψ hψPos
  have hqEq : q =ᶠ[𝓝 τ] fun s ↦ watsonQ n v s := by
    filter_upwards [hψEq] with s hs
    simp [q, hs]
  have htime (y : ℝ^n) : fderiv ℝ (Function.uncurry q) (τ, y) ((1 : ℝ), (0 : ℝ^n)) =
      deriv (fun s ↦ watsonQ n v s y) τ :=
    (((hq.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt τ
      (show HasDerivAt (fun s : ℝ ↦ (s, y)) ((1 : ℝ), (0 : ℝ^n)) τ from
        (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y))).congr_of_eventuallyEq
        (hqEq.mono fun s hs ↦ (congrFun hs y).symm)).deriv.symm
  refine ((hasDerivAt_ballIntegral_moving q hq (0 : ℝ^n) (heatBallSliceRadius n 1)
    (hasDerivAt_heatBallSliceRadius hn zero_lt_one hτ.1 (by simpa using hτ.2))
    hradiusPos).congr_of_eventuallyEq (hqEq.mono fun s hs ↦ by simp only [hs])).congr_deriv ?_
  have hflux (i : Fin n) := contDiff_watsonF_component v (hvSpace τ) hτ.1.ne' i
  have hgauss : ballIntegral n (fun y ↦ ∇· (watsonF n τ (v τ)) y) 0 (heatBallSliceRadius n 1 τ) =
      sphereIntegral n (fun y ↦ ∑ i : Fin n, watsonF n τ (v τ) y i *
        (NormedSpace.normalize (y - 0)) i) 0 (heatBallSliceRadius n 1 τ) := by
    simpa [divergence] using ballIntegral_divergence_eq_sphereIntegral_normal_flux
      (fun i y ↦ watsonF n τ (v τ) y i) hflux (0 : ℝ^n) hradiusPos
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) :
      IntegrableOn f (Metric.ball 0 (heatBallSliceRadius n 1 τ)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      Metric.ball_subset_closedBall
  have htimeCont : Continuous fun y : ℝ^n ↦ deriv (fun s ↦ watsonQ n v s y) τ := by
    simp only [← htime]
    exact ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  have hdivCont : Continuous fun y : ℝ^n ↦ ∇· (watsonF n τ (v τ)) y := by
    unfold divergence
    exact continuous_finsetSum _ fun i _ ↦
      ((hflux i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [hqEq.self_of_nhds, ← sphereIntegral_const_mul, sphereIntegral_congr_on_sphere hradiusPos
    fun y hy ↦ sliceRadiusVelocity_mul_watsonQ_eq_normalFlux hn hτ v hy, ← hgauss]
  simp only [ballIntegral, htime]
  rw [← integral_add (hint htimeCont) (hint hdivCont)]
  refine setIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
  exact deriv_watsonQ_add_divergence_watsonF_of_backward_caloric n hτ.1.ne' v y
    ((hv.differentiable one_ne_zero).differentiableAt.comp τ
      (differentiableAt_id.prodMk (differentiableAt_const y)))
    (hvSpace τ).contDiffAt (hcaloric y hy)

end HeatEquation
