/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.Endpoints
public import PDE.Parabolic.Heat.MeanValue.Scale
public import PDE.Parabolic.Heat.MeanValue.Slicing
import PDE.FDeriv.SpaceTime
import PDE.Parabolic.Heat.MeanValue.Topology
import PDE.Representations.Similarity.DynamicAffine
import CAS.ExactTactic
public import PDE.Parabolic.Heat.MeanValue.Normalization
public import PDE.Parabolic.Heat.MeanValue.Transport
import PDE.FDeriv.Calculus

/-!
# The heat-ball mean-value formula

Evans's heat-ball mean-value formula (§2.3.2, Theorem 3), `heatBall_meanValue`. We follow the
proof in Evans, which he credits to Watson (§2.6): fix the unit heat ball and differentiate the
parabolic scaling `heatBallParabolicMap x t a` in `a`. The scale derivative becomes Watson's
transport density on the spatial slices (`watsonTransportCore_eq_scaleDeriv`), its slice
integral vanishes by the flux identity and the endpoint decay of `MeanValue.Endpoints`, and
Fubini integrates the zero scale derivative from the pole `a = 0`, where the weighted integral
is `4 u(x, t)` (`setIntegral_heatBallWeight`), out to `a = r`.

There is no separate notion of caloric function. `heatBall_meanValue` takes joint `C¹`
regularity, `C²` regularity on each spatial slice, and the pointwise equation
`heatOperator u p = 0` on `heatBall x t r`. No mixed or second time derivative is needed.
Positive spatial dimension is explicit as `hn : 0 < n`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, Theorem 3 (a mean-value property for the heat
  equation), and §2.6, which credits Theorem 3 and its proof to Watson.
  <https://doi.org/10.1090/gsm/019>
* N. A. Watson, "A Theory of Subtemperatures in Several Variables", *Proc. London Math. Soc.*
  (3) 26 (1973), 385-417. <https://doi.org/10.1112/plms/s3-26.3.385>
-/

@[expose] public section

open PDE (SpaceTime laplacian advectiveDerivative time)

noncomputable section

namespace HeatEquation

open Filter PDE.Analysis PDE.Common
open MeasureTheory
open scoped Topology

variable {n : ℕ}

/-- The parabolic map sends the backward point `(-τ, y)` to `(t - a ^ 2 * τ, x + a • y)`. -/
private theorem heatBallParabolicMap_timeSpaceCons_neg (x : ℝ^n) (t a τ : ℝ) (y : ℝ^n) :
    heatBallParabolicMap x t a (timeSpaceCons (-τ) y) =
      timeSpaceCons (t - a ^ 2 * τ) (x + a • y) := by
  ext i
  cases i using Fin.cases <;> simp [heatBallParabolicMap, time, sub_eq_add_neg]

/-- Watson's transport derivative for a backward parabolic pullback is the
scale derivative of the original field, multiplied by the current scale. -/
private theorem watsonTransportCore_eq_scaleDeriv
    {u : SpaceTime n → ℝ}
    (x : ℝ^n) (t a τ : ℝ) (y : ℝ^n)
    (hu : DifferentiableAt ℝ u
      (heatBallParabolicMap x t a (timeSpaceCons (-τ) y))) :
    advectiveDerivative (fun z : ℝ^n ↦ z)
          (fun z ↦
            u (timeSpaceCons (t - a ^ 2 * τ) (x + a • z))) y +
        2 * τ *
          deriv
            (fun s ↦
              u (timeSpaceCons (t - a ^ 2 * s) (x + a • y))) τ =
      a *
        deriv
          (fun b ↦
            u (heatBallParabolicMap x t b
              (timeSpaceCons (-τ) y))) a := by
  have hmap := heatBallParabolicMap_timeSpaceCons_neg x t a τ y
  have huq : DifferentiableAt ℝ u (timeSpaceCons (t - a ^ 2 * τ) (x + a • y)) := hmap ▸ hu
  have htime : deriv (fun s ↦ u (timeSpaceCons (t - a ^ 2 * s) (x + a • y))) τ =
      -(a ^ 2) * (∂[0] u) (timeSpaceCons (t - a ^ 2 * τ) (x + a • y)) := by
    have hcomp := HasDerivAt.comp τ (PDE.hasDerivAt_timeSpaceCons u (t - a ^ 2 * τ) (x + a • y) huq)
      (by cas : HasDerivAt (fun s : ℝ ↦ t - a ^ 2 * s) (-(a ^ 2)) τ)
    simpa only [Function.comp_def, mul_comm] using hcomp.deriv
  have hprofile : DifferentiableAt ℝ (fun z ↦ u (timeSpaceCons (t - a ^ 2 * τ) z)) (x + a • y) :=
    huq.comp (x + a • y)
      (hasFDerivAt_timeSpaceCons_spatial n (t - a ^ 2 * τ) (x + a • y)).differentiableAt
  have hspatial : advectiveDerivative (fun z : ℝ^n ↦ z)
      (fun z ↦ u (timeSpaceCons (t - a ^ 2 * τ) (x + a • z))) y =
        a * ∑ j : Fin n, y j * (∂[j.succ] u) (timeSpaceCons (t - a ^ 2 * τ) (x + a • y)) := by
    rw [PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← PDE.partialDeriv_timeSpaceCons_spatial j u _ _ huq]
    have := PDE.Representations.Similarity.partialDeriv_comp_affineDilation j _ a x y
      (by simpa [PDE.Representations.Similarity.affineDilation, add_comm] using hprofile)
    simp only [PDE.Representations.Similarity.affineDilation, add_comm] at this
    rw [this]
    ring
  rw [htime, hspatial, (hasDerivAt_comp_heatBallParabolicMap_scale x t a _ hu).deriv]
  simp only [time, timeSpaceCons_zero, spatialPart_timeSpaceCons]
  rw [hmap]
  ring

/-- At every positive scale below the caloric radius, the weighted scale
derivative has zero integral on the unit heat ball. -/
private theorem setIntegral_unitHeatBall_scaleDerivative_eq_zero
    (hn : 0 < n) {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 1 u)
    (huSpace : ∀ s, ContDiff ℝ 2 (fun z ↦ u (timeSpaceCons s z)))
    (x : ℝ^n) (t : ℝ)
    {r a : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hcaloric :
      ∀ p ∈ heatBall x t r, heatOperator u p = 0) :
    (∫ p in heatBall (0 : ℝ^n) 0 1,
        heatBallWeight (0 : ℝ^n) 0 p *
          ((2 * a * time p) *
              (∂[0] u) (heatBallParabolicMap x t a p) +
            ∑ j : Fin n,
              spatialPart p j *
                (∂[j.succ] u)
                  (heatBallParabolicMap x t a p))
          ∂(volume : Measure (SpaceTime n))) = 0 := by
  let P : SpaceTime n → SpaceTime n := heatBallParabolicMap x t a
  let D : SpaceTime n → ℝ := fun p ↦
    (2 * a * time p) * (∂[0] u) (P p) + ∑ j : Fin n, spatialPart p j * (∂[j.succ] u) (P p)
  let F : SpaceTime n → ℝ := fun p ↦ heatBallWeight (0 : ℝ^n) 0 p * D p
  let v : ℝ → ℝ^n → ℝ := fun τ y ↦ u (timeSpaceCons (t - a ^ 2 * τ) (x + a • y))
  let S : ℝ → ℝ := fun τ ↦
    ballIntegral n (fun y ↦ F (timeSpaceCons (-τ) y)) (0 : ℝ^n) (heatBallSliceRadius n 1 τ)
  have htime : ContDiff ℝ 2 fun p : SpaceTime n ↦ time p := (timeCLM n).contDiff
  have hspace : ContDiff ℝ 2 fun p : SpaceTime n ↦ spatialPart p := (spatialPartCLM n).contDiff
  have hP : ContDiff ℝ 2 P := by
    change ContDiff ℝ 2 ((fun q : ℝ × ℝ^n ↦ timeSpaceCons q.1 q.2) ∘
      fun p : SpaceTime n ↦ (t + a ^ 2 * time p, x + a • spatialPart p))
    exact (contDiff_timeSpaceCons_uncurry n).comp (by fun_prop)
  have hpartial (i : Fin (n + 1)) : Continuous fun p ↦ (∂[i] u) (P p) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hu).continuous.comp hP.continuous
  have hcoord (j : Fin n) : Continuous fun p : SpaceTime n ↦ spatialPart p j :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hspace.continuous
  have htime' := htime.continuous
  have hD : Continuous D := by
    simp only [D]
    fun_prop
  have hF : IntegrableOn F (heatBall (0 : ℝ^n) 0 1) :=
    (integrableOn_heatBallWeight hn (0 : ℝ^n) 0 zero_lt_one).mul_continuousOn_of_subset
      hD.continuousOn (measurableSet_heatBall (n := n) (0 : ℝ^n) 0 1)
      (isCompact_closure_heatBall hn zero_lt_one) subset_closure
  have hv : ContDiff ℝ 1 (Function.uncurry v) := by
    change ContDiff ℝ 1 (u ∘ (fun q : ℝ × ℝ^n ↦ timeSpaceCons q.1 q.2) ∘
      fun q : ℝ × ℝ^n ↦ (t - a ^ 2 * q.1, x + a • q.2))
    exact hu.comp ((contDiff_timeSpaceCons_uncurry n).comp (by fun_prop))
  have hvSpace (s : ℝ) : ContDiff ℝ 2 (v s) := by
    change ContDiff ℝ 2
      ((fun z ↦ u (timeSpaceCons (t - a ^ 2 * s) z)) ∘ fun y ↦ x + a • y)
    exact (huSpace _).comp (by fun_prop)
  have hcaloricSlice (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi))) (y : ℝ^n)
      (hy : y ∈ Metric.ball (0 : ℝ^n) (heatBallSliceRadius n 1 τ)) :
      deriv (fun s ↦ v s y) τ + laplacian (v τ) y = 0 := by
    have hs : -τ ∈ Set.Ioo (0 - (1 : ℝ) ^ 2 / (4 * Real.pi)) 0 := by
      constructor <;> norm_num at * <;> linarith
    have hp := heatBall_mono ha har ((heatBallParabolicMap_mem_iff x t ha _).2
      ((timeSpaceCons_mem_heatBall_iff_mem_ball (x := (0 : ℝ^n)) (y := y) (t := 0) hn zero_lt_one
        hs).2 (by simpa using hy)))
    rw [show deriv (fun s ↦ v s y) τ + laplacian (v τ) y =
        -(a ^ 2) * heatOperator u (timeSpaceCons (t - a ^ 2 * τ) (x + a • y)) by
      simpa only [v] using deriv_backward_parabolic_pullback_add_laplacian u hu huSpace x t a τ y,
      ← heatBallParabolicMap_timeSpaceCons_neg, hcaloric _ hp, mul_zero]
  have htransport (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi))) :
      HasDerivAt (fun s ↦ ballIntegral n (watsonQ n v s) (0 : ℝ^n) (heatBallSliceRadius n 1 s))
        (a * S τ) τ := by
    refine (hasDerivAt_ballIntegral_watsonQ hn v hv hvSpace hτ (hcaloricSlice τ hτ)).congr_deriv ?_
    dsimp only [S]
    unfold ballIntegral
    rw [← integral_const_mul]
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun y _ ↦ ?_
    have huAt : DifferentiableAt ℝ u (heatBallParabolicMap x t a (timeSpaceCons (-τ) y)) :=
      (hu.differentiable one_ne_zero).differentiableAt
    have hcore := watsonTransportCore_eq_scaleDeriv x t a τ y huAt
    rw [(hasDerivAt_comp_heatBallParabolicMap_scale x t a _ huAt).deriv] at hcore
    have hweight : heatBallWeight (0 : ℝ^n) 0 (timeSpaceCons (-τ) y) = watsonWeight τ y := by
      unfold heatBallWeight watsonWeight
      simp [time, norm_neg]
    simp only [v]
    rw [hcore]
    simp only [F, D, P, hweight]
    ring
  have hS : IntervalIntegrable S volume 0 (1 / (4 * Real.pi)) := by
    simpa only [S, ballIntegral] using intervalIntegrable_unitHeatBall_backward_slices hn F hF
  have hcap : 0 < (1 / (4 * Real.pi) : ℝ) := by positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hcap htransport
    (hS.const_mul a) (tendsto_ballIntegral_watsonQ_nhdsGT_zero hn hv.continuous)
    (tendsto_ballIntegral_watsonQ_nhdsLT_timeCap hn hv.continuous)
  have hslice : ∫ τ in (0 : ℝ)..(1 / (4 * Real.pi)), S τ = 0 :=
    (mul_eq_zero.mp (by simpa using hFTC)).resolve_left ha.ne'
  rw [intervalIntegral.integral_of_le hcap.le, integral_Ioc_eq_integral_Ioo] at hslice
  simpa only [F, D, P, S, ballIntegral] using
    (setIntegral_unitHeatBall_eq_integral_backward_slices hn F hF).trans hslice

/-- The heat-ball mean-value formula under anisotropic regularity.

The equation is required only on the heat ball of radius `r`. Joint `C¹`
regularity and spatial `C²` slices suffice for the scale and flux calculations. -/
theorem heatBall_meanValue
    (hn : 0 < n) (u : SpaceTime n → ℝ) (hu : ContDiff ℝ 1 u)
    (huSpace : ∀ s, ContDiff ℝ 2 (fun z ↦ u (timeSpaceCons s z)))
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hcaloric :
      ∀ p ∈ heatBall x t r, heatOperator u p = 0) :
    (∫ p in heatBall x t r,
        heatBallWeight x t p * u p
          ∂(volume : Measure (SpaceTime n))) =
      4 * r ^ n * u (timeSpaceCons t x) := by
  let P : ℝ → SpaceTime n → SpaceTime n := fun a ↦ heatBallParabolicMap x t a
  let D : ℝ → SpaceTime n → ℝ := fun a p ↦
    (2 * a * time p) * (∂[0] u) (P a p) + ∑ j : Fin n, spatialPart p j * (∂[j.succ] u) (P a p)
  have hB := measurableSet_heatBall (n := n) (0 : ℝ^n) 0 1
  have hK := isCompact_closure_heatBall hn (x := (0 : ℝ^n)) (t := 0) zero_lt_one
  have htime : ContDiff ℝ 1 fun q : ℝ × SpaceTime n ↦ time q.2 :=
    (timeCLM n).contDiff.comp contDiff_snd
  have hspace : ContDiff ℝ 1 fun q : ℝ × SpaceTime n ↦ spatialPart q.2 :=
    (spatialPartCLM n).contDiff.comp contDiff_snd
  have hP : ContDiff ℝ 1 (Function.uncurry P) := by
    change ContDiff ℝ 1 ((fun q : ℝ × ℝ^n ↦ timeSpaceCons q.1 q.2) ∘
      fun q : ℝ × SpaceTime n ↦ (t + q.1 ^ 2 * time q.2, x + q.1 • spatialPart q.2))
    exact (contDiff_timeSpaceCons_uncurry n).comp (by fun_prop)
  have hpartial (i : Fin (n + 1)) : Continuous fun q : ℝ × SpaceTime n ↦ (∂[i] u) (P q.1 q.2) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hu).continuous.comp hP.continuous
  have hcoord (j : Fin n) : Continuous fun q : ℝ × SpaceTime n ↦ spatialPart q.2 j :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hspace.continuous
  have htime' := htime.continuous
  have hD : Continuous fun q : ℝ × SpaceTime n ↦ D q.1 q.2 := by fun_prop
  have hW := integrableOn_heatBallWeight hn (0 : ℝ^n) 0 zero_lt_one
  have hjoint : Integrable (fun q : ℝ × SpaceTime n ↦ heatBallWeight 0 0 q.2 * D q.1 q.2)
      ((volume.restrict (Set.uIoc 0 r)).prod (volume.restrict (heatBall (0 : ℝ^n) 0 1))) := by
    rw [Measure.prod_restrict]
    refine IntegrableOn.mul_continuousOn_of_subset ?_ hD.continuousOn
      (measurableSet_uIoc.prod hB) (isCompact_uIcc.prod hK)
      (Set.prod_mono Set.uIoc_subset_uIcc subset_closure)
    rw [IntegrableOn, ← Measure.prod_restrict]
    simpa using (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.uIoc 0 r)).mul_prod hW
  have hFTC (p : SpaceTime n) : ∫ a in (0 : ℝ)..r, D a p = u (P r p) - u (P 0 p) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ ↦ by
      simpa only [D, P] using hasDerivAt_comp_heatBallParabolicMap_scale x t a p
        ((hu.differentiable one_ne_zero).differentiableAt))
      ((show Continuous fun a ↦ D a p from
        hD.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 r)
  have hterm (a : ℝ) : IntegrableOn (fun p ↦ heatBallWeight 0 0 p * u (P a p))
      (heatBall (0 : ℝ^n) 0 1) :=
    hW.mul_continuousOn_of_subset (hu.continuous.comp
      (hP.continuous.comp (continuous_const.prodMk continuous_id))).continuousOn
      hB hK subset_closure
  have hunitScale : ∫ p in heatBall (0 : ℝ^n) 0 1, heatBallWeight 0 0 p * u (P r p) =
      ∫ p in heatBall (0 : ℝ^n) 0 1, heatBallWeight 0 0 p * u (P 0 p) := by
    rw [← sub_eq_zero, ← integral_sub (hterm r) (hterm 0)]
    calc _ = ∫ p in heatBall (0 : ℝ^n) 0 1, ∫ a in (0 : ℝ)..r, heatBallWeight 0 0 p * D a p :=
          setIntegral_congr_fun hB fun p _ ↦ by
            simp only [intervalIntegral.integral_const_mul, hFTC, mul_sub]
      _ = 0 := by
        rw [← intervalIntegral_integral_swap (f := fun a p ↦ heatBallWeight 0 0 p * D a p)
          hjoint, intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ 0) hr.le
          fun a ha ↦ ?_, intervalIntegral.integral_zero]
        simpa only [D, P] using setIntegral_unitHeatBall_scaleDerivative_eq_zero hn hu huSpace
          x t ha.1 ha.2.le hcaloric
  have hP0 (p : SpaceTime n) : P 0 p = timeSpaceCons t x := by
    ext i
    cases i using Fin.cases <;> simp [P, heatBallParabolicMap, time]
  rw [heatBallWeighted_setIntegral_scaling u x t hr]
  change r ^ n * ∫ p in heatBall (0 : ℝ^n) 0 1, heatBallWeight 0 0 p * u (P r p) = _
  rw [hunitScale]
  simp only [hP0]
  rw [integral_mul_const, setIntegral_heatBallWeight hn 0 0 zero_lt_one]
  ring

end HeatEquation
