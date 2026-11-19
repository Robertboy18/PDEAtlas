/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CAS.IntegrationTactic

/-!
# Quadratic Taylor remainders

The integral Taylor formula gives a uniform remainder estimate from continuity of
the second Fréchet derivative. This yields the Peano remainder and the
quadratic limit of a rescaled stationary phase in an arbitrary real normed space.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral remainder uses the second derivative throughout the segment. -/
theorem quadratic_taylor_integral {f : E → ℝ} {x h : E}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • h)) :
    f (x + h) = f x + fderiv ℝ f x h +
      ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (x + t • h) h h := by
  simpa [Finset.sum_range_succ, iteratedFDeriv_two_apply] using
    map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) hf

/-- Uniform control of the Hessian gives a quadratic remainder bound in every direction. -/
theorem quadratic_taylor_remainder_le {f : E → ℝ} {x h : E} {η : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • h))
    (hη : 0 ≤ η)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (x + t • h) - fderiv ℝ (fderiv ℝ f) x‖ ≤ η) :
    ‖f (x + h) - f x - fderiv ℝ f x h -
      fderiv ℝ (fderiv ℝ f) x h h / 2‖ ≤ η * ‖h‖ ^ 2 := by
  let H := fderiv ℝ (fderiv ℝ f)
  have hcont : ContinuousOn (fun t : ℝ ↦ (1 - t) * H (x + t • h) h h) (Icc 0 1) := by
    intro t ht
    have hc : ContinuousAt H (x + t • h) :=
      (((hf t ht).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuousAt
    exact ((continuousAt_const.sub continuousAt_id).mul
      ((hc.comp (f := fun s : ℝ ↦ x + s • h) (by fun_prop)).clm_apply
        continuousAt_const |>.clm_apply
        continuousAt_const)).continuousWithinAt
  have hweight : (∫ t in (0 : ℝ)..1, (1 - t)) = (1 / 2 : ℝ) := by
    cas
  have hconst : (∫ t in (0 : ℝ)..1, (1 - t) * H x h h) = H x h h / 2 := by
    rw [intervalIntegral.integral_mul_const, hweight]
    ring
  have heq : f (x + h) - f x - fderiv ℝ f x h - H x h h / 2 =
      ∫ t in (0 : ℝ)..1, (1 - t) * ((H (x + t • h) - H x) h h) := by
    rw [quadratic_taylor_integral hf]
    simp_rw [show ∀ t : ℝ, (1 - t) * ((H (x + t • h) - H x) h h) =
        (1 - t) * H (x + t • h) h h - (1 - t) * H x h h by
      intro t; simp only [sub_apply]; ring]
    rw [intervalIntegral.integral_sub
      (by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le zero_le_one] using hcont)
      (by apply Continuous.intervalIntegrable; fun_prop), hconst]
    dsimp [H]
    ring
  change ‖f (x + h) - f x - fderiv ℝ f x h - H x h h / 2‖ ≤ _
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := η * ‖h‖ ^ 2)
    (f := fun t ↦ (1 - t) * ((H (x + t • h) - H x) h h)) ?_
  · simpa using hb
  intro t ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le zero_le_one] using ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨htIoc.1.le, htIoc.2⟩
  have hs : ‖1 - t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht'.2])]
    linarith [ht'.1]
  calc
    ‖(1 - t) * ((H (x + t • h) - H x) h h)‖ =
        ‖1 - t‖ * ‖(H (x + t • h) - H x) h h‖ := norm_mul _ _
    _ ≤ ‖1 - t‖ * (η * ‖h‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left
        (((H (x + t • h) - H x).le_opNorm₂ h h).trans
          (by gcongr; exact hH t ht')) (norm_nonneg _)
    _ ≤ 1 * (η * ‖h‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_right hs
        (mul_nonneg (mul_nonneg hη (norm_nonneg _)) (norm_nonneg _))
    _ = η * ‖h‖ ^ 2 := by ring

/-- Local C² regularity supplies Hessian control; no remainder estimate is assumed. -/
theorem exists_quadratic_remainder_bound {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ h : E, ‖h‖ < r →
      ‖f (x + h) - f x - fderiv ℝ f x h -
        fderiv ℝ (fderiv ℝ f) x h h / 2‖ ≤ η * ‖h‖ ^ 2 := by
  let H := fderiv ℝ (fderiv ℝ f)
  have hc : ContinuousAt H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, ‖H y - H x‖ < η := by
    have hd : ContinuousAt (fun y : E ↦ H y - H x) x :=
      hc.sub continuousAt_const
    have hn := ContinuousAt.norm (E := E →L[ℝ] E →L[ℝ] ℝ) hd
    have ht : Tendsto (fun y : E ↦ ‖H y - H x‖) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self, ContinuousLinearMap.opNorm_zero] using hn.tendsto
    exact ht.eventually (gt_mem_nhds hη)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and hnear)
  refine ⟨r, hr, fun h hh ↦ quadratic_taylor_remainder_le ?_ hη.le ?_⟩
  all_goals
    intro t ht
    have hseg : dist (x + t • h) x < r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans_lt hh
    first | exact (hball hseg).1 | exact (hball hseg).2.le

/-- The multivariate Peano remainder follows from local C² regularity. -/
theorem quadratic_taylor_isLittleO {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    Asymptotics.IsLittleO (𝓝 (0 : E))
      (fun h : E ↦ f (x + h) - f x - fderiv ℝ f x h -
        fderiv ℝ (fderiv ℝ f) x h h / 2)
      (fun h : E ↦ ‖h‖ ^ 2) := by
  apply Asymptotics.IsLittleO.of_bound
  intro η hη
  obtain ⟨r, hr, hbound⟩ := exists_quadratic_remainder_bound hf hη
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with h hh
  simpa only [norm_pow, norm_norm] using
    hbound h (by simpa only [Metric.mem_ball, dist_zero_right] using hh)

/-- The rescaled phase limit is derived from its Hessian, in any normed space. -/
theorem tendsto_rescaled_stationary_phase {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hstationary : fderiv ℝ f x = 0) (v : E) :
    Tendsto (fun ε : ℝ ↦ (f (x + ε • v) - f x) / ε ^ 2)
      (𝓝[>] 0) (𝓝 (fderiv ℝ (fderiv ℝ f) x v v / 2)) := by
  have hscale : Tendsto (fun ε : ℝ ↦ ε • v) (𝓝[>] 0) (𝓝 (0 : E)) := by
    simpa using (show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
      nhdsWithin_le_nhds).smul_const v
  have hrem :=
    ((quadratic_taylor_isLittleO hf).tendsto_div_nhds_zero.comp hscale).mul_const (‖v‖ ^ 2)
  have hlim := hrem.add_const (fderiv ℝ (fderiv ℝ f) x v v / 2)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  simp only [Function.comp_apply, hstationary, zero_apply, sub_zero]
  by_cases hv : v = 0
  · simp [hv]
  · simp only [map_smul, smul_apply, smul_eq_mul, norm_smul,
      Real.norm_of_nonneg hεpos.le]
    field_simp [ne_of_gt hεpos, norm_ne_zero_iff.mpr hv]
    ring

end PDE.Analysis
