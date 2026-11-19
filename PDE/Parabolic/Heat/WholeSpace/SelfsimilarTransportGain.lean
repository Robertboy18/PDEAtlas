/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarForward

/-!
# Gaining paths of self-similar evolution perturbed by an operator losing one derivative

Let `T` be a bounded operator from vector `Hᵏ⁺¹(ℝ³)` to vector `Hᵏ(ℝ³)`, for example the
transport `v ↦ Σᵢ bᵢ ∂ᵢ v + c v` with coefficients in `W^{k,∞}`. The evolution `S` on vector
`Hᵏ` with generator `L₀ - Π T` solves the Duhamel equation
`S(t) u = S₀(t) u - ∫₀ᵗ Π S₀(t - s) T S(s) u ds`, where `S₀` is the free self-similar heat
evolution and `Π` is the Leray projection.

The unknown of the construction is the gaining path `t ↦ S(t) u` in `Hᵏ⁺¹`, with the weight
`√t e^{-ω t}`. The free gain `‖S₀(t)‖_{Hᵏ → Hᵏ⁺¹} ≲ t^{-1/2}` makes the Volterra operator a
contraction for a large rate `ω`, and the gaining path is its fixed point. It solves the
Duhamel equation in `Hᵏ⁺¹`, has the bound `C t^{-1/2} e^{ω t}`, and is the only path in `Hᵏ⁺¹`
that is continuous at positive times, solves the Duhamel equation and has a singular bound
`C t^{-1/2} e^{ω' t}`, with any rate `ω'`.

Let `T'` be an operator from `Hᵏ⁺²` to `Hᵏ⁺¹` that agrees with `T` once the top order is
forgotten. Forgetting the top order of the gaining path of `T'` gives a path that solves the
Duhamel equation of `T`, so uniqueness identifies it with the gaining path of `T`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped NNReal Sobolev BoundedContinuousFunction

namespace HeatEquation.WholeSpace

variable {k : ℕ} (T : VectorH 3 (k + 1) →L[ℝ] VectorH 3 k)

/-! ### Kernels -/

/-- The projected free gain after the operator `T`, as a kernel on vector `Hᵏ⁺¹`. -/
def transportKernel (r : ℝ) : VectorH 3 (k + 1) →L[ℝ] VectorH 3 (k + 1) :=
  (projectedSelfsimilarHeatGainKernel 3 k r).comp T

/-- The kernel applies `T` and then the projected free gain. -/
@[simp]
theorem transportKernel_apply (r : ℝ) (v : VectorH 3 (k + 1)) :
    transportKernel T r v = projectedSelfsimilarHeatGainKernel 3 k r (T v) :=
  rfl

/-- The constant in the square-root bound of the kernel. -/
def transportKernelBound : ℝ :=
  singularSelfsimilarConstant 3 k 0 * ‖T‖

/-- The square-root constant of the kernel is nonnegative. -/
theorem transportKernelBound_nonneg : 0 ≤ transportKernelBound T :=
  mul_nonneg (singularSelfsimilarConstant_nonneg 3 k 0) (norm_nonneg T)

/-- The kernel has the square-root bound `‖K(r)‖ ≤ M r^{-1/2}` at positive lag. -/
theorem norm_transportKernel_le {r : ℝ} (hr : 0 < r) :
    ‖transportKernel T r‖ ≤ transportKernelBound T * r ^ (-(1 / 2 : ℝ)) := by
  have hG := norm_projectedSelfsimilarHeatGainKernel_le_singular_exp (n := 3) (k := k)
    (ω := 0) (by norm_num) hr
  rw [zero_mul, Real.exp_zero, mul_one] at hG
  calc
    ‖transportKernel T r‖ ≤ ‖projectedSelfsimilarHeatGainKernel 3 k r‖ * ‖T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (singularSelfsimilarConstant 3 k 0 * r ^ (-(1 / 2 : ℝ))) * ‖T‖ :=
      mul_le_mul_of_nonneg_right hG (norm_nonneg T)
    _ = _ := by
      unfold transportKernelBound
      ring

/-- The action of the kernel is jointly continuous at positive lag. -/
theorem continuousOn_transportKernel_apply :
    ContinuousOn (fun p : ℝ × VectorH 3 (k + 1) ↦ transportKernel T p.1 p.2)
      (Ioi 0 ×ˢ univ) := by
  have h := continuousOn_projectedSelfsimilarHeatGainKernel_apply (n := 3) (k := k)
  have hmap : Continuous (fun p : ℝ × VectorH 3 (k + 1) ↦ (p.1, T p.2)) :=
    continuous_fst.prodMk (T.continuous.comp continuous_snd)
  have hmaps : MapsTo (fun p : ℝ × VectorH 3 (k + 1) ↦ (p.1, T p.2))
      (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hcomp := ContinuousOn.comp h hmap.continuousOn hmaps
  simpa only [Function.comp_def, transportKernel_apply] using hcomp

/-- The projected free evolution after `T`, as a kernel from `Hᵏ⁺¹` to `Hᵏ`. -/
def transportLowerKernel (r : ℝ) : VectorH 3 (k + 1) →L[ℝ] VectorH 3 k :=
  (leraySobolev 3 k).comp ((vectorSelfsimilarHeat 3 k r.toNNReal).comp T)

@[simp]
theorem transportLowerKernel_apply (r : ℝ) (v : VectorH 3 (k + 1)) :
    transportLowerKernel T r v =
      leraySobolev 3 k (vectorSelfsimilarHeat 3 k r.toNNReal (T v)) :=
  rfl

/-- The kernel without gain is uniformly bounded, since the free evolution is bounded in
dimension three. -/
theorem norm_transportLowerKernel_le (r : ℝ) :
    ‖transportLowerKernel T r‖ ≤ selfsimilarGraphConstant 3 k * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (selfsimilarGraphConstant_nonneg 3 k) (norm_nonneg T))
  intro v
  rw [transportLowerKernel_apply]
  calc
    _ ≤ ‖vectorSelfsimilarHeat 3 k r.toNNReal (T v)‖ := norm_leraySobolev_le _
    _ ≤ selfsimilarGraphConstant 3 k * ‖T v‖ :=
      norm_vectorSelfsimilarHeat_le_of_two_le (by norm_num) _ _
    _ ≤ selfsimilarGraphConstant 3 k * (‖T‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm v) (selfsimilarGraphConstant_nonneg 3 k)
    _ = _ := by ring

/-- The action of the kernel without gain is jointly continuous, including lag zero. -/
theorem continuous_transportLowerKernel_apply :
    Continuous (fun p : ℝ × VectorH 3 (k + 1) ↦ transportLowerKernel T p.1 p.2) := by
  have h := (vectorSelfsimilarHeatSemigroup 3 k).continuous_apply
  have hmap : Continuous (fun p : ℝ × VectorH 3 (k + 1) ↦ (p.1.toNNReal, T p.2)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk (T.continuous.comp continuous_snd)
  have hcomp := h.comp hmap
  simp only [Function.comp_def, vectorSelfsimilarHeatSemigroup_apply] at hcomp
  simp only [transportLowerKernel_apply]
  exact (leraySobolev 3 k).continuous.comp hcomp

/-- The kernel without gain is additive in the operator. -/
theorem transportLowerKernel_add (T' : VectorH 3 (k + 1) →L[ℝ] VectorH 3 k) (r : ℝ) :
    transportLowerKernel (T + T') r = transportLowerKernel T r + transportLowerKernel T' r := by
  simp only [transportLowerKernel, ContinuousLinearMap.comp_add]

/-- At positive lag, forgetting the gained derivative of the kernel gives the kernel without
gain. -/
theorem vectorLower_transportKernel {r : ℝ} (hr : 0 < r) (v : VectorH 3 (k + 1)) :
    vectorLower 3 k (transportKernel T r v) = transportLowerKernel T r v := by
  rw [transportKernel_apply, vectorLower_projectedSelfsimilarHeatGainKernel hr,
    transportLowerKernel_apply]

/-- The kernel at lag `τ + σ` is the kernel without gain at lag `σ` followed by free gain. -/
theorem transportKernel_add {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ) (v : VectorH 3 (k + 1)) :
    transportKernel T (τ + σ) v =
      vectorSelfsimilarHeatGainKernel 3 k τ (transportLowerKernel T σ v) := by
  rw [transportKernel_apply, projectedSelfsimilarHeatGainKernel_add hτ hσ,
    transportLowerKernel_apply]

/-! ### The Volterra equation -/

/-- An exponential weight that makes the perturbation a contraction. -/
def transportWeight : ℝ := (2 * forwardSmoothingConstant * transportKernelBound T + 1) ^ 2

/-- The weight is positive. -/
theorem transportWeight_pos : 0 < transportWeight T := by
  have h1 := transportKernelBound_nonneg T
  have h2 := forwardSmoothingConstant_nonneg
  unfold transportWeight
  positivity

/-- The square root of the weight is `2 * forwardSmoothingConstant * M + 1`. -/
theorem sqrt_transportWeight :
    Real.sqrt (transportWeight T) = 2 * forwardSmoothingConstant * transportKernelBound T + 1 := by
  have h1 := transportKernelBound_nonneg T
  have h2 := forwardSmoothingConstant_nonneg
  exact Real.sqrt_sq (by positivity)

/-- The Volterra operator of the perturbation on weighted gaining paths. -/
def transportVolterra :
    (Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)) →L[ℝ] (Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)) :=
  forwardSmoothingOperator (transportKernel T) (transportWeight_pos T)
    (continuousOn_transportKernel_apply T) (fun _ hr ↦ norm_transportKernel_le T hr)

/-- At the weight the contraction factor `forwardSmoothingConstant * M / √ω` is at most one
half. -/
theorem forwardSmoothingConstant_mul_div_sqrt_transportWeight_le :
    forwardSmoothingConstant * transportKernelBound T / Real.sqrt (transportWeight T) ≤
      1 / 2 := by
  have h1 := transportKernelBound_nonneg T
  have h2 := forwardSmoothingConstant_nonneg
  rw [sqrt_transportWeight, div_le_iff₀ (by positivity)]
  nlinarith

/-- The Volterra operator has norm at most one half. -/
theorem norm_transportVolterra_le : ‖transportVolterra T‖ ≤ 1 / 2 :=
  (norm_forwardSmoothingOperator_le _ _ _ _).trans
    (forwardSmoothingConstant_mul_div_sqrt_transportWeight_le T)

/-- The Volterra operator halves the norm of each weighted path. -/
theorem norm_transportVolterra_apply_le (w : Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)) :
    ‖transportVolterra T w‖ ≤ 1 / 2 * ‖w‖ :=
  (norm_forwardSmoothingOperator_apply_le _ _ _ _ w).trans (mul_le_mul_of_nonneg_right
    (forwardSmoothingConstant_mul_div_sqrt_transportWeight_le T) (norm_nonneg w))

/-- The Volterra operator has norm less than one, so `1 + V` is invertible. -/
theorem norm_transportVolterra_lt : ‖transportVolterra T‖ < 1 :=
  (norm_transportVolterra_le T).trans_lt (by norm_num)

/-- The weight lies above the free decay rate `(2 - 3) / 4` of three dimensions. -/
theorem lt_transportWeight : ((2 : ℝ) - (3 : ℕ)) / 4 < transportWeight T := by
  have h := transportWeight_pos T
  norm_num
  linarith

/-- The Volterra operator is the weighted forward Duhamel integral of the decoded path. -/
theorem transportVolterra_apply (w : Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)) (t : Ioi (0 : ℝ)) :
    transportVolterra T w t = (Real.sqrt t * Real.exp (-(transportWeight T * t))) •
      forwardDuhamel (transportKernel T) (forwardDecode (transportWeight T) w) t :=
  forwardSmoothingOperator_apply _ _ _ _ w t

/-- The weighted gaining path of the evolution: the fixed point of the Volterra equation whose
forcing is the free gaining path. -/
def transportGainPath : VectorH 3 k →L[ℝ] (Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)) :=
  ContinuousLinearMap.comp
    (inverseOneAdd (X := Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)) (transportVolterra T)
      (norm_transportVolterra_lt T))
    (vectorSelfsimilarHeatGainPath 3 k (transportWeight T) (lt_transportWeight T))

/-- The fixed-point equation of the weighted gaining path. -/
theorem transportGainPath_add_transportVolterra (u : VectorH 3 k) :
    transportGainPath T u + transportVolterra T (transportGainPath T u) =
      vectorSelfsimilarHeatGainPath 3 k (transportWeight T) (lt_transportWeight T) u :=
  inverseOneAdd_add_apply _ _ _

/-- The fixed point is the only bounded weighted path solving the Volterra equation. -/
theorem eq_transportGainPath {u : VectorH 3 k} {w : Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1)}
    (h : w + transportVolterra T w =
      vectorSelfsimilarHeatGainPath 3 k (transportWeight T) (lt_transportWeight T) u) :
    w = transportGainPath T u :=
  eq_inverseOneAdd _ _ h

/-- The constant in the bound of the weighted gaining path. -/
def transportGainConstant : ℝ := 2 * singularSelfsimilarConstant 3 k (transportWeight T)

/-- The constant of the weighted gaining path is nonnegative. -/
theorem transportGainConstant_nonneg : 0 ≤ transportGainConstant T :=
  mul_nonneg zero_le_two (singularSelfsimilarConstant_nonneg _ _ _)

/-- The weighted gaining path is at most twice the free weighted gaining path. -/
theorem norm_transportGainPath_apply_le (u : VectorH 3 k) :
    ‖transportGainPath T u‖ ≤ transportGainConstant T * ‖u‖ := by
  calc
    ‖transportGainPath T u‖ ≤
        2 * ‖vectorSelfsimilarHeatGainPath 3 k (transportWeight T) (lt_transportWeight T) u‖ :=
      norm_le_two_mul_of_add_eq (transportGainPath_add_transportVolterra T u)
        (norm_transportVolterra_apply_le T _)
    _ ≤ 2 * (singularSelfsimilarConstant 3 k (transportWeight T) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_vectorSelfsimilarHeatGainPath_apply_le _ u) zero_le_two
    _ = _ := by
      unfold transportGainConstant
      ring

/-! ### The gaining path -/

/-- The gaining path of the evolution at positive times, extended by zero. -/
def transportGain (t : ℝ) : VectorH 3 k →L[ℝ] VectorH 3 (k + 1) :=
  if ht : 0 < t then
    (t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T * t)) •
      (BoundedContinuousFunction.evalCLM ℝ (⟨t, ht⟩ : Ioi (0 : ℝ))).comp (transportGainPath T)
  else 0

/-- The gaining path is the decoded weighted fixed point. -/
theorem transportGain_apply (t : ℝ) (u : VectorH 3 k) :
    transportGain T t u = forwardDecode (transportWeight T) (transportGainPath T u) t := by
  by_cases ht : 0 < t
  · rw [transportGain, dite_eq_left ht, forwardDecode_of_pos _ _ ht]
    rfl
  · rw [transportGain, dite_eq_right ht, forwardDecode_of_nonpos _ _ (not_lt.mp ht)]
    rfl

/-- The gaining path vanishes at nonpositive times. -/
theorem transportGain_of_nonpos {t : ℝ} (ht : t ≤ 0) : transportGain T t = 0 :=
  dite_eq_right (not_lt.mpr ht)

/-- At positive times the gaining path has the singular bound with the constant
`‖transportGainPath T u‖`. -/
theorem norm_transportGain_apply_le {t : ℝ} (ht : 0 < t) (u : VectorH 3 k) :
    ‖transportGain T t u‖ ≤
      ‖transportGainPath T u‖ * t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T * t) := by
  rw [transportGain_apply]
  exact norm_forwardDecode_le _ _ ht

/-- The gaining path is continuous at positive times. -/
theorem continuousOn_transportGain_apply (u : VectorH 3 k) :
    ContinuousOn (fun t ↦ transportGain T t u) (Ioi 0) := by
  have h : (fun t ↦ transportGain T t u) =
      forwardDecode (transportWeight T) (transportGainPath T u) := by
    funext t
    exact transportGain_apply T t u
  rw [h]
  exact continuousOn_forwardDecode _ _

/-- The Duhamel integrand of the gaining path is integrable on `[0, t]`. -/
theorem intervalIntegrable_transportKernel {t : ℝ} (ht : 0 ≤ t) (u : VectorH 3 k) :
    IntervalIntegrable (fun s ↦ transportKernel T (t - s) (transportGain T s u)) volume 0 t :=
  intervalIntegrable_forwardIntegrand (continuousOn_transportKernel_apply T)
    (fun _ hr ↦ norm_transportKernel_le T hr) (continuousOn_transportGain_apply T u)
    (fun _ hs ↦ norm_transportGain_apply_le T hs u) ht

/-- The Duhamel integrand without gain is integrable on `[0, t]`. -/
theorem intervalIntegrable_transportLowerKernel {t : ℝ} (ht : 0 ≤ t) (u : VectorH 3 k) :
    IntervalIntegrable (fun s ↦ transportLowerKernel T (t - s) (transportGain T s u))
      volume 0 t :=
  intervalIntegrable_forwardIntegrand_of_bounded
    (continuous_transportLowerKernel_apply T).continuousOn
    (fun r _ ↦ norm_transportLowerKernel_le T r) (continuousOn_transportGain_apply T u)
    (fun _ hs ↦ norm_transportGain_apply_le T hs u) ht

/-- The gaining path solves the Duhamel equation in vector `Hᵏ⁺¹`: by definition of
`forwardDuhamel`, the integral is `∫₀ᵗ Π S₀(t - s) T (gain(s) u) ds` with the projected free
gain `projectedSelfsimilarHeatGainKernel 3 k` as kernel. -/
theorem transportGain_eq_forwardDuhamel {t : ℝ} (ht : 0 < t) (u : VectorH 3 k) :
    transportGain T t u = vectorSelfsimilarHeatGainKernel 3 k t u -
      forwardDuhamel (transportKernel T) (fun s ↦ transportGain T s u) t := by
  have hfix := congrArg (fun w : Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1) ↦ w ⟨t, ht⟩)
    (transportGainPath_add_transportVolterra T u)
  have hdec : forwardDecode (transportWeight T) (transportGainPath T u) =
      fun s ↦ transportGain T s u := by
    funext s
    exact (transportGain_apply T s u).symm
  change transportGainPath T u ⟨t, ht⟩ +
      (Real.sqrt t * Real.exp (-(transportWeight T * t))) •
        forwardDuhamel (transportKernel T)
          (forwardDecode (transportWeight T) (transportGainPath T u)) t =
      (Real.sqrt t * Real.exp (-(transportWeight T * t))) •
        vectorSelfsimilarHeatGainKernel 3 k t u at hfix
  rw [hdec] at hfix
  have hW : transportGainPath T u ⟨t, ht⟩ =
      (Real.sqrt t * Real.exp (-(transportWeight T * t))) •
        (vectorSelfsimilarHeatGainKernel 3 k t u -
          forwardDuhamel (transportKernel T) (fun s ↦ transportGain T s u) t) := by
    rw [smul_sub, ← hfix]
    abel
  rw [transportGain_apply T t u, forwardDecode_of_pos _ _ ht, hW, smul_smul,
    rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp ht _, one_smul, ← hdec]

/-- The gaining path is the only solution of the `Hᵏ⁺¹` Duhamel equation that is continuous at
positive times and has a singular bound `C t^{-1/2} e^{ω t}`, for any rate `ω`. -/
theorem eq_transportGain_of_duhamel {u : VectorH 3 k} {v : ℝ → VectorH 3 (k + 1)}
    (hvc : ContinuousOn v (Ioi 0)) {C ω : ℝ}
    (hvb : ∀ t, 0 < t → ‖v t‖ ≤ C * t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t))
    (hv : ∀ t, 0 < t → v t = vectorSelfsimilarHeatGainKernel 3 k t u -
      ∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 k (t - s) (T (v s)))
    {t : ℝ} (ht : 0 < t) : v t = transportGain T t u := by
  refine eq_of_add_forwardDuhamel_eq (transportKernel T) (continuousOn_transportKernel_apply T)
    (fun _ hr ↦ norm_transportKernel_le T hr) hvc (continuousOn_transportGain_apply T u) hvb
    (fun _ hs ↦ norm_transportGain_apply_le T hs u) (fun τ hτ ↦ ?_) ht
  rw [transportGain_eq_forwardDuhamel T hτ u, sub_add_cancel, hv τ hτ]
  simp only [forwardDuhamel, transportKernel_apply, sub_add_cancel]

/-- The gaining path of a field fixed by the Leray projection is fixed by the Leray
projection. -/
theorem leraySobolev_transportGain {t : ℝ} (ht : 0 < t) {u : VectorH 3 k}
    (hu : leraySobolev 3 k u = u) :
    leraySobolev 3 (k + 1) (transportGain T t u) = transportGain T t u := by
  rw [transportGain_eq_forwardDuhamel T ht u, map_sub, forwardDuhamel,
    ← (leraySobolev 3 (k + 1)).intervalIntegral_comp_comm
      (intervalIntegrable_transportKernel T ht.le u),
    vectorSelfsimilarHeatGainKernel_eq_toNNReal ht, leraySobolev_vectorSelfsimilarHeatGain, hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [transportKernel_apply, projectedSelfsimilarHeatGainKernel,
    ContinuousLinearMap.comp_apply, leraySobolev_idempotent]

/-! ### Restriction to the next order -/

section Restriction

variable (T' : VectorH 3 (k + 2) →L[ℝ] VectorH 3 (k + 1))
  (hT : ∀ v, vectorLower 3 k (T' v) = T (vectorLower 3 (k + 1) v))
include hT

/-- Forgetting the top order commutes with the kernels of `T'` and `T`. -/
theorem vectorLower_transportKernel_succ (r : ℝ) (v : VectorH 3 (k + 2)) :
    vectorLower 3 (k + 1) (transportKernel T' r v) =
      transportKernel T r (vectorLower 3 (k + 1) v) := by
  rw [transportKernel_apply, transportKernel_apply,
    vectorLower_succ_projectedSelfsimilarHeatGainKernel, hT]

/-- The gaining path of `T'`, with the top order forgotten, is the gaining path of `T` of the
datum with the top order forgotten. -/
theorem vectorLower_transportGain {t : ℝ} (ht : 0 < t) (u : VectorH 3 (k + 1)) :
    vectorLower 3 (k + 1) (transportGain T' t u) = transportGain T t (vectorLower 3 k u) := by
  have hc : ContinuousOn (fun s ↦ vectorLower 3 (k + 1) (transportGain T' s u)) (Ioi 0) :=
    (vectorLower 3 (k + 1)).continuous.comp_continuousOn (continuousOn_transportGain_apply T' u)
  refine eq_of_add_forwardDuhamel_eq (transportKernel T) (continuousOn_transportKernel_apply T)
    (fun _ hr ↦ norm_transportKernel_le T hr) hc
    (continuousOn_transportGain_apply T (vectorLower 3 k u))
    (fun s hs ↦ (norm_vectorLower_le _).trans (norm_transportGain_apply_le T' hs u))
    (fun s hs ↦ norm_transportGain_apply_le T hs _) (fun τ hτ ↦ ?_) ht
  have hlow : vectorLower 3 (k + 1)
      (forwardDuhamel (transportKernel T') (fun s ↦ transportGain T' s u) τ) =
      forwardDuhamel (transportKernel T) (fun s ↦ vectorLower 3 (k + 1) (transportGain T' s u))
        τ := by
    rw [forwardDuhamel, ← (vectorLower 3 (k + 1)).intervalIntegral_comp_comm
      (intervalIntegrable_transportKernel T' hτ.le u), forwardDuhamel]
    apply intervalIntegral.integral_congr
    intro s _
    exact vectorLower_transportKernel_succ T T' hT _ _
  rw [transportGain_eq_forwardDuhamel T hτ (vectorLower 3 k u), sub_add_cancel,
    transportGain_eq_forwardDuhamel T' hτ u, map_sub, hlow,
    vectorLower_succ_vectorSelfsimilarHeatGainKernel, sub_add_cancel]

end Restriction

end HeatEquation.WholeSpace
