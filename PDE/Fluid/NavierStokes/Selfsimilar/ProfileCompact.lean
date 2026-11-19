/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.TransportCutoff
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileSemigroup
public import PDE.Parabolic.Heat.WholeSpace.LocalizedCompact
import PDE.Analysis.Normed.Operator.Compact.Averages

/-!
# Compactness of the profile perturbation of the time-one map

Let `S` be the self-similar evolution around a profile with bounded transport coefficients `b`
and stretching coefficients `c`, and let `S₀` be the free self-similar heat evolution. If the
coefficients vanish at infinity, then `S(1) - S₀(1)` is a compact operator on vector `L²`.

By the Duhamel formula, `S(1) u - S₀(1) u = -∫₀¹ Π S₀(1 - s) B G(s) u ds`, where `B` is the
transport and `G(s)` is the gaining path, with `‖G(s)‖ ≲ s^{-1/2}`. Given `ε > 0`, let `χ` be
the indicator of a ball so large that `‖B - χ B‖` is small, and choose `θ` small. The integrals
over `[0, θ²]` and `[1 - θ, 1]` are small, and so is the integral with `B - χ B`. On
`[θ², 1 - θ]` the integrand with `χ B` is `Π S₀(1 - θ - s) C (B G(s) u)`, where `C = S₀(θ) χ` is
compact (heat smoothing after localization) and `B G(s) u` is bounded uniformly in `s` and in
`u` in the unit ball. So the integrand takes values in one compact set `Q`, and the integral
lies in a multiple of the closed convex hull of `Q`, which is compact. The image of the unit
ball therefore lies within every distance of a compact set.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Metric SobolevSpace SobolevSpace.GraphSpace
open IncompressibleFlow HeatEquation.WholeSpace PDE.Analysis.Evolution PDE.Analysis
open scoped ENNReal NNReal Sobolev Pointwise

namespace NavierStokes.Selfsimilar

/-! ### Duhamel integrals on the unit interval -/

variable (b : Fin 3 → DerivLp 3 ∞ Set.univ) (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ)

/-- The bounded transport of the coefficients `b` and `c`. -/
local notation "T₀" => (BoundedTransport.transport b c)

/-- The Duhamel integrand after `A` along the gaining path is integrable on `[0, 1]`. -/
theorem intervalIntegrable_transportLowerKernel_profileGain0
    (A : VectorH 3 1 →L[ℝ] VectorH 3 0)
    (u : VectorH 3 0) :
    IntervalIntegrable (fun s ↦ transportLowerKernel A (1 - s) (profileGain0 b c s u)) volume 0 1 :=
  intervalIntegrable_forwardIntegrand_of_bounded
    (continuous_transportLowerKernel_apply A).continuousOn
    (fun r _ ↦ norm_transportLowerKernel_le A r) (continuousOn_profileGain0_apply b c u)
    (fun _ hs ↦ norm_profileGain0_apply_le b c hs u) zero_le_one

/-- The constant in the bound of the profile Duhamel integrals on subintervals of `[0, 1]`. -/
def profileDuhamelConstant : ℝ :=
  2 * selfsimilarGraphConstant 3 0 * transportGainConstant T₀ * Real.exp (transportWeight T₀)

/-- The Duhamel constant is nonnegative. -/
theorem profileDuhamelConstant_nonneg : 0 ≤ profileDuhamelConstant b c := by
  have h1 := selfsimilarGraphConstant_nonneg 3 0
  have h2 := transportGainConstant_nonneg T₀
  unfold profileDuhamelConstant
  positivity

/-- The Duhamel integral over `[α, β] ⊆ [0, 1]` after a map `A` is bounded by
`C ‖A‖ ‖u‖ (√β - √α)`. -/
theorem norm_integral_transportLowerKernel_profileGain0_le (A : VectorH 3 1 →L[ℝ] VectorH 3 0)
    (u : VectorH 3 0) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    ‖∫ s in α..β, transportLowerKernel A (1 - s) (profileGain0 b c s u)‖ ≤
      profileDuhamelConstant b c * ‖A‖ * ‖u‖ * (Real.sqrt β - Real.sqrt α) := by
  have hS := selfsimilarGraphConstant_nonneg 3 0
  have hG := transportGainConstant_nonneg T₀
  have hω := (transportWeight_pos T₀).le
  set M := selfsimilarGraphConstant 3 0 * ‖A‖ * (transportGainConstant T₀ * ‖u‖) *
    Real.exp (transportWeight T₀) with hMdef
  calc
    _ ≤ ∫ s in α..β, M * s ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hαβ
      · refine Filter.Eventually.of_forall fun s hs ↦ ?_
        have hs0 : 0 < s := hα.trans_lt hs.1
        have hs1 : s ≤ 1 := hs.2.trans hβ
        have hpow := Real.rpow_nonneg hs0.le (-(1 / 2 : ℝ))
        have hexp : Real.exp (transportWeight T₀ * s) ≤ Real.exp (transportWeight T₀) :=
          Real.exp_le_exp.mpr (mul_le_of_le_one_right hω hs1)
        calc
          _ ≤ ‖transportLowerKernel A (1 - s)‖ * ‖profileGain0 b c s u‖ :=
            (transportLowerKernel A (1 - s)).le_opNorm _
          _ ≤ (selfsimilarGraphConstant 3 0 * ‖A‖) * (‖transportGainPath T₀ u‖ *
              s ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T₀ * s)) :=
            mul_le_mul (norm_transportLowerKernel_le A _) (norm_profileGain0_apply_le b c hs0 u)
              (norm_nonneg _) (mul_nonneg hS (norm_nonneg A))
          _ ≤ (selfsimilarGraphConstant 3 0 * ‖A‖) * ((transportGainConstant T₀ * ‖u‖) *
              s ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T₀)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hS (norm_nonneg A))
            apply mul_le_mul _ hexp (Real.exp_pos _).le
              (mul_nonneg (mul_nonneg hG (norm_nonneg u)) hpow)
            exact mul_le_mul_of_nonneg_right (norm_transportGainPath_apply_le T₀ u) hpow
          _ = M * s ^ (-(1 / 2 : ℝ)) := by
            rw [hMdef]
            ring
      · exact (intervalIntegrable_rpow_neg_one_half α β).const_mul M
    _ = M * (2 * Real.sqrt β - 2 * Real.sqrt α) := by
      rw [intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_interval_sub_left (intervalIntegrable_rpow_neg_one_half 0 β)
          (intervalIntegrable_rpow_neg_one_half 0 α),
        integral_rpow_neg_one_half, integral_rpow_neg_one_half]
    _ = _ := by
      rw [hMdef]
      unfold profileDuhamelConstant
      ring

/-! ### Compactness -/

/-- For `0 < θ ≤ 1/4` the interval `[θ², 1 - θ]` is nondegenerate. -/
private theorem sq_lt_one_sub {θ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) : θ ^ 2 < 1 - θ := by
  have h : θ ^ 2 ≤ θ * (1 / 4) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left hθ4 hθ.le
  linarith

variable {b c}

/-- At time one the difference of the two evolutions is minus the Duhamel integral. -/
theorem profileSemigroup0_sub_apply_one (hk : ProfileCoefficientBounds 0 b c) (u : VectorH 3 0) :
    (profileSemigroup0 b c hk 1 - vectorSelfsimilarHeatSemigroup 3 0 1) u =
      -∫ s in (0 : ℝ)..1, transportLowerKernel T₀ (1 - s)
        (profileGain0 b c s u) := by
  rw [sub_apply, profileSemigroup0_duhamel_l2, vectorSelfsimilarHeatSemigroup_apply,
    sub_sub_cancel_left]
  simp only [NNReal.coe_one]
  rfl

/-- After localization of the transport, the Duhamel integrand on `[θ², 1 - θ]` takes its
values, for all `u` in the unit ball, in one compact set. -/
theorem exists_isCompact_transportLowerKernel_mem {ψ : DerivLp 3 ∞ Set.univ} {K : Set (ℝ^3)}
    (hK : IsCompact K) (hψ : ∀ᵐ x ∂volume, ψ x = 0 ∨ x ∈ K) {θ : ℝ} (hθ : 0 < θ) :
    ∃ Q : Set (VectorH 3 0), IsCompact Q ∧ ∀ u : VectorH 3 0, ‖u‖ ≤ 1 →
      ∀ s ∈ Ioc (θ ^ 2) (1 - θ),
        transportLowerKernel ((vectorMul 3 ψ).comp T₀) (1 - s)
          (profileGain0 b c s u) ∈ Q := by
  let T := BoundedTransport.transport b c
  let δ : ℝ≥0 := ⟨θ, hθ.le⟩
  have hδ : 0 < δ := hθ
  let C := (vectorSelfsimilarHeat 3 0 δ).comp (vectorMul 3 ψ)
  have hC : IsCompactOperator C := isCompactOperator_vectorSelfsimilarHeat_comp_vectorMul hδ hK hψ
  let M := ‖T‖ * (transportGainConstant T₀ * θ⁻¹ * Real.exp (transportWeight T₀))
  obtain ⟨Kc, hKc, hCK⟩ := hC.image_closedBall_subset_compact M
  let Φ : ℝ≥0 × VectorH 3 0 → VectorH 3 0 :=
    fun p ↦ leraySobolev 3 0 (vectorSelfsimilarHeat 3 0 p.1 p.2)
  have hΦ : Continuous Φ := by
    have h := (vectorSelfsimilarHeatSemigroup 3 0).continuous_apply
    simp only [vectorSelfsimilarHeatSemigroup_apply] at h
    exact (leraySobolev 3 0).continuous.comp h
  refine ⟨Φ '' (Icc (0 : ℝ≥0) 1 ×ˢ Kc), (isCompact_Icc.prod hKc).image hΦ, ?_⟩
  intro u hu s hs
  have hθsq : 0 < θ ^ 2 := by positivity
  have hs0 : 0 < s := hθsq.trans hs.1
  have hs1 : 0 ≤ 1 - s - θ := by linarith [hs.2]
  have hG := transportGainConstant_nonneg T₀
  refine ⟨((1 - s - θ).toNNReal, C (T (profileGain0 b c s u))),
    ⟨⟨bot_le, ?_⟩, hCK ⟨_, ?_, rfl⟩⟩, ?_⟩
  · rw [Real.toNNReal_le_one]
    linarith
  · rw [mem_closedBall_zero_iff]
    have hpow := Real.rpow_nonneg hs0.le (-(1 / 2 : ℝ))
    have hroot : s ^ (-(1 / 2 : ℝ)) ≤ θ⁻¹ := by
      have h := Real.rpow_le_rpow_of_nonpos hθsq hs.1.le (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
      rwa [rpow_neg_one_half_eq_inv_sqrt hθsq.le, Real.sqrt_sq hθ.le] at h
    have hexp : Real.exp (transportWeight T₀ * s) ≤ Real.exp (transportWeight T₀) :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_right (transportWeight_pos T₀).le
        (by linarith [hs.2]))
    have hpath : ‖transportGainPath T₀ u‖ ≤ transportGainConstant T₀ :=
      (norm_transportGainPath_apply_le T₀ u).trans (mul_le_of_le_one_right hG hu)
    calc
      ‖T (profileGain0 b c s u)‖ ≤ ‖T‖ * ‖profileGain0 b c s u‖ := T.le_opNorm _
      _ ≤ M := by
        apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg T)
        calc
          ‖profileGain0 b c s u‖ ≤ ‖transportGainPath T₀ u‖ * s ^ (-(1 / 2 : ℝ)) *
              Real.exp (transportWeight T₀ * s) := norm_profileGain0_apply_le b c hs0 u
          _ ≤ transportGainConstant T₀ * θ⁻¹ * Real.exp (transportWeight T₀) :=
            mul_le_mul (mul_le_mul hpath hroot hpow hG) hexp (Real.exp_pos _).le
              (mul_nonneg hG (inv_nonneg.mpr hθ.le))
  · have hsum : (1 - s - θ).toNNReal + δ = (1 - s).toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hs1, Real.coe_toNNReal _ (by linarith)]
      change 1 - s - θ + θ = 1 - s
      ring
    change leraySobolev 3 0 (vectorSelfsimilarHeat 3 0 (1 - s - θ).toNNReal
      (vectorSelfsimilarHeat 3 0 δ (vectorMul 3 ψ (T (profileGain0 b c s u))))) =
        leraySobolev 3 0 (vectorSelfsimilarHeat 3 0 (1 - s).toNNReal
          (vectorMul 3 ψ (T (profileGain0 b c s u))))
    rw [← vectorSelfsimilarHeat_add, hsum]

variable (b c) in
/-- Removing the integrals over `[0, θ²]` and `[1 - θ, 1]` and the part of the coefficients
outside the localization changes the Duhamel integral by a small amount. -/
theorem norm_integral_transportLowerKernel_profileGain0_sub_le
    (A₁ A₂ : VectorH 3 1 →L[ℝ] VectorH 3 0)
    (u : VectorH 3 0) {θ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) :
    ‖(∫ s in (0 : ℝ)..1, transportLowerKernel (A₁ + A₂) (1 - s) (profileGain0 b c s u)) -
        ∫ s in (θ ^ 2)..(1 - θ), transportLowerKernel A₁ (1 - s) (profileGain0 b c s u)‖ ≤
      profileDuhamelConstant b c * ‖u‖ * (2 * ‖A₁‖ * θ + ‖A₂‖) := by
  let F : (VectorH 3 1 →L[ℝ] VectorH 3 0) → ℝ → VectorH 3 0 :=
    fun A s ↦ transportLowerKernel A (1 - s) (profileGain0 b c s u)
  have hθsq : 0 < θ ^ 2 := by positivity
  have hθsq1 : θ ^ 2 ≤ 1 - θ := (sq_lt_one_sub hθ hθ4).le
  have hI₁ : IntervalIntegrable (F A₁) volume 0 1 :=
    intervalIntegrable_transportLowerKernel_profileGain0 b c A₁ u
  have hI₂ : IntervalIntegrable (F A₂) volume 0 1 :=
    intervalIntegrable_transportLowerKernel_profileGain0 b c A₂ u
  have hsub (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
      IntervalIntegrable (F A₁) volume α β :=
    hI₁.mono_set (by
      rw [uIcc_of_le hαβ, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hα hβ)
  have hsplitT : (∫ s in (0 : ℝ)..1, F (A₁ + A₂) s) =
      (∫ s in (0 : ℝ)..1, F A₁ s) + ∫ s in (0 : ℝ)..1, F A₂ s := by
    rw [← intervalIntegral.integral_add hI₁ hI₂]
    apply intervalIntegral.integral_congr
    intro s _
    change transportLowerKernel (A₁ + A₂) (1 - s) _ =
      transportLowerKernel A₁ (1 - s) _ + transportLowerKernel A₂ (1 - s) _
    rw [transportLowerKernel_add, add_apply]
  have hsplit₁ : (∫ s in (0 : ℝ)..1, F A₁ s) =
      (∫ s in (0 : ℝ)..(θ ^ 2), F A₁ s) + (∫ s in (θ ^ 2)..(1 - θ), F A₁ s) +
        ∫ s in (1 - θ)..1, F A₁ s := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (hsub 0 (θ ^ 2) le_rfl hθsq.le (by linarith)) (hsub (θ ^ 2) (1 - θ) hθsq.le hθsq1
          (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals
        (hsub 0 (1 - θ) le_rfl (by linarith) (by linarith))
        (hsub (1 - θ) 1 (by linarith) (by linarith) le_rfl)]
  have e1 := norm_integral_transportLowerKernel_profileGain0_le b c A₁ u le_rfl hθsq.le
    (by linarith)
  have e2 := norm_integral_transportLowerKernel_profileGain0_le b c A₁ u (α := 1 - θ) (β := 1)
    (by linarith)
    (by linarith) le_rfl
  have e3 := norm_integral_transportLowerKernel_profileGain0_le b c A₂ u le_rfl zero_le_one le_rfl
  rw [Real.sqrt_sq hθ.le, Real.sqrt_zero, sub_zero] at e1
  rw [Real.sqrt_one] at e2
  rw [Real.sqrt_one, Real.sqrt_zero, sub_zero, mul_one] at e3
  have hroot : 1 - Real.sqrt (1 - θ) ≤ θ := by
    have h : 1 - θ ≤ Real.sqrt (1 - θ) := by
      rw [Real.le_sqrt (by linarith) (by linarith)]
      have h' : (1 - θ) * (1 - θ) ≤ (1 - θ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    linarith
  have hC₀ := profileDuhamelConstant_nonneg b c
  have hu0 := norm_nonneg u
  have hA₁0 := ContinuousLinearMap.opNorm_nonneg A₁
  have e2' : ‖∫ s in (1 - θ)..1, F A₁ s‖ ≤ profileDuhamelConstant b c * ‖A₁‖ * ‖u‖ * θ :=
    e2.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  change ‖(∫ s in (0 : ℝ)..1, F (A₁ + A₂) s) - ∫ s in (θ ^ 2)..(1 - θ), F A₁ s‖ ≤ _
  rw [hsplitT, hsplit₁]
  calc
    _ = ‖(∫ s in (0 : ℝ)..(θ ^ 2), F A₁ s) + (∫ s in (1 - θ)..1, F A₁ s) +
        ∫ s in (0 : ℝ)..1, F A₂ s‖ := by
      congr 1
      abel
    _ ≤ ‖∫ s in (0 : ℝ)..(θ ^ 2), F A₁ s‖ + ‖∫ s in (1 - θ)..1, F A₁ s‖ +
        ‖∫ s in (0 : ℝ)..1, F A₂ s‖ := norm_add₃_le
    _ ≤ profileDuhamelConstant b c * ‖A₁‖ * ‖u‖ * θ +
        profileDuhamelConstant b c * ‖A₁‖ * ‖u‖ * θ +
        profileDuhamelConstant b c * ‖A₂‖ * ‖u‖ := add_le_add (add_le_add e1 e2') e3
    _ = _ := by ring

variable (b c) in
/-- If the transport and stretching coefficients vanish at infinity, the difference between
the profile semigroup and the free self-similar semigroup at time one is compact on vector
`L²`. -/
theorem isCompactOperator_profileSemigroup_sub (hk : ProfileCoefficientBounds 0 b c)
    (hb : BoundedTransport.CoefficientsVanishAtInfinity b c) :
    IsCompactOperator (profileSemigroup0 b c hk 1 - vectorSelfsimilarHeatSemigroup 3 0 1) := by
  apply isCompactOperator_of_forall_exists_dist_lt
  intro ε hε
  have hC₀ := profileDuhamelConstant_nonneg b c
  obtain ⟨ψ, K, hK, hψ, hA₂⟩ := BoundedTransport.exists_vectorMul_cutoff hb
    (ε := ε / (3 * (profileDuhamelConstant b c + 1))) (by positivity)
  let T := BoundedTransport.transport b c
  let A₁ := (vectorMul 3 ψ).comp T
  have hTA : T = A₁ + (T - A₁) := (add_sub_cancel A₁ T).symm
  set X := profileDuhamelConstant b c * ‖A₁‖ with hXdef
  have hX : 0 ≤ X := mul_nonneg hC₀ (ContinuousLinearMap.opNorm_nonneg _)
  set θ := min (1 / 4 : ℝ) (ε / (6 * (X + 1))) with hθdef
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ4 : θ ≤ 1 / 4 := min_le_left _ _
  have hXθ : 2 * X * θ < ε / 3 := by
    have h1 : θ ≤ ε / (6 * (X + 1)) := min_le_right _ _
    have h2 : 2 * X * θ ≤ 2 * X * (ε / (6 * (X + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * X * (ε / (6 * (X + 1))) = ε / 3 * (X / (X + 1)) := by
      field_simp
      ring
    have h4 : X / (X + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    have h5 : ε / 3 * (X / (X + 1)) < ε / 3 := mul_lt_of_lt_one_right (by positivity) h4
    linarith
  have hA₂' : profileDuhamelConstant b c * ‖T - A₁‖ ≤ ε / 3 := by
    have h1 := mul_le_mul_of_nonneg_left hA₂ hC₀
    have h2 : profileDuhamelConstant b c * (ε / (3 * (profileDuhamelConstant b c + 1))) =
        ε / 3 * (profileDuhamelConstant b c / (profileDuhamelConstant b c + 1)) := by
      field_simp
    have h3 : profileDuhamelConstant b c / (profileDuhamelConstant b c + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    have h4 := mul_le_of_le_one_right (by positivity : 0 ≤ ε / 3) h3
    linarith
  obtain ⟨Q, hQ, hQmem⟩ := exists_isCompact_transportLowerKernel_mem (b := b) (c := c) hK hψ hθ
  have hθsq1 : θ ^ 2 < 1 - θ := sq_lt_one_sub hθ hθ4
  refine ⟨-(((1 - θ) - θ ^ 2) • closedConvexHull ℝ Q),
    ((isCompact_closedConvexHull hQ).smul _).neg, fun u hu ↦ ?_⟩
  have hu1 : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le
  have hint : IntervalIntegrable (fun s ↦ transportLowerKernel A₁ (1 - s) (profileGain0 b c s u))
      volume (θ ^ 2) (1 - θ) :=
    (intervalIntegrable_transportLowerKernel_profileGain0 b c A₁ u).mono_set (by
      rw [uIcc_of_le hθsq1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (by positivity) (by linarith))
  refine ⟨-(∫ s in (θ ^ 2)..(1 - θ), transportLowerKernel A₁ (1 - s) (profileGain0 b c s u)),
    neg_mem_neg.mpr (intervalIntegral_mem_smul_closedConvexHull hθsq1 hint
      (hQmem u hu1)), ?_⟩
  rw [profileSemigroup0_sub_apply_one hk u, dist_neg_neg, dist_eq_norm]
  change ‖(∫ s in (0 : ℝ)..1, transportLowerKernel T (1 - s) (profileGain0 b c s u)) - _‖ < ε
  rw [hTA]
  refine (norm_integral_transportLowerKernel_profileGain0_sub_le b c A₁ (T - A₁) u hθ
    hθ4).trans_lt ?_
  have hu0 := norm_nonneg u
  have hA0 := ContinuousLinearMap.opNorm_nonneg (T - A₁)
  calc
    profileDuhamelConstant b c * ‖u‖ * (2 * ‖A₁‖ * θ + ‖T - A₁‖) =
        ‖u‖ * (2 * X * θ + profileDuhamelConstant b c * ‖T - A₁‖) := by
      rw [hXdef]
      ring
    _ ≤ 1 * (2 * X * θ + profileDuhamelConstant b c * ‖T - A₁‖) :=
      mul_le_mul_of_nonneg_right hu1 (by positivity)
    _ < ε := by linarith

end NavierStokes.Selfsimilar
