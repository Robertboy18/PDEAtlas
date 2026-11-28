/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Lagrangian
public import PDE.Analysis.ODE.Flow.IntegralEstimates
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Lower-order a priori bounds of solutions of a half-plane system

This module proves the lower-order bounds of the continuation criterion: the quantities of a
solution of a half-plane system that are controlled by the data and by the time integral of the
velocity gradient alone, without any pointwise bound of that gradient. The gradient of the vorticity
and the Hessian of the temperature are treated in `APrioriTop.lean`, `APrioriTopBounds.lean` and
`APriori.lean`.

Let `sol` solve the system with the velocity law `U` and the forcing coefficient `κ` on `[0, b]`,
with velocity a `C¹` field, and let `A t` bound the derivative of the velocity on the closed
half-plane `H̄` at time `t`, with `∫₀ᵇ A ≤ Λ`. The flow of the velocity (`trajectory`, `label`) has
first variations bounded by `exp Λ` and is `exp Λ`-Lipschitz on `H̄`, whatever the size of `A`
pointwise: the first variation solves a linear equation with the coefficient `Du`, and the closed
half-plane is convex and invariant under the flow. Through the Lagrangian form of the solution this
bounds, for data of the class `IsHolderData … α R N`, in terms of the data at time `0`, the bound
`|κ| ≤ Bκ 0` and `Λ` only: the temperature and its gradient, the vorticity, the velocity, and the
supports, which move by at most this velocity times the time.

## Main results

* `IsSolutionOn.norm_variation_le`, `IsSolutionOn.norm_inverseVariation_le`: the first variation of
  the flow from time `0` to time `s`, and back, is bounded by `exp Λ` on `H̄`.
* `IsSolutionOn.norm_trajectory_sub_le`, `IsSolutionOn.norm_label_sub_le`: trajectories and labels
  are `exp Λ`-Lipschitz on `H̄`.
* `IsSolutionOn.abs_temperature_le`, `IsSolutionOn.norm_fderiv_temperature_le`: `|θ| ≤ N` and
  `‖∇θ‖ ≤ N exp Λ` on `H̄`; `IsSolutionOn.fderiv_temperature_eq` is the formula
  `∇θ(s, x) = ∇θ₀(label) ∘ W` with the inverse first variation `W`.
* `IsSolutionOn.abs_vorticity_le`: `|ω(s)| ≤ N + s Bκ₀ N exp Λ` on `H̄`.
* `IsSolutionOn.norm_velocity_le`: `‖u(s)‖ ≤ C 0 0 (N + b Bκ₀ N exp Λ)` on `H̄`.
* `IsSolutionOn.eq_zero_of_label`, `IsSolutionOn.eq_zero_of_norm`: both fields vanish at a point
  whose label lies outside the support disc of the data, hence outside the disc of radius `R + V b`,
  `V` the bound of the velocity.
* `IsSolutionOn.velocityFieldDeriv_eq`: on `H̄` the derivative of the velocity field of the solution
  is the derivative within `H̄` of the field of the law at the vorticity.

`APrioriHolder.lean` and `APriori.lean` use the Lipschitz bounds of the flow, and
`APrioriEstimate.lean` uses the bounds of the fields and of the supports in the a priori estimate
`exists_holderData_bound`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow Boussinesq.HalfPlane
open scoped Topology NNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ} {b Λ : ℝ} {K : ℝ≥0} {A : ℝ → ℝ}

/-- On the closed half-plane the derivative of the velocity field is the derivative within the
closed half-plane of the field of the law at the vorticity. -/
theorem velocityFieldDeriv_eq (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    (hb : 0 < b) (hI : Icc 0 b ⊆ I) {t : ℝ} (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    velocityFieldDeriv U sol t x = fderivWithin ℝ (U (fun y ↦ sol.vorticity y t)) H̄ x := by
  obtain ⟨R, hR, B, B₁, -, -, hω, -⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  exact fderiv_extendedField_of_nonneg le_rfl
    (by simpa using hω.contDiffOn_law hU hR.le (by norm_num) (by norm_num) ht) hx

section Flow

variable (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b)
  (hI : Icc 0 b ⊆ I) (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)

include hDu in
/-- The bound `A` of the gradient is nonnegative. -/
theorem nonneg_of_bound {t : ℝ} (ht : t ∈ Icc 0 b) : 0 ≤ A t :=
  (norm_nonneg _).trans (hDu t ht 0 (by simp))

include hb hDu hΛ in
/-- `Λ ≥ 0`. -/
theorem zero_le_Λ : 0 ≤ Λ :=
  (intervalIntegral.integral_nonneg hb.le fun _ ht ↦ nonneg_of_bound hDu ht).trans hΛ

include hU h hI hv in
/-- The flow of the velocity field keeps the closed half-plane. -/
theorem mapsTo_flowOn : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
    MapsTo (flowOn (velocityField U sol) 0 b s t) H̄ H̄ :=
  fun _ hs _ ht ↦ (h.bijOn_flowOn hU hI hv.isLipschitzFieldOn hs ht).mapsTo

include hb hA hDu hΛ in
/-- The integral of `A` over `[0, s] ⊆ [0, b]` is at most `Λ`. -/
theorem integral_le {s : ℝ} (hs : s ∈ Icc 0 b) : ∫ t in (0)..s, A t ≤ Λ := by
  refine le_trans ?_ hΛ
  have hint : IntervalIntegrable A volume 0 b :=
    (hA.mono (uIcc_of_le hb.le).subset).intervalIntegrable
  refine intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 ?_ hint
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact nonneg_of_bound hDu ⟨ht.1.le, ht.2⟩

include hU h hb hI hv hA hDu hΛ in
/-- **The first variation along a trajectory** is bounded by `exp Λ`. Proof: it solves a linear
equation whose coefficient is `Du` along the trajectory, and the trajectory stays in the closed
half-plane, where `‖Du‖ ≤ A`. -/
theorem norm_variation_le {s : ℝ} (hs : s ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b s 0 a‖ ≤ Real.exp Λ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  refine (hv.norm_variationOn_le_exp_integral (h.mapsTo_flowOn hU hI hv) hA
    (fun t ht ↦ nonneg_of_bound hDu ht) hDu hs h0 ha).trans
    (Real.exp_le_exp.mpr ?_)
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg hs.1 fun t ht ↦
    nonneg_of_bound hDu ⟨ht.1, ht.2.trans hs.2⟩)]
  exact integral_le hb hA hDu hΛ hs

include hU h hb hI hv hA hDu hΛ in
/-- **The inverse first variation** (from time `s` back to time `0`) is bounded by `exp Λ`. -/
theorem norm_inverseVariation_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 s x‖ ≤ Real.exp Λ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  refine (hv.norm_variationOn_le_exp_integral (h.mapsTo_flowOn hU hI hv) hA
    (fun t ht ↦ nonneg_of_bound hDu ht) hDu h0 hs hx).trans
    (Real.exp_le_exp.mpr ?_)
  rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg (intervalIntegral.integral_nonneg
    hs.1 fun t ht ↦ nonneg_of_bound hDu ⟨ht.1, ht.2.trans hs.2⟩)]
  exact integral_le hb hA hDu hΛ hs

include hU h hb hI hv hA hDu hΛ in
/-- **Trajectories are `exp Λ`-Lipschitz** in the label on the closed half-plane. This bound
uses only the integral of the velocity gradient. Proof: the mean value inequality on the closed
half-plane, which is convex, with the bound `exp Λ` of the first variation. -/
theorem norm_trajectory_sub_le {s : ℝ} (hs : s ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) :
    ‖trajectory U sol b s a - trajectory U sol b s a'‖ ≤ Real.exp Λ * ‖a - a'‖ :=
  PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun y ↦ trajectory U sol b s y)
    (f' := fun z ↦ variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b s 0 z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn hs ⟨le_rfl, hb.le⟩ z).hasFDerivWithinAt)
    (fun _ hz ↦ h.norm_variation_le hU hb hI hv hA hDu hΛ hs hz) ha' ha

include hU h hb hI hv hA hDu hΛ in
/-- **Labels are `exp Λ`-Lipschitz** on the closed half-plane. -/
theorem norm_label_sub_le {s : ℝ} (hs : s ∈ Icc 0 b) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖label U sol b x s - label U sol b x' s‖ ≤ Real.exp Λ * ‖x - x'‖ :=
  PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun y ↦ label U sol b y s)
    (f' := fun z ↦ variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 s z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn ⟨le_rfl, hb.le⟩ hs z).hasFDerivWithinAt)
    (fun _ hz ↦ h.norm_inverseVariation_le hU hb hI hv hA hDu hΛ hs hz) hx' hx

end Flow

section Data

variable {α R N : ℝ} (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
  (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)
  (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)

include hU h hb hI hv hd in
/-- **The temperature is bounded by its initial bound.** -/
theorem abs_temperature_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.temperature x s| ≤ N := by
  rw [h.temperature_eq_label hU hb hI hv hs hx]
  exact hd.abs_temperature_le _ (h.label_mem hU hI hv.isLipschitzFieldOn hb.le hs hx)

include hU h hb hI hv in
/-- The gradient of the temperature at time `s` is the initial gradient at the label composed
with the inverse first variation. -/
theorem fderiv_temperature_eq {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (fun y ↦ sol.temperature y s) x =
      (fderiv ℝ (fun y ↦ sol.temperature y 0) (label U sol b x s)).comp
        (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 s x) := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hlab := h.label_mem hU hI hL hb.le hs hx
  have hgrad := h.fderiv_temperature_trajectory_comp hU hb hI hv hlab hs
  rw [trajectory_label hL hb.le hs] at hgrad
  have hJW := hv.variationOn_flowOn_comp_variationOn h0 hs x
  rw [← hgrad, ContinuousLinearMap.comp_assoc]
  change _ = (fderiv ℝ (fun y ↦ sol.temperature y s) x).comp
    ((variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b s 0
      (flowOn (velocityField U sol) 0 b 0 s x)).comp
      (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 s x))
  rw [hJW, ContinuousLinearMap.comp_id]

include h hI hd in
/-- The gradient of the initial temperature is bounded by `N` on the closed half-plane. -/
theorem norm_fderiv_temperature_zero_le (hb : 0 ≤ b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun y ↦ sol.temperature y 0) x‖ ≤ N := by
  have hd0 : DifferentiableAt ℝ (fun y ↦ sol.temperature y 0) x :=
    (h.contDiff_temperature (hI ⟨le_rfl, hb⟩)).differentiable one_ne_zero x
  rw [← hd0.fderivWithin (uniqueDiffOn_closedUpper x hx)]
  exact hd.norm_fderivWithin_temperature_le _ hx

include hU h hb hI hv hA hDu hΛ hd in
/-- **The gradient of the temperature** is bounded by `N exp Λ`. Proof: it is the gradient of
the datum at the label composed with the inverse first variation, which is bounded by
`exp Λ`. -/
theorem norm_fderiv_temperature_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun y ↦ sol.temperature y s) x‖ ≤ N * Real.exp Λ := by
  have hlab := h.label_mem hU hI hv.isLipschitzFieldOn hb.le hs hx
  rw [h.fderiv_temperature_eq hU hb hI hv hs hx]
  have hθ₀ := h.norm_fderiv_temperature_zero_le hI hd hb.le hlab
  exact ((fderiv ℝ _ _).opNorm_comp_le _).trans (mul_le_mul hθ₀
    (h.norm_inverseVariation_le hU hb hI hv hA hDu hΛ hs hx) (norm_nonneg _)
    ((norm_nonneg _).trans hθ₀))

include hU hκ h hb hI hv hA hDu hΛ hd in
/-- **The vorticity** is bounded by `N + s Bκ₀ N exp Λ`. Proof: in Lagrangian form the vorticity
is the datum at the label plus the time integral of `κ ∂₀θ` along the trajectory, and the
integrand is at most `Bκ₀ N exp Λ`. -/
theorem abs_vorticity_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.vorticity x s| ≤ N + s * (Bκ 0 * (N * Real.exp Λ)) := by
  have hL := hv.isLipschitzFieldOn
  have hlab := h.label_mem hU hI hL hb.le hs hx
  rw [h.vorticity_eq_label hU hκ.contDiff_one.continuous hb hI hv hs hx]
  have hθ₀ := h.norm_fderiv_temperature_zero_le hI hd hb.le hlab
  have hint : ‖∫ r in (0)..s, κ (trajectory U sol b r (label U sol b x s)) *
      fderiv ℝ (fun y ↦ sol.temperature y 0) (label U sol b x s)
        (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 r
          (trajectory U sol b r (label U sol b x s)) (EuclideanSpace.single 0 1))‖ ≤
      Bκ 0 * (N * Real.exp Λ) * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    rw [uIoc_of_le hs.1] at hr
    have hr' : r ∈ Icc 0 b := ⟨hr.1.le, hr.2.trans hs.2⟩
    have hW := h.norm_inverseVariation_le hU hb hI hv hA hDu hΛ hr'
      (h.trajectory_mem hU hI hL hb.le hr' hlab)
    have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
    rw [norm_mul, Real.norm_eq_abs]
    refine mul_le_mul (hκ.abs_le _) ?_ (norm_nonneg _) (hκ.bound_nonneg 0)
    calc _ ≤ ‖fderiv ℝ (fun y ↦ sol.temperature y 0) (label U sol b x s)‖ *
          ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 r
            (trajectory U sol b r (label U sol b x s)) (EuclideanSpace.single 0 1)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * (Real.exp Λ * 1) := by
          refine mul_le_mul hθ₀ ?_ (norm_nonneg _) ((norm_nonneg _).trans hθ₀)
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          rw [he]
          exact mul_le_mul_of_nonneg_right hW zero_le_one
      _ = N * Real.exp Λ := by ring
  rw [sub_zero, abs_of_nonneg hs.1] at hint
  calc |sol.vorticity (label U sol b x s) 0 + _| ≤ |sol.vorticity (label U sol b x s) 0| +
        ‖∫ r in (0)..s, κ (trajectory U sol b r (label U sol b x s)) *
          fderiv ℝ (fun y ↦ sol.temperature y 0) (label U sol b x s)
            (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 r
              (trajectory U sol b r (label U sol b x s)) (EuclideanSpace.single 0 1))‖ :=
        abs_add_le _ _
    _ ≤ N + Bκ 0 * (N * Real.exp Λ) * s := add_le_add (hd.abs_vorticity_le _ hlab) hint
    _ = N + s * (Bκ 0 * (N * Real.exp Λ)) := by ring

include hU hκ h hb hI hv hd in
/-- **Supports.** At a point whose label lies outside the support disc of the data both fields
vanish. -/
theorem eq_zero_of_label {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R < ‖label U sol b x s‖) : sol.vorticity x s = 0 ∧ sol.temperature x s = 0 := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hlab := h.label_mem hU hI hL hb.le hs hx
  have hzero : fderiv ℝ (fun y ↦ sol.temperature y 0) (label U sol b x s) = 0 :=
    PDE.Analysis.fderiv_slice_eq_zero (f := sol.temperature)
      ((h.contDiff_temperature (hI h0)).differentiable one_ne_zero)
      (fun y hy hyR ↦ (hd.eq_zero y hy hyR).2) hlab hxR
  refine ⟨?_, ?_⟩
  · rw [h.vorticity_eq_label hU hκ.contDiff_one.continuous hb hI hv hs hx, hzero,
      (hd.eq_zero _ hlab hxR).1]
    simp
  · rw [h.temperature_eq_label hU hb hI hv hs hx]
    exact (hd.eq_zero _ hlab hxR).2

include hU hκ h hb hI hv hA hDu hΛ hd in
/-- **The velocity is bounded** on the closed half-plane at every time of `[0, b]` by
`C 0 0 (N + b Bκ₀ N exp Λ)`. -/
theorem norm_velocity_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖U (fun y ↦ sol.vorticity y s) x‖ ≤ C 0 0 * (N + b * (Bκ 0 * (N * Real.exp Λ))) := by
  obtain ⟨R', hR', hz⟩ := h.exists_vorticity_eq_zero (hI hs)
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hsB : N + s * (Bκ 0 * (N * Real.exp Λ)) ≤ N + b * (Bκ 0 * (N * Real.exp Λ)) := by
    have := mul_le_mul_of_nonneg_right hs.2
      (mul_nonneg (hκ.bound_nonneg 0) (mul_nonneg hN0 (Real.exp_pos Λ).le))
    linarith
  exact hU.norm_le hR'.le (h.contDiff_vorticity (hI hs)).continuous.continuousOn hz
    (fun y hy ↦ (h.abs_vorticity_le hU hκ hb hI hv hA hDu hΛ hd hs hy).trans hsB) x hx

include hU hκ h hb hI hv hA hDu hΛ hd in
/-- **Supports at later times.** With `V = C 0 0 (N + b Bκ₀ N exp Λ)`, both fields vanish on the
closed half-plane outside the disc of radius `R + V b` at every time of `[0, b]`. Proof: a
particle moves by at most `V s` in the time `s`, so the label of such a point lies outside the
support disc of the data, where `eq_zero_of_label` applies. -/
theorem eq_zero_of_norm {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R + C 0 0 * (N + b * (Bκ 0 * (N * Real.exp Λ))) * b < ‖x‖) :
    sol.vorticity x s = 0 ∧ sol.temperature x s = 0 := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set V := C 0 0 * (N + b * (Bκ 0 * (N * Real.exp Λ)))
  have hV : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityField U sol r y‖ ≤ V := fun r hr y hy ↦ by
    rw [velocityField_eq hy]
    exact h.norm_velocity_le hU hκ hb hI hv hA hDu hΛ hd hr hy
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 h0 0 (by simp))
  have hdisp := IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant
    (h.mapsTo_flowOn hU hI hv) hV h0 hs hx
  rw [zero_sub, abs_neg, abs_of_nonneg hs.1] at hdisp
  refine h.eq_zero_of_label hU hκ hb hI hv hd hs hx ?_
  have hsb : V * s ≤ V * b := mul_le_mul_of_nonneg_left hs.2 hV0
  have htri : ‖x‖ ≤ ‖label U sol b x s‖ + ‖flowOn (velocityField U sol) 0 b 0 s x - x‖ := by
    calc ‖x‖ = ‖label U sol b x s - (flowOn (velocityField U sol) 0 b 0 s x - x)‖ := by
          simp [label]
      _ ≤ _ := norm_sub_le _ _
  linarith

end Data

end IsSolutionOn

end HalfPlaneSystem
