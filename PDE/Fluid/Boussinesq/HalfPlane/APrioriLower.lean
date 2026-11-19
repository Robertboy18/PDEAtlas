/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Lagrangian
public import PDE.Fluid.Boussinesq.HalfPlane.Construction
public import PDE.Analysis.ODE.Flow.IntegralEstimates
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Lower-order a priori bounds of half-plane Boussinesq solutions

Let `sol` solve the system on `[0, b]` and let `A(t)` bound the gradient of the velocity on the
closed half-plane `H̄` at time `t`, with `∫₀ᵇ A ≤ Λ`. We bound the first variations of the flow
(`trajectory`, `label`), the temperature, its gradient, the vorticity, the velocity and the supports
in terms of the data at time `0` and `Λ` only. These are the lower-order bounds of the continuation
criterion: they do not involve the pointwise size of `A`, only its integral.

## Main results

* `IsSolutionOn.norm_variation_le`: the first variation along a trajectory is at most `exp Λ`.
* `IsSolutionOn.norm_trajectory_sub_le`: trajectories are `exp Λ`-Lipschitz in the label on `H̄`.
* `IsSolutionOn.abs_temperature_le`: `|θ| ≤ N`.
* `IsSolutionOn.norm_fderiv_temperature_le`: `‖∇θ‖ ≤ N exp Λ`.
* `IsSolutionOn.abs_vorticity_le`: `|ω(t)| ≤ N + t N exp Λ`.
* `IsSolutionOn.eq_zero_of_label`: the fields vanish at points whose label lies outside the
  support disc of the data.
* `IsSolutionOn.norm_velocity_le`: the velocity is at most
  `V = (N + b N exp Λ)(1 + 2 exp (2Λ) R²)` on the plane at every time of `[0, b]`.
* `IsSolutionOn.eq_zero_of_norm`: both fields vanish on `H̄` outside the disc of radius `R + V b`.

## How it works

The first variation solves the variational equation along the trajectory, so its norm is at most
`exp ∫₀ˢ A ≤ exp Λ` (`IsC1FieldOn.norm_variationOn_le_exp_integral`), and so is the norm of the
inverse variation. The mean value inequality on the convex closed half-plane turns these bounds into
the Lipschitz bounds of trajectories and labels. The Lagrangian form gives the values: the
temperature is the initial temperature at the label (`IsSolutionOn.temperature_eq_label`), its
gradient is `∇θ₀` at the label composed with the inverse variation (`fderiv_temperature_eq`), and
the vorticity is the initial vorticity at the label plus the time integral of `∇θ₀(W e₀)`
(`IsSolutionOn.vorticity_eq_label`). For the velocity we use `|u| ≤ B + π⁻¹ ∫ |ω|`
(`norm_halfPlaneVelocity_le_of_continuousOn`) with `B` the bound of the vorticity. The vorticity
vanishes outside the image under the flow of the support disc `|y| ≤ R` of the data, whose area is
at most `2 exp (2Λ) π R²` because `|det L| ≤ 2 ‖L‖²` (`exists_support_image`,
`abs_det_le_two_mul_sq`). Finally, both fields vanish at a point whose label lies outside that disc
(`eq_zero_of_label`), and a particle moves by at most `V s` in time `s`
(`IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant`), which gives the radius `R + V b`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow
open scoped Topology NNReal
open SobolevSpace

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- `|det L| ≤ 2 ‖L‖²` for a linear map of the plane. -/
theorem abs_det_le_two_mul_sq (L : ℝ^2 →L[ℝ] ℝ^2) : |L.det| ≤ 2 * ‖L‖ ^ 2 := by
  set B := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hdet : L.det = (LinearMap.toMatrix B B (L : ℝ^2 →ₗ[ℝ] ℝ^2)).det :=
    (LinearMap.det_toMatrix B _).symm
  have hentry (i j : Fin 2) : |LinearMap.toMatrix B B (L : ℝ^2 →ₗ[ℝ] ℝ^2) i j| ≤ ‖L‖ := by
    rw [LinearMap.toMatrix_apply]
    simp only [B, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    calc |(L (EuclideanSpace.single j 1)) i| ≤ ‖L (EuclideanSpace.single j 1)‖ := by
          rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
      _ ≤ ‖L‖ * ‖(EuclideanSpace.single j (1 : ℝ) : ℝ^2)‖ := L.le_opNorm _
      _ = ‖L‖ := by simp
  rw [hdet, Matrix.det_fin_two]
  have hL := norm_nonneg L
  calc |_ * _ - _ * _| ≤ |LinearMap.toMatrix B B (L : ℝ^2 →ₗ[ℝ] ℝ^2) 0 0| *
        |LinearMap.toMatrix B B (L : ℝ^2 →ₗ[ℝ] ℝ^2) 1 1| +
        |LinearMap.toMatrix B B (L : ℝ^2 →ₗ[ℝ] ℝ^2) 0 1| *
        |LinearMap.toMatrix B B (L : ℝ^2 →ₗ[ℝ] ℝ^2) 1 0| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ ‖L‖ * ‖L‖ + ‖L‖ * ‖L‖ :=
        add_le_add (mul_le_mul (hentry 0 0) (hentry 1 1) (abs_nonneg _) hL)
          (mul_le_mul (hentry 0 1) (hentry 1 0) (abs_nonneg _) hL)
    _ = 2 * ‖L‖ ^ 2 := by ring

/-- The integral over the open half-plane of a function continuous on the closed half-plane,
vanishing there outside a disc and outside a measurable set `S` of finite measure, and bounded by
`N`, is at most `N` times the measure of `S`. -/
theorem setIntegral_upper_le_of_subset {g : ℝ^2 → ℝ} {N R₀ : ℝ} {S : Set (ℝ^2)}
    (hg : ContinuousOn g H̄) (hR₀ : ∀ y : ℝ^2, 0 ≤ y 1 → R₀ < ‖y‖ → g y = 0)
    (hS : MeasurableSet S) (hSf : volume S ≠ ⊤) (hN : ∀ y, 0 ≤ y 1 → g y ≤ N)
    (hg0 : ∀ y, 0 ≤ g y) (hgS : ∀ y, 0 ≤ y 1 → y ∉ S → g y = 0) :
    ∫ y in HalfSpace.upper 2, g y ≤ N * volume.real S := by
  have hN0 : 0 ≤ N := (hg0 0).trans (hN 0 (by simp))
  have hle : ∀ y ∈ HalfSpace.upper 2, g y ≤ S.indicator (fun _ ↦ N) y := by
    intro y hy
    by_cases hyS : y ∈ S
    · rw [indicator_of_mem hyS]; exact hN y (le_of_lt hy)
    · rw [indicator_of_notMem hyS, hgS y (le_of_lt hy) hyS]
  have hind : Integrable (S.indicator fun _ ↦ N) :=
    (integrableOn_const (C := N) hSf).integrable_indicator hS
  calc ∫ y in HalfSpace.upper 2, g y
      ≤ ∫ y in HalfSpace.upper 2, S.indicator (fun _ ↦ N) y :=
        setIntegral_mono_on (integrableOn_upper_of_continuousOn hg hR₀) hind.integrableOn
          (HalfSpace.measurableSet_upper (n := 2)) hle
    _ ≤ ∫ y, S.indicator (fun _ ↦ N) y :=
        setIntegral_le_integral hind (Eventually.of_forall fun y ↦ by
          by_cases hy : y ∈ S <;> simp [hy, hN0])
    _ = N * volume.real S := by
        rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]

namespace IsSolutionOn

variable {sol : VorticityStreamFields} {I : Set ℝ} {b Λ : ℝ} {K : ℝ≥0} {A : ℝ → ℝ}

/-- On the closed half-plane the derivative of the velocity field is the derivative within the
closed half-plane of the half-plane velocity of the vorticity. -/
theorem velocityFieldDeriv_eq (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    {t : ℝ} (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    velocityFieldDeriv sol t x =
      fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x := by
  obtain ⟨R, B, B₁, -, -, hω, -⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  exact fderiv_extendedVelocity_of_nonneg le_rfl
    (hω.contDiffOn_halfPlaneVelocity_one (by norm_num) ht) hx

/-- The derivative of a slice at a point of the closed half-plane is its derivative within the
closed half-plane. -/
theorem fderiv_eq_fderivWithin {f : ℝ^2 → ℝ} (hf : Differentiable ℝ f) {x : ℝ^2}
    (hx : 0 ≤ x 1) : fderiv ℝ f x = fderivWithin ℝ f H̄ x :=
  ((hf x).fderivWithin (uniqueDiffOn_closedUpper x hx)).symm

section Flow

variable (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)

omit h hb hI hv hA hΛ in
include hDu in
/-- The bound `A` of the gradient is nonnegative. -/
theorem nonneg_of_bound {t : ℝ} (ht : t ∈ Icc 0 b) : 0 ≤ A t :=
  (norm_nonneg _).trans (hDu t ht 0 (by simp))

omit hb hA hΛ hDu in
include h hI hv in
/-- The flow of the velocity field keeps the closed half-plane. -/
theorem mapsTo_flowOn : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
    MapsTo (flowOn (velocityField sol) 0 b s t) H̄ H̄ :=
  fun _ hs _ ht ↦ (h.bijOn_flowOn hI hv.isLipschitzFieldOn hs ht).mapsTo

omit h hI hv in
include hb hA hDu hΛ in
/-- The integral of `A` over `[0, s] ⊆ [0, b]` is at most `Λ`. -/
theorem integral_le {s : ℝ} (hs : s ∈ Icc 0 b) : ∫ t in (0)..s, A t ≤ Λ := by
  refine le_trans ?_ hΛ
  have hint : IntervalIntegrable A volume 0 b :=
    (hA.mono (uIcc_of_le hb.le).subset).intervalIntegrable
  refine intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 ?_ hint
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact nonneg_of_bound hDu ⟨ht.1.le, ht.2⟩

include h hb hI hv hA hDu hΛ in
/-- **The first variation along a trajectory** is bounded by `exp Λ`. -/
theorem norm_variation_le {s : ℝ} (hs : s ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    ‖variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s 0 a‖ ≤ Real.exp Λ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  refine (hv.norm_variationOn_le_exp_integral (h.mapsTo_flowOn hI hv) hA
    (fun t ht ↦ nonneg_of_bound hDu ht) hDu hs h0 ha).trans
    (Real.exp_le_exp.mpr ?_)
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg hs.1 fun t ht ↦
    nonneg_of_bound hDu ⟨ht.1, ht.2.trans hs.2⟩)]
  exact integral_le hb hA hDu hΛ hs

include h hb hI hv hA hDu hΛ in
/-- **The inverse first variation** (from time `s` back to time `0`) is bounded by `exp Λ`. -/
theorem norm_inverseVariation_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 s x‖ ≤ Real.exp Λ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  refine (hv.norm_variationOn_le_exp_integral (h.mapsTo_flowOn hI hv) hA
    (fun t ht ↦ nonneg_of_bound hDu ht) hDu h0 hs hx).trans
    (Real.exp_le_exp.mpr ?_)
  rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg (intervalIntegral.integral_nonneg
    hs.1 fun t ht ↦ nonneg_of_bound hDu ⟨ht.1, ht.2.trans hs.2⟩)]
  exact integral_le hb hA hDu hΛ hs

include h hb hI hv hA hDu hΛ in
/-- **Trajectories are `exp Λ`-Lipschitz** in the label on the closed half-plane. -/
theorem norm_trajectory_sub_le {s : ℝ} (hs : s ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) :
    ‖trajectory sol b s a - trajectory sol b s a'‖ ≤ Real.exp Λ * ‖a - a'‖ :=
  PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun y ↦ trajectory sol b s y)
    (f' := fun z ↦ variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s 0 z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn hs ⟨le_rfl, hb.le⟩ z).hasFDerivWithinAt)
    (fun _ hz ↦ h.norm_variation_le hb hI hv hA hDu hΛ hs hz) ha' ha

include h hb hI hv hA hDu hΛ in
/-- **Labels are `exp Λ`-Lipschitz** on the closed half-plane. -/
theorem norm_label_sub_le {s : ℝ} (hs : s ∈ Icc 0 b) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖label sol b x s - label sol b x' s‖ ≤ Real.exp Λ * ‖x - x'‖ :=
  PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun y ↦ label sol b y s)
    (f' := fun z ↦ variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 s z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn ⟨le_rfl, hb.le⟩ hs z).hasFDerivWithinAt)
    (fun _ hz ↦ h.norm_inverseVariation_le hb hI hv hA hDu hΛ hs hz) hx' hx

end Flow

section Data

variable {α R N : ℝ}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)
  (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)

omit hA hDu hΛ in
include h hI hv hd in
/-- **The temperature is bounded by its initial bound.** -/
theorem abs_temperature_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.temperature x s| ≤ N := by
  rw [h.temperature_eq_label hI hv hs hx]
  exact hd.abs_temperature_le _ (h.label_mem hI hv.isLipschitzFieldOn hs hx)

omit hA hDu hΛ in
include h hb hI hv in
/-- The gradient of the temperature at time `s` is the initial gradient at the label composed
with the inverse first variation. -/
theorem fderiv_temperature_eq {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (fun y ↦ sol.temperature y s) x =
      (fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)).comp
        (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 s x) := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hlab := h.label_mem hI hL hs hx
  have hgrad := h.fderiv_temperature_trajectory_comp hb hI hv hlab hs
  rw [trajectory_label hL hs] at hgrad
  have hJW := hv.variationOn_flowOn_comp_variationOn h0 hs x
  rw [← hgrad, ContinuousLinearMap.comp_assoc]
  change _ = (fderiv ℝ (fun y ↦ sol.temperature y s) x).comp
    ((variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s 0
      (flowOn (velocityField sol) 0 b 0 s x)).comp
      (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 s x))
  rw [hJW, ContinuousLinearMap.comp_id]

include h hb hI hv hA hDu hΛ hd in
/-- **The gradient of the temperature** is bounded by `N exp Λ`. -/
theorem norm_fderiv_temperature_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun y ↦ sol.temperature y s) x‖ ≤ N * Real.exp Λ := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hlab := h.label_mem hI hL hs hx
  rw [h.fderiv_temperature_eq hb hI hv hs hx]
  have hθ₀ : ‖fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)‖ ≤ N := by
    rw [fderiv_eq_fderivWithin ((h.contDiff_temperature (hI h0)).differentiable one_ne_zero)
      hlab]
    exact hd.norm_fderivWithin_temperature_le _ hlab
  exact ((fderiv ℝ _ _).opNorm_comp_le _).trans (mul_le_mul hθ₀
    (h.norm_inverseVariation_le hb hI hv hA hDu hΛ hs hx) (norm_nonneg _)
    ((norm_nonneg _).trans hθ₀))

include h hb hI hv hA hDu hΛ hd in
/-- **The vorticity** is bounded by `N + s N exp Λ`. -/
theorem abs_vorticity_le {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.vorticity x s| ≤ N + s * (N * Real.exp Λ) := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hlab := h.label_mem hI hL hs hx
  rw [h.vorticity_eq_label hb hI hv hs hx]
  have hθ₀ : ‖fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)‖ ≤ N := by
    rw [fderiv_eq_fderivWithin ((h.contDiff_temperature (hI h0)).differentiable one_ne_zero)
      hlab]
    exact hd.norm_fderivWithin_temperature_le _ hlab
  have hint : ‖∫ r in (0)..s, fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)
      (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 r
        (trajectory sol b r (label sol b x s)) (EuclideanSpace.single 0 1))‖ ≤
      (N * Real.exp Λ) * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    rw [uIoc_of_le hs.1] at hr
    have hr' : r ∈ Icc 0 b := ⟨hr.1.le, hr.2.trans hs.2⟩
    have hW := h.norm_inverseVariation_le hb hI hv hA hDu hΛ hr'
      (h.trajectory_mem hI hL hr' hlab)
    calc _ ≤ ‖fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)‖ *
          ‖variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 r
            (trajectory sol b r (label sol b x s)) (EuclideanSpace.single 0 1)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * (Real.exp Λ * 1) := by
          refine mul_le_mul hθ₀ ?_ (norm_nonneg _) ((norm_nonneg _).trans hθ₀)
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
          rw [he]
          exact mul_le_mul_of_nonneg_right hW zero_le_one
      _ = N * Real.exp Λ := by ring
  rw [sub_zero, abs_of_nonneg hs.1] at hint
  calc |sol.vorticity (label sol b x s) 0 + _| ≤ |sol.vorticity (label sol b x s) 0| +
        ‖∫ r in (0)..s, fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s)
          (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 r
            (trajectory sol b r (label sol b x s)) (EuclideanSpace.single 0 1))‖ :=
        abs_add_le _ _
    _ ≤ N + N * Real.exp Λ * s := add_le_add (hd.abs_vorticity_le _ hlab) hint
    _ = N + s * (N * Real.exp Λ) := by ring

omit hA hDu hΛ in
include h hb hI hv hd in
/-- **Supports.** At a point whose label lies outside the support disc of the data both fields
vanish. -/
theorem eq_zero_of_label {s : ℝ} (hs : s ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R < ‖label sol b x s‖) : sol.vorticity x s = 0 ∧ sol.temperature x s = 0 := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hlab := h.label_mem hI hL hs hx
  have hzero : fderiv ℝ (fun y ↦ sol.temperature y 0) (label sol b x s) = 0 :=
    PDE.Analysis.fderiv_slice_eq_zero (f := sol.temperature)
      ((h.contDiff_temperature (hI h0)).differentiable one_ne_zero)
      (fun y hy hyR ↦ (hd.eq_zero y hy hyR).2) hlab hxR
  refine ⟨?_, ?_⟩
  · rw [h.vorticity_eq_label hb hI hv hs hx, hzero, (hd.eq_zero _ hlab hxR).1]
    simp
  · rw [h.temperature_eq_label hI hv hs hx]
    exact (hd.eq_zero _ hlab hxR).2

include h hb hI hv hA hDu hΛ hd in
/-- **The image of the support disc.** Every point of the closed half-plane where the vorticity
does not vanish at time `s` lies in the image under the flow of the support disc of the data, and
that image has measure at most `2 exp (2Λ) π R²`. -/
theorem exists_support_image {s : ℝ} (hs : s ∈ Icc 0 b) (hR0 : 0 ≤ R) :
    ∃ S : Set (ℝ^2), MeasurableSet S ∧ volume S ≠ ⊤ ∧
      volume.real S ≤ 2 * Real.exp Λ ^ 2 * (Real.pi * R ^ 2) ∧
      ∀ y : ℝ^2, 0 ≤ y 1 → y ∉ S → sol.vorticity y s = 0 ∧ sol.temperature y s = 0 := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set K : Set (ℝ^2) := closedBall (0 : ℝ^2) R ∩ H̄
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hXc : Continuous (trajectory sol b s) := continuous_iff_continuousAt.mpr fun a ↦
    (hv.hasFDerivAt_flowOn hs h0 a).continuousAt
  set S := trajectory sol b s '' K
  have hSc : IsCompact S := hKc.image hXc
  have hSm : MeasurableSet S := hSc.measurableSet
  have hJ : ∀ a ∈ K, HasFDerivWithinAt (trajectory sol b s)
      (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s 0 a) K a :=
    fun a _ ↦ (hv.hasFDerivAt_flowOn hs h0 a).hasFDerivWithinAt
  set c : ℝ := 2 * Real.exp Λ ^ 2
  have hdet : ∀ a ∈ K, ENNReal.ofReal
      |(variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s 0 a).det| ≤
        ENNReal.ofReal c := fun a ha ↦ by
    refine ENNReal.ofReal_le_ofReal ((abs_det_le_two_mul_sq _).trans ?_)
    have hJa := h.norm_variation_le hb hI hv hA hDu hΛ hs ha.2
    have := pow_le_pow_left₀ (norm_nonneg _) hJa 2
    linarith
  have hmeas : volume S ≤ ENNReal.ofReal c * (ENNReal.ofReal R ^ 2 * ENNReal.ofReal Real.pi) := by
    calc volume S ≤ ∫⁻ a in K, ENNReal.ofReal
          |(variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b s 0 a).det| :=
          addHaar_image_le_lintegral_abs_det_fderiv volume hKc.measurableSet hJ
      _ ≤ ∫⁻ _ in K, ENNReal.ofReal c := setLIntegral_mono measurable_const hdet
      _ = ENNReal.ofReal c * volume K := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal c * volume (closedBall (0 : ℝ^2) R) := by
          gcongr
          exact inter_subset_left
      _ = _ := by rw [EuclideanSpace.volume_closedBall_fin_two]
  have hfin : ENNReal.ofReal c * (ENNReal.ofReal R ^ 2 * ENNReal.ofReal Real.pi) ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  refine ⟨S, hSm, ne_top_of_le_ne_top hfin hmeas, ?_, fun y hy hyS ↦ ?_⟩
  · have h1 := ENNReal.toReal_mono hfin hmeas
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR0,
      ENNReal.toReal_ofReal Real.pi_pos.le, ENNReal.toReal_ofReal (by positivity)] at h1
    calc volume.real S = (volume S).toReal := rfl
      _ ≤ c * (R ^ 2 * Real.pi) := h1
      _ = 2 * Real.exp Λ ^ 2 * (Real.pi * R ^ 2) := by ring
  · have hlab := h.label_mem hI hL hs hy
    refine h.eq_zero_of_label hb hI hv hd hs hy (lt_of_not_ge fun hle ↦ hyS ?_)
    exact ⟨label sol b y s, ⟨mem_closedBall_zero_iff.mpr hle, hlab⟩,
      trajectory_label hL hs y⟩

include h hb hI hv hA hDu hΛ hd in
/-- **The mass of the vorticity** on the open half-plane at time `s` is at most
`(N + s N exp Λ) · 2 exp (2Λ) π R²`. -/
theorem setIntegral_abs_vorticity_le {s : ℝ} (hs : s ∈ Icc 0 b) (hR0 : 0 ≤ R) :
    ∫ y in HalfSpace.upper 2, |sol.vorticity y s| ≤
      (N + s * (N * Real.exp Λ)) * (2 * Real.exp Λ ^ 2 * (Real.pi * R ^ 2)) := by
  obtain ⟨S, hSm, hSf, hSv, hS⟩ := h.exists_support_image hb hI hv hA hDu hΛ hd hs hR0
  obtain ⟨R₀, hR₀⟩ := h.exists_vorticity_eq_zero (hI hs)
  have hB := fun y hy ↦ h.abs_vorticity_le hb hI hv hA hDu hΛ hd hs (x := y) hy
  have hB0 : 0 ≤ N + s * (N * Real.exp Λ) := (abs_nonneg _).trans (hB 0 (by simp))
  refine (setIntegral_upper_le_of_subset (g := fun y ↦ |sol.vorticity y s|) (R₀ := R₀)
    (h.contDiff_vorticity (hI hs)).continuous.abs.continuousOn
    (fun y hy hyR ↦ by simp [hR₀ y hy hyR]) hSm hSf hB (fun _ ↦ abs_nonneg _)
    (fun y hy hyS ↦ by simp [(hS y hy hyS).1])).trans ?_
  exact mul_le_mul_of_nonneg_left hSv hB0

include h hb hI hv hA hDu hΛ hd in
/-- **The velocity is bounded** on the plane at every time of `[0, b]` by
`V = (N + b N exp Λ)(1 + 2 exp (2Λ) R²)`. -/
theorem norm_velocity_le {s : ℝ} (hs : s ∈ Icc 0 b) (hR0 : 0 ≤ R) (x : ℝ^2) :
    ‖halfPlaneVelocity (fun y ↦ sol.vorticity y s) x‖ ≤
      (N + b * (N * Real.exp Λ)) * (1 + 2 * Real.exp Λ ^ 2 * R ^ 2) := by
  obtain ⟨R₀, hR₀⟩ := h.exists_vorticity_eq_zero (hI hs)
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  set B := N + b * (N * Real.exp Λ)
  have hsB : N + s * (N * Real.exp Λ) ≤ B := by
    have := mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hN0 (Real.exp_pos Λ).le)
    linarith
  have hB : ∀ y ∈ HalfSpace.upper 2, |sol.vorticity y s| ≤ B := fun y hy ↦
    (h.abs_vorticity_le hb hI hv hA hDu hΛ hd hs (le_of_lt hy)).trans hsB
  have hm := h.setIntegral_abs_vorticity_le hb hI hv hA hDu hΛ hd hs hR0
  have hv' := norm_halfPlaneVelocity_le_of_continuousOn
    (h.contDiff_vorticity (hI hs)).continuous.continuousOn hR₀ hB x
  have hc : 0 ≤ 2 * Real.exp Λ ^ 2 * (Real.pi * R ^ 2) := by positivity
  calc _ ≤ B + (∫ y in HalfSpace.upper 2, |sol.vorticity y s|) / Real.pi := hv'
    _ ≤ B + (B * (2 * Real.exp Λ ^ 2 * (Real.pi * R ^ 2))) / Real.pi := by
        gcongr
        exact hm.trans (mul_le_mul_of_nonneg_right hsB hc)
    _ = B * (1 + 2 * Real.exp Λ ^ 2 * R ^ 2) := by
        field_simp

include h hb hI hv hA hDu hΛ hd in
/-- **Supports at later times.** With `V = (N + b N exp Λ)(1 + 2 exp (2Λ) R²)`, both fields
vanish on the closed half-plane outside the disc of radius `R + V b` at every time of `[0, b]`. -/
theorem eq_zero_of_norm {s : ℝ} (hs : s ∈ Icc 0 b) (hR0 : 0 ≤ R) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R + (N + b * (N * Real.exp Λ)) * (1 + 2 * Real.exp Λ ^ 2 * R ^ 2) * b < ‖x‖) :
    sol.vorticity x s = 0 ∧ sol.temperature x s = 0 := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set V := (N + b * (N * Real.exp Λ)) * (1 + 2 * Real.exp Λ ^ 2 * R ^ 2)
  have hV : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityField sol r y‖ ≤ V := fun r hr y hy ↦ by
    rw [velocityField, extendedVelocity_of_nonneg 1 _ hy]
    exact h.norm_velocity_le hb hI hv hA hDu hΛ hd hr hR0 y
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 h0 0 (by simp))
  have hdisp := IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant (h.mapsTo_flowOn hI hv) hV
    h0 hs hx
  rw [zero_sub, abs_neg, abs_of_nonneg hs.1] at hdisp
  refine h.eq_zero_of_label hb hI hv hd hs hx ?_
  have hsb : V * s ≤ V * b := mul_le_mul_of_nonneg_left hs.2 hV0
  have htri : ‖x‖ ≤ ‖label sol b x s‖ + ‖flowOn (velocityField sol) 0 b 0 s x - x‖ := by
    calc ‖x‖ = ‖label sol b x s - (flowOn (velocityField sol) 0 b 0 s x - x)‖ := by
          simp [label]
      _ ≤ _ := norm_sub_le _ _
  linarith

end Data

end IsSolutionOn

end Boussinesq.HalfPlane
