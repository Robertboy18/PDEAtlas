/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.CarriedBounds

/-!
# Bounds of the carried vorticity and temperature

The vorticity carried by the flow of the velocity field of a history is the amplitude `Ω (Y, t)` at
the label `Y = flowOn v a b 0 t x` of the particle at `x` at time `t`, and the carried temperature
is `θ̃₀(Y)`. All bounds hold on the closed half-plane, under the flow bounds `IsBoundedFlowOn`.

## Main results

* `abs_carriedVorticity_le`: `|ω(x, t)| ≤ N + |t| N L`.
* `norm_fderiv_carriedVorticity_le`: the spatial derivative of the carried vorticity is at most
  `(N + |t| c₀) L`.
* `norm_fderiv_carriedVorticity_sub_le`: that derivative is `α`-Hölder with constant
  `(N + |t| c_α) L ^ α L + (N + |t| c₀) max σ (2 δ)`.
* `carried_eq_zero`: the supports grow by at most `V` times the elapsed time.
* `exists_abs_carriedVorticity_sub_le`: the carried vorticity is continuous in time uniformly on
  the closed half-plane.
* `exists_norm_fderiv_carriedVorticity_sub_le`: so is its spatial derivative.
* `carriedTemperature_bounds`: the carried temperature is at most `N`, its derivative at most
  `N L`, its second derivative `Dθ̃₀(Y) D²Y + D²θ̃₀(Y)[DY, DY]` at most `N σ + N L²`.
* `norm_fderiv_fderiv_carriedTemperature_sub_le`: that second derivative is `α`-Hölder.

## How it works

With `J = D_x Y`, the chain rule gives `Dω(x) = DΩ(Y) ∘ J` (`hasFDerivAt_carriedVorticity`). For two
points `x` and `x'` we split `DΩ(Y) ∘ J - DΩ(Y') ∘ J'` as
`(DΩ(Y) - DΩ(Y')) ∘ J + DΩ(Y') ∘ (J - J')`. The first term is controlled by the Hölder bound of the
amplitude (`IsBoundedFlowOn.norm_fderiv_amplitude_sub_le`) and `‖Y - Y'‖ ≤ L ‖x - x'‖`, the second
by `‖J - J'‖ ≤ max σ (2 δ) ‖x - x'‖ ^ α` (`IsBoundedFlowOn.norm_variationOn_sub_le_rpow`). The
difference of the second derivatives of the carried temperature is a Hölder term plus a Lipschitz
term (`norm_fderiv_fderiv_carriedTemperature_sub_le_add`), and the size bound `N σ + N L²` turns the
Lipschitz term into a Hölder one (`le_add_max_mul_rpow`). For the supports, a label moves by at most
`V |t|` (`IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant`) and the data vanish outside the
disc of radius `R`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The carried vorticity -/

namespace IsBoundedFlowOn

variable {ω : ℝ → ℝ^2 → ℝ} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0} {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ}

/-- The carried vorticity is the amplitude at the label. -/
theorem carriedVorticity_eq (x : ℝ^2) (t : ℝ) :
    carriedVorticity ω₀ θ₀ ω a b x t = forcedAmplitude (dataVorticity ω₀)
      (labelForcing (historyField ω) (historyFieldDeriv ω) a b (dataTemperature θ₀)
        (EuclideanSpace.single 0 1)) (flowOn (historyField ω) a b 0 t x) t :=
  rfl

/-- The label `flowOn v a b 0 t x` moves at most `L V |s - t|` between the times `s` and `t`. -/
theorem norm_label_sub_le {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
    {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2}
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (hv : IsC1FieldOn v Dv a b K)
    (h0 : (0 : ℝ) ∈ Icc a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    ‖flowOn v a b 0 s x - flowOn v a b 0 t x‖ ≤ L * (V * |s - t|) := by
  have hL := hv.isLipschitzFieldOn
  rw [← hL.flowOn_flowOn h0 ht hs x]
  refine (hb.norm_flowOn_sub_le hv h0 ht (hb.flowOn_mem ht hs hx) hx).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (hb.zero_le_L h0)
  rw [abs_sub_comm]
  exact IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hb.mapsTo hb.norm_le ht hs hx

/-- The first variation of the label map moves by at most
`σ V |s - t| L + L (exp (K₁ |s - t|) - 1)` between the times `s` and `t`. -/
theorem norm_labelVariation_sub_le {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
    {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2}
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    ‖variationOn v Dv a b 0 s x - variationOn v Dv a b 0 t x‖ ≤
      σ * (V * |s - t|) * L + L * (Real.exp (K₁ * |s - t|) - 1) := by
  have hv1 := hv.toIsC1FieldOn
  have hL := hv1.isLipschitzFieldOn
  set z := flowOn v a b t s x
  have hz : 0 ≤ z 1 := hb.flowOn_mem ht hs hx
  rw [hv1.variationOn_eq_comp h0 ht hs x]
  have hsplit : (variationOn v Dv a b 0 t z).comp (variationOn v Dv a b t s x) -
      variationOn v Dv a b 0 t x =
      (variationOn v Dv a b 0 t z - variationOn v Dv a b 0 t x).comp
          (variationOn v Dv a b t s x) +
        (variationOn v Dv a b 0 t x).comp
          (variationOn v Dv a b t s x - ContinuousLinearMap.id ℝ (ℝ^2)) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    abel
  rw [hsplit]
  have hzx : ‖z - x‖ ≤ V * |s - t| := by
    rw [abs_sub_comm]
    exact IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hb.mapsTo hb.norm_le ht hs hx
  have h₁ : ‖variationOn v Dv a b 0 t z - variationOn v Dv a b 0 t x‖ ≤ σ * (V * |s - t|) :=
    (hb.norm_variationOn_sub_le hv h0 ht hz hx).trans
      (mul_le_mul_of_nonneg_left hzx (hb.zero_le_σ h0))
  have h₂ : ‖variationOn v Dv a b t s x - ContinuousLinearMap.id ℝ (ℝ^2)‖ ≤
      Real.exp (K₁ * |s - t|) - 1 := by
    rw [abs_sub_comm]
    exact hv1.norm_variationOn_sub_id_le_of_invariant hb.mapsTo hb.norm_deriv_le ht hs hx
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul h₁
      (hb.norm_variationOn_le t ht s hs x hx) (norm_nonneg _)
      (mul_nonneg (hb.zero_le_σ h0) (by positivity [hb.zero_le_V h0])))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
      (hb.norm_variationOn_le 0 h0 t ht x hx) h₂ (norm_nonneg _) (hb.zero_le_L h0))

/-- **The carried vorticity is bounded** by `N + |t| N L` on the closed half-plane. -/
theorem abs_carriedVorticity_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η) (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ}
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity ω₀ θ₀ ω a b x t| ≤ N + |t| * (N * L) :=
  hb.abs_amplitude_le h0 hd ht (hb.flowOn_mem h0 ht hx)

/-- The spatial derivative of the carried vorticity: the derivative of the amplitude at the
label composed with the first variation of the label map. -/
theorem hasFDerivAt_carriedVorticity (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω)
      (historyFieldDeriv₂ ω) a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ^2) :
    HasFDerivAt (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t)
      ((fderiv ℝ (dataVorticity ω₀) (flowOn (historyField ω) a b 0 t x) + ∫ r in (0)..t,
        labelForcingDeriv (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b
          (dataTemperature θ₀) (EuclideanSpace.single 0 1) (flowOn (historyField ω) a b 0 t x)
          r).comp (variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x)) x :=
  (hasFDerivAt_amplitude hv h0 hd ht _).comp x (hv.toIsC1FieldOn.hasFDerivAt_flowOn h0 ht x)

/-- The carried vorticity is `C¹` in space at every time of `[a, b]`. -/
theorem contDiff_carriedVorticity (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω)
      (historyFieldDeriv₂ ω) a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 1 (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) :=
  (contDiff_amplitude hv h0 hd ht).comp ((hv.contDiff_flowOn h0 ht).of_le (by norm_num))

/-- On the closed half-plane the derivative within the closed half-plane of the carried
vorticity is its derivative. -/
theorem fderivWithin_carriedVorticity (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω)
      (historyFieldDeriv₂ ω) a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) H̄ x =
      fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) x :=
  ((hasFDerivAt_carriedVorticity hv h0 hd ht x).differentiableAt).fderivWithin
    (uniqueDiffOn_closedUpper x hx)

/-- **The spatial derivative of the carried vorticity is bounded** by `(N + |t| c₀) L` on the
closed half-plane. -/
theorem norm_fderiv_carriedVorticity_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) x‖ ≤
      (N + |t| * forcingDerivBound N L σ) * L := by
  rw [(hasFDerivAt_carriedVorticity hv h0 hd ht x).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
    (hb.norm_fderiv_amplitude_le h0 hd ht (hb.flowOn_mem h0 ht hx))
    (hb.norm_variationOn_le 0 h0 t ht x hx) (norm_nonneg _)
    ((norm_nonneg _).trans (hb.norm_fderiv_amplitude_le h0 hd ht (hb.flowOn_mem h0 ht hx))))

/-- **The spatial derivative of the carried vorticity is `α`-Hölder** on the closed half-plane,
with constant `(N + |t| c_α) L ^ α L + (N + |t| c₀) max σ (2 δ)`. -/
theorem norm_fderiv_carriedVorticity_sub_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {t : ℝ} (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) x -
        fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) x'‖ ≤
      ((N + |t| * forcingDerivHolderConst N L σ η) * L ^ α * L +
        (N + |t| * forcingDerivBound N L σ) * max σ (2 * δ)) * ‖x - x'‖ ^ α := by
  set v := historyField ω
  set Dv := historyFieldDeriv ω
  set D2v := historyFieldDeriv₂ ω
  set A := fun y ↦ fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
    labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r
  set Y := flowOn v a b 0 t x
  set Y' := flowOn v a b 0 t x'
  set J := variationOn v Dv a b 0 t x
  set J' := variationOn v Dv a b 0 t x'
  have hY : 0 ≤ Y 1 := hb.flowOn_mem h0 ht hx
  have hY' : 0 ≤ Y' 1 := hb.flowOn_mem h0 ht hx'
  have hL0 := hb.zero_le_L h0
  have hd0 : 0 ≤ ‖x - x'‖ := norm_nonneg _
  rw [(hasFDerivAt_carriedVorticity hv h0 hd ht x).fderiv,
    (hasFDerivAt_carriedVorticity hv h0 hd ht x').fderiv]
  change ‖(A Y).comp J - (A Y').comp J'‖ ≤ _
  have hsplit : (A Y).comp J - (A Y').comp J' = (A Y - A Y').comp J + (A Y').comp (J - J') := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  have hAA : ‖A Y - A Y'‖ ≤ (N + |t| * forcingDerivHolderConst N L σ η) * ‖Y - Y'‖ ^ α :=
    hb.norm_fderiv_amplitude_sub_le hv h0 hd hα0 hα1 ht hY hY'
  have hYY : ‖Y - Y'‖ ^ α ≤ L ^ α * ‖x - x'‖ ^ α := by
    rw [← Real.mul_rpow hL0 hd0]
    exact Real.rpow_le_rpow (norm_nonneg _)
      (hb.norm_flowOn_sub_le hv.toIsC1FieldOn h0 ht hx hx') hα0
  have hA' : ‖A Y'‖ ≤ N + |t| * forcingDerivBound N L σ := hb.norm_fderiv_amplitude_le h0 hd ht hY'
  have hJJ : ‖J - J'‖ ≤ max σ (2 * δ) * ‖x - x'‖ ^ α :=
    hb.norm_variationOn_sub_le_rpow hv hα0 hα1 h0 ht hx hx'
  have hJ : ‖J‖ ≤ L := hb.norm_variationOn_le 0 h0 t ht x hx
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hd.norm_fderiv_dataVorticity_le hx)
  have hcα : 0 ≤ N + |t| * forcingDerivHolderConst N L σ η :=
    add_nonneg hN0 (mul_nonneg (abs_nonneg t) (forcingDerivHolderConst_nonneg hN0 hL0
      (hb.zero_le_σ h0) (hb.zero_le_η h0)))
  calc ‖(A Y - A Y').comp J + (A Y').comp (J - J')‖
      ≤ ‖A Y - A Y'‖ * ‖J‖ + ‖A Y'‖ * ‖J - J'‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _))
    _ ≤ ((N + |t| * forcingDerivHolderConst N L σ η) * (L ^ α * ‖x - x'‖ ^ α)) * L +
        (N + |t| * forcingDerivBound N L σ) * (max σ (2 * δ) * ‖x - x'‖ ^ α) := by
        refine add_le_add (mul_le_mul (hAA.trans (mul_le_mul_of_nonneg_left hYY hcα)) hJ
          (norm_nonneg _) (mul_nonneg hcα (mul_nonneg (Real.rpow_nonneg hL0 α)
            (Real.rpow_nonneg hd0 α)))) (mul_le_mul hA' hJJ (norm_nonneg _)
          ((norm_nonneg _).trans hA'))
    _ = _ := by ring

/-- **Support of the carried fields.** At a time `t` with `|t| ≤ τ` the carried vorticity and
the carried temperature vanish on the closed half-plane outside the disc of radius `R + V τ`. -/
theorem carried_eq_zero
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {τ t : ℝ} (ht : t ∈ Icc a b) (htτ : |t| ≤ τ) {x : ℝ^2}
    (hx : 0 ≤ x 1) (hxR : R + V * τ < ‖x‖) :
    carriedVorticity ω₀ θ₀ ω a b x t = 0 ∧ carriedTemperature θ₀ ω a b x t = 0 := by
  set Y := flowOn (historyField ω) a b 0 t x
  have hY : 0 ≤ Y 1 := hb.flowOn_mem h0 ht hx
  have hYx : ‖Y - x‖ ≤ V * |0 - t| :=
    IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hb.mapsTo hb.norm_le h0 ht hx
  rw [zero_sub, abs_neg] at hYx
  have hV0 := hb.zero_le_V h0
  have hYR : R < ‖Y‖ := by
    have h1 : ‖x‖ ≤ ‖Y‖ + ‖Y - x‖ := by
      have := norm_sub_le Y (Y - x)
      rwa [sub_sub_cancel] at this
    have h2 : V * |t| ≤ V * τ := mul_le_mul_of_nonneg_left htτ hV0
    linarith
  obtain ⟨hω, hθ⟩ := hd.data_eq_zero hY hYR
  refine ⟨?_, hθ⟩
  rw [carriedVorticity_eq, forcedAmplitude, hω, zero_add]
  have hG : ∀ r, labelForcing (historyField ω) (historyFieldDeriv ω) a b (dataTemperature θ₀)
      (EuclideanSpace.single 0 1) Y r = 0 := fun r ↦ by
    rw [labelForcing, hd.fderiv_dataTemperature_eq_zero hY hYR, zero_apply]
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r _ ↦ hG r,
    intervalIntegral.integral_zero]

/-- A point of `[a, b]` has absolute value at most `|a| + |b|`. -/
theorem abs_le_add_abs_of_mem_Icc {a b r : ℝ} (hr : r ∈ Icc a b) : |r| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le a, hr.1, abs_nonneg b]
  · linarith [le_abs_self b, hr.2, abs_nonneg a]

/-- A modulus continuous at zero and vanishing there is small near zero. -/
theorem exists_forall_le_of_continuousAt {m : ℝ → ℝ} (hm : ContinuousAt m 0) (hm0 : m 0 = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ h, |h| < δ → m h ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hm ε hε
  refine ⟨δ, hδ, fun h' hh' ↦ ?_⟩
  have := h (by rwa [Real.dist_eq, sub_zero])
  rw [Real.dist_eq, hm0, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- The carried vorticity is Lipschitz in time on the closed half-plane. -/
theorem abs_carriedVorticity_time_sub_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity ω₀ θ₀ ω a b x s - carriedVorticity ω₀ θ₀ ω a b x t| ≤
      (N + |s| * forcingDerivBound N L σ) * (L * (V * |s - t|)) + N * L * |s - t| := by
  set Ys := flowOn (historyField ω) a b 0 s x
  set Yt := flowOn (historyField ω) a b 0 t x
  have hYs : 0 ≤ Ys 1 := hb.flowOn_mem h0 hs hx
  have hYt : 0 ≤ Yt 1 := hb.flowOn_mem h0 ht hx
  rw [carriedVorticity_eq, carriedVorticity_eq]
  set Ω := forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω)
    (historyFieldDeriv ω) a b (dataTemperature θ₀) (EuclideanSpace.single 0 1))
  have h₁ : |Ω Ys s - Ω Yt s| ≤ (N + |s| * forcingDerivBound N L σ) * (L * (V * |s - t|)) := by
    refine (hb.abs_amplitude_sub_le hv h0 hd hs hYs hYt).trans (mul_le_mul_of_nonneg_left
      (hb.norm_label_sub_le hv.toIsC1FieldOn h0 hs ht hx) ?_)
    exact add_nonneg ((abs_nonneg _).trans (hd.abs_dataVorticity_le hx)) (mul_nonneg
      (abs_nonneg s) (forcingDerivBound_nonneg ((abs_nonneg _).trans (hd.abs_dataVorticity_le hx))
        (hb.zero_le_L h0) (hb.zero_le_σ h0)))
  have h₂ : |Ω Yt s - Ω Yt t| ≤ N * L * |s - t| := hb.abs_amplitude_time_sub_le hv h0 hd hs ht hYt
  calc |Ω Ys s - Ω Yt t| = |(Ω Ys s - Ω Yt s) + (Ω Yt s - Ω Yt t)| := by ring_nf
    _ ≤ |Ω Ys s - Ω Yt s| + |Ω Yt s - Ω Yt t| := abs_add_le _ _
    _ ≤ _ := add_le_add h₁ h₂

/-- **Continuity in time of the carried vorticity**, uniformly on the closed half-plane. -/
theorem exists_abs_carriedVorticity_sub_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ' > 0, ∀ s ∈ Icc a b, |s - t| < δ' → ∀ x : ℝ^2, 0 ≤ x 1 →
      |carriedVorticity ω₀ θ₀ ω a b x s - carriedVorticity ω₀ θ₀ ω a b x t| ≤ ε := by
  set τ := |a| + |b|
  set c := (N + τ * forcingDerivBound N L σ) * (L * V) + N * L
  have hm : ContinuousAt (fun h : ℝ ↦ c * |h|) 0 := by fun_prop
  obtain ⟨δ', hδ', hδ'ε⟩ := exists_forall_le_of_continuousAt hm (by simp) hε
  refine ⟨δ', hδ', fun s hs hst x hx ↦ ?_⟩
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have hL0 := hb.zero_le_L h0
  have hc₀ := forcingDerivBound_nonneg hN0 hL0 (hb.zero_le_σ h0)
  have hsτ : |s| ≤ τ := abs_le_add_abs_of_mem_Icc hs
  refine (hb.abs_carriedVorticity_time_sub_le hv h0 hd hs ht hx).trans
    (le_trans ?_ (hδ'ε (s - t) hst))
  have hV0 := hb.zero_le_V h0
  have h1 : (N + |s| * forcingDerivBound N L σ) ≤ N + τ * forcingDerivBound N L σ := by
    gcongr
  calc (N + |s| * forcingDerivBound N L σ) * (L * (V * |s - t|)) + N * L * |s - t|
      ≤ (N + τ * forcingDerivBound N L σ) * (L * (V * |s - t|)) + N * L * |s - t| := by
        gcongr
    _ = c * |s - t| := by ring

/-- The spatial derivative of the carried vorticity moves continuously in time, with an explicit
modulus, on the closed half-plane. -/
theorem norm_fderiv_carriedVorticity_time_sub_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z s) x -
        fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) x‖ ≤
      (N + |s| * forcingDerivHolderConst N L σ η) * (L * (V * |s - t|)) ^ α * L +
        forcingDerivBound N L σ * |s - t| * L +
        (N + |t| * forcingDerivBound N L σ) *
          (σ * (V * |s - t|) * L + L * (Real.exp (K₁ * |s - t|) - 1)) := by
  set v := historyField ω
  set Dv := historyFieldDeriv ω
  set D2v := historyFieldDeriv₂ ω
  set A := fun (r : ℝ) (y : ℝ^2) ↦ fderiv ℝ (dataVorticity ω₀) y + ∫ q in (0)..r,
    labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y q
  set Ys := flowOn v a b 0 s x
  set Yt := flowOn v a b 0 t x
  set Js := variationOn v Dv a b 0 s x
  set Jt := variationOn v Dv a b 0 t x
  have hYs : 0 ≤ Ys 1 := hb.flowOn_mem h0 hs hx
  have hYt : 0 ≤ Yt 1 := hb.flowOn_mem h0 ht hx
  have hL0 := hb.zero_le_L h0
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have hσ0 := hb.zero_le_σ h0
  have hc₀ := forcingDerivBound_nonneg hN0 hL0 hσ0
  have hcα := forcingDerivHolderConst_nonneg hN0 hL0 hσ0 (hb.zero_le_η h0)
  rw [(hasFDerivAt_carriedVorticity hv h0 hd hs x).fderiv,
    (hasFDerivAt_carriedVorticity hv h0 hd ht x).fderiv]
  change ‖(A s Ys).comp Js - (A t Yt).comp Jt‖ ≤ _
  have hsplit : (A s Ys).comp Js - (A t Yt).comp Jt =
      (A s Ys - A s Yt).comp Js + (A s Yt - A t Yt).comp Js + (A t Yt).comp (Js - Jt) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  have hJs : ‖Js‖ ≤ L := hb.norm_variationOn_le 0 h0 s hs x hx
  have h₁ : ‖A s Ys - A s Yt‖ ≤
      (N + |s| * forcingDerivHolderConst N L σ η) * (L * (V * |s - t|)) ^ α :=
    (hb.norm_fderiv_amplitude_sub_le hv h0 hd hα0 hα1 hs hYs hYt).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
        (hb.norm_label_sub_le hv.toIsC1FieldOn h0 hs ht hx) hα0)
        (add_nonneg hN0 (mul_nonneg (abs_nonneg s) hcα)))
  have h₂ : ‖A s Yt - A t Yt‖ ≤ forcingDerivBound N L σ * |s - t| :=
    hb.norm_fderiv_amplitude_time_sub_le hv h0 hd hs ht hYt
  have h₃ : ‖A t Yt‖ ≤ N + |t| * forcingDerivBound N L σ :=
    hb.norm_fderiv_amplitude_le h0 hd ht hYt
  have h₄ : ‖Js - Jt‖ ≤ σ * (V * |s - t|) * L + L * (Real.exp (K₁ * |s - t|) - 1) :=
    hb.norm_labelVariation_sub_le hv h0 hs ht hx
  calc _ ≤ ‖(A s Ys - A s Yt).comp Js‖ + ‖(A s Yt - A t Yt).comp Js‖ +
        ‖(A t Yt).comp (Js - Jt)‖ := norm_add₃_le
    _ ≤ ‖A s Ys - A s Yt‖ * ‖Js‖ + ‖A s Yt - A t Yt‖ * ‖Js‖ + ‖A t Yt‖ * ‖Js - Jt‖ :=
        add_le_add (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ _ := add_le_add (add_le_add
        (mul_le_mul h₁ hJs (norm_nonneg _) ((norm_nonneg _).trans h₁))
        (mul_le_mul h₂ hJs (norm_nonneg _) (mul_nonneg hc₀ (abs_nonneg _))))
        (mul_le_mul h₃ h₄ (norm_nonneg _) ((norm_nonneg _).trans h₃))

/-- **Continuity in time of the spatial derivative of the carried vorticity**, uniformly on the
closed half-plane, for `0 < α ≤ 1`. -/
theorem exists_norm_fderiv_carriedVorticity_sub_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 < α) (hα1 : α ≤ 1)
    {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ' > 0, ∀ s ∈ Icc a b, |s - t| < δ' → ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z s) x -
        fderiv ℝ (fun z ↦ carriedVorticity ω₀ θ₀ ω a b z t) x‖ ≤ ε := by
  set τ := |a| + |b|
  set cα := N + τ * forcingDerivHolderConst N L σ η
  set c₀ := N + τ * forcingDerivBound N L σ
  set m : ℝ → ℝ := fun h ↦ cα * (L * (V * |h|)) ^ α * L + forcingDerivBound N L σ * |h| * L +
    c₀ * (σ * (V * |h|) * L + L * (Real.exp (K₁ * |h|) - 1))
  have hm : ContinuousAt m 0 := by
    have hr : Continuous fun h : ℝ ↦ (L * (V * |h|)) ^ α :=
      (Real.continuous_rpow_const hα0.le).comp (by fun_prop)
    exact (((continuous_const.mul hr).mul continuous_const).add (by fun_prop)).add
      (by fun_prop) |>.continuousAt
  have hm0 : m 0 = 0 := by simp [m, Real.zero_rpow hα0.ne']
  obtain ⟨δ', hδ', hδ'ε⟩ := exists_forall_le_of_continuousAt hm hm0 hε
  refine ⟨δ', hδ', fun s hs hst x hx ↦ ?_⟩
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hc₀ := forcingDerivBound_nonneg hN0 hL0 hσ0
  have hcα := forcingDerivHolderConst_nonneg hN0 hL0 hσ0 (hb.zero_le_η h0)
  have hτ (r : ℝ) (hr : r ∈ Icc a b) : |r| ≤ τ := abs_le_add_abs_of_mem_Icc hr
  refine (hb.norm_fderiv_carriedVorticity_time_sub_le hv h0 hd hα0.le hα1 hs ht hx).trans
    (le_trans ?_ (hδ'ε (s - t) hst))
  have hK₁ := hb.zero_le_K₁ h0
  have hV0 := hb.zero_le_V h0
  have hexp : 0 ≤ Real.exp (K₁ * |s - t|) - 1 := by
    have := Real.add_one_le_exp (K₁ * |s - t|)
    nlinarith [mul_nonneg hK₁ (abs_nonneg (s - t))]
  have hp : 0 ≤ (L * (V * |s - t|)) ^ α := Real.rpow_nonneg (by positivity) α
  have h1 : N + |s| * forcingDerivHolderConst N L σ η ≤ cα :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (hτ s hs) hcα)
  have h2 : N + |t| * forcingDerivBound N L σ ≤ c₀ :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (hτ t ht) hc₀)
  simp only [m]
  gcongr

end IsBoundedFlowOn

/-! ### The carried temperature -/

/-- On the closed half-plane the derivative within the closed half-plane of a `C¹` function is
its derivative. -/
theorem fderivWithin_closedUpper_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ^2 → F} (hf : Differentiable ℝ f) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ f H̄ x = fderiv ℝ f x :=
  (hf x).fderivWithin (uniqueDiffOn_closedUpper x hx)

/-- On the closed half-plane the second derivative within the closed half-plane of a `C²`
function is its second derivative. -/
theorem fderivWithin_fderivWithin_closedUpper_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ^2 → F} (hf : ContDiff ℝ 2 f) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (fderivWithin ℝ f H̄) H̄ x = fderiv ℝ (fderiv ℝ f) x := by
  have hd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h := fderivWithin_congr (𝕜 := ℝ) (f₁ := fderivWithin ℝ f H̄) (f := fderiv ℝ f)
    (s := H̄) (x := x) (fun y hy ↦ fderivWithin_closedUpper_eq hd hy)
    (fderivWithin_closedUpper_eq hd hx)
  rw [h]
  exact fderivWithin_closedUpper_eq hD hx

namespace IsBoundedFlowOn

variable {ω : ℝ → ℝ^2 → ℝ} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0} {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ}

/-- The carried temperature is `C²` in space at every time of `[a, b]`. -/
theorem contDiff_carriedTemperature (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω)
      (historyFieldDeriv₂ ω) a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 2 (fun z ↦ carriedTemperature θ₀ ω a b z t) :=
  contDiff_comp_flowOn hv h0 hd.contDiff_dataTemperature ht

/-- The spatial derivative of the carried temperature. -/
theorem hasFDerivAt_carriedTemperature (hv : IsC1FieldOn (historyField ω) (historyFieldDeriv ω)
      a b K) (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ}
    (ht : t ∈ Icc a b) (x : ℝ^2) :
    HasFDerivAt (fun z ↦ carriedTemperature θ₀ ω a b z t)
      ((fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t x)).comp
        (variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x)) x :=
  hasFDerivAt_comp_flowOn hv h0 (hd.contDiff_dataTemperature.differentiable two_ne_zero) ht x

/-- The second spatial derivative of the carried temperature applied to `h` and `k`:
`Dθ₀(Y) (D²Y h k) + D²θ₀(Y) (DY h) (DY k)` at the label `Y`. -/
theorem fderiv_fderiv_carriedTemperature_apply (hv : IsC2FieldOn (historyField ω)
      (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b) (x h k : ℝ^2) :
    fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x h k =
      fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t x)
          (secondVariationOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b 0
            t x h k) +
        fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn (historyField ω) a b 0 t x)
          (variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x h)
          (variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x k) := by
  have hv1 := hv.toIsC1FieldOn
  have hθ := hd.contDiff_dataTemperature
  have hD : Differentiable ℝ (fderiv ℝ (dataTemperature θ₀)) :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hfun : fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t) = fun z ↦
      (fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t z)).comp
        (variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t z) :=
    funext fun z ↦ (hasFDerivAt_carriedTemperature hv1 h0 hd ht z).fderiv
  have hc : HasFDerivAt (fun z ↦ fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t z))
      ((fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn (historyField ω) a b 0 t x)).comp
        (variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x)) x :=
    (hD _).hasFDerivAt.comp x (hv1.hasFDerivAt_flowOn h0 ht x)
  have hJ := hv.hasFDerivAt_variationOn h0 ht x
  rw [hfun, (hc.clm_comp hJ).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

/-- **Bounds of the carried temperature** on the closed half-plane: the value is at most `N`, the
derivative at most `N L` and the second derivative at most `N σ + N L ^ 2`. -/
theorem carriedTemperature_bounds
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedTemperature θ₀ ω a b x t| ≤ N ∧
      ‖fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t) x‖ ≤ N * L ∧
      ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x‖ ≤
        N * σ + N * L ^ 2 := by
  have hY := hb.flowOn_mem h0 ht hx
  have hL0 := hb.zero_le_L h0
  have hB := hd.norm_fderiv_dataTemperature_le hY
  have hA := hd.norm_fderiv_fderiv_dataTemperature_le hY
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hB
  have hJ := hb.norm_variationOn_le 0 h0 t ht x hx
  have hS := hb.norm_secondVariationOn_le 0 h0 t ht x hx
  refine ⟨hd.abs_dataTemperature_le hY, ?_, ?_⟩
  · rw [(hasFDerivAt_carriedTemperature hv.toIsC1FieldOn h0 hd ht x).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hB hJ (norm_nonneg _) hN0)
  · have hσ0 := hb.zero_le_σ h0
    have hM0 : 0 ≤ N * σ + N * L ^ 2 := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun h ↦ ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM0 (norm_nonneg h)) fun k ↦ ?_
    rw [fderiv_fderiv_carriedTemperature_apply hv h0 hd ht]
    set J := variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x
    set S := secondVariationOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b
      0 t x
    set B := fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t x)
    set A := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn (historyField ω) a b 0 t x)
    have h₁ : ‖B (S h k)‖ ≤ N * σ * ‖h‖ * ‖k‖ := by
      refine (B.le_opNorm _).trans ?_
      have : ‖S h k‖ ≤ σ * ‖h‖ * ‖k‖ :=
        ((S h).le_opNorm k).trans (mul_le_mul_of_nonneg_right ((S.le_opNorm h).trans
          (mul_le_mul_of_nonneg_right hS (norm_nonneg _))) (norm_nonneg _))
      calc ‖B‖ * ‖S h k‖ ≤ N * (σ * ‖h‖ * ‖k‖) :=
            mul_le_mul hB this (norm_nonneg _) hN0
        _ = N * σ * ‖h‖ * ‖k‖ := by ring
    have h₂ : ‖A (J h) (J k)‖ ≤ N * L ^ 2 * ‖h‖ * ‖k‖ := by
      have hJh : ‖J h‖ ≤ L * ‖h‖ := (J.le_opNorm h).trans
        (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
      have hJk : ‖J k‖ ≤ L * ‖k‖ := (J.le_opNorm k).trans
        (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
      calc ‖A (J h) (J k)‖ ≤ ‖A‖ * ‖J h‖ * ‖J k‖ := A.le_opNorm₂ _ _
        _ ≤ N * (L * ‖h‖) * (L * ‖k‖) := by gcongr
        _ = N * L ^ 2 * ‖h‖ * ‖k‖ := by ring
    calc ‖B (S h k) + A (J h) (J k)‖ ≤ ‖B (S h k)‖ + ‖A (J h) (J k)‖ := norm_add_le _ _
      _ ≤ N * σ * ‖h‖ * ‖k‖ + N * L ^ 2 * ‖h‖ * ‖k‖ := add_le_add h₁ h₂
      _ = (N * σ + N * L ^ 2) * ‖h‖ * ‖k‖ := by ring

/-- The second spatial derivative of the carried temperature: a Hölder term plus a Lipschitz
term on the closed half-plane. -/
theorem norm_fderiv_fderiv_carriedTemperature_sub_le_add
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) {t : ℝ}
    (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x -
        fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x'‖ ≤
      (N * η + N * L ^ α * L ^ 2) * ‖x - x'‖ ^ α + 3 * N * L * σ * ‖x - x'‖ := by
  have hY := hb.flowOn_mem h0 ht hx
  have hY' := hb.flowOn_mem h0 ht hx'
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hη0 := hb.zero_le_η h0
  set J := variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x
  set J' := variationOn (historyField ω) (historyFieldDeriv ω) a b 0 t x'
  set S := secondVariationOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b
    0 t x
  set S' := secondVariationOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b
    0 t x'
  set B := fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t x)
  set B' := fderiv ℝ (dataTemperature θ₀) (flowOn (historyField ω) a b 0 t x')
  set A := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn (historyField ω) a b 0 t x)
  set A' := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn (historyField ω) a b 0 t x')
  set d := ‖x - x'‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hp0 : 0 ≤ d ^ α := Real.rpow_nonneg hd0 α
  have hYY : ‖flowOn (historyField ω) a b 0 t x - flowOn (historyField ω) a b 0 t x'‖ ≤ L * d :=
    hb.norm_flowOn_sub_le hv.toIsC1FieldOn h0 ht hx hx'
  have hB' : ‖B'‖ ≤ N := hd.norm_fderiv_dataTemperature_le hY'
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hB'
  have hBB : ‖B - B'‖ ≤ N * (L * d) :=
    (hd.norm_fderiv_dataTemperature_sub_le hY hY').trans (mul_le_mul_of_nonneg_left hYY hN0)
  have hA' : ‖A'‖ ≤ N := hd.norm_fderiv_fderiv_dataTemperature_le hY'
  have hAA : ‖A - A'‖ ≤ N * (L ^ α * d ^ α) := by
    refine (hd.norm_fderiv_fderiv_dataTemperature_sub_le hY hY').trans
      (mul_le_mul_of_nonneg_left ?_ hN0)
    rw [← Real.mul_rpow hL0 hd0]
    exact Real.rpow_le_rpow (norm_nonneg _) hYY hα0
  have hS : ‖S‖ ≤ σ := hb.norm_secondVariationOn_le 0 h0 t ht x hx
  have hSS : ‖S - S'‖ ≤ η * d ^ α := hb.holder_secondVariationOn 0 h0 t ht x x' hx hx'
  have hJ : ‖J‖ ≤ L := hb.norm_variationOn_le 0 h0 t ht x hx
  have hJ' : ‖J'‖ ≤ L := hb.norm_variationOn_le 0 h0 t ht x' hx'
  have hJJ : ‖J - J'‖ ≤ σ * d := hb.norm_variationOn_sub_le hv h0 ht hx hx'
  have hM0 : 0 ≤ (N * η + N * L ^ α * L ^ 2) * d ^ α + 3 * N * L * σ * d := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun h ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM0 (norm_nonneg h)) fun k ↦ ?_
  rw [sub_apply, sub_apply, fderiv_fderiv_carriedTemperature_apply hv h0 hd ht,
    fderiv_fderiv_carriedTemperature_apply hv h0 hd ht]
  change ‖(B (S h k) + A (J h) (J k)) - (B' (S' h k) + A' (J' h) (J' k))‖ ≤ _
  have hsplit : (B (S h k) + A (J h) (J k)) - (B' (S' h k) + A' (J' h) (J' k)) =
      (B - B') (S h k) + B' ((S - S') h k) + (A - A') (J h) (J k) +
        A' ((J - J') h) (J k) + A' (J' h) ((J - J') k) := by
    simp only [sub_apply, map_sub]
    abel
  rw [hsplit]
  have hnh := norm_nonneg h
  have hnk := norm_nonneg k
  have hJh : ‖J h‖ ≤ L * ‖h‖ := (J.le_opNorm h).trans (mul_le_mul_of_nonneg_right hJ hnh)
  have hJk : ‖J k‖ ≤ L * ‖k‖ := (J.le_opNorm k).trans (mul_le_mul_of_nonneg_right hJ hnk)
  have hJ'h : ‖J' h‖ ≤ L * ‖h‖ := (J'.le_opNorm h).trans (mul_le_mul_of_nonneg_right hJ' hnh)
  have hJJh : ‖(J - J') h‖ ≤ σ * d * ‖h‖ :=
    ((J - J').le_opNorm h).trans (mul_le_mul_of_nonneg_right hJJ hnh)
  have hJJk : ‖(J - J') k‖ ≤ σ * d * ‖k‖ :=
    ((J - J').le_opNorm k).trans (mul_le_mul_of_nonneg_right hJJ hnk)
  have hShk : ‖S h k‖ ≤ σ * ‖h‖ * ‖k‖ := (S.le_opNorm₂ h k).trans (by gcongr)
  have hSShk : ‖(S - S') h k‖ ≤ η * d ^ α * ‖h‖ * ‖k‖ :=
    ((S - S').le_opNorm₂ h k).trans (by gcongr)
  have e₁ : ‖(B - B') (S h k)‖ ≤ N * (L * d) * (σ * ‖h‖ * ‖k‖) :=
    ((B - B').le_opNorm _).trans (mul_le_mul hBB hShk (norm_nonneg _) (by positivity))
  have e₂ : ‖B' ((S - S') h k)‖ ≤ N * (η * d ^ α * ‖h‖ * ‖k‖) :=
    (B'.le_opNorm _).trans (mul_le_mul hB' hSShk (norm_nonneg _) hN0)
  have e₃ : ‖(A - A') (J h) (J k)‖ ≤ N * (L ^ α * d ^ α) * (L * ‖h‖) * (L * ‖k‖) :=
    ((A - A').le_opNorm₂ _ _).trans (by gcongr)
  have e₄ : ‖A' ((J - J') h) (J k)‖ ≤ N * (σ * d * ‖h‖) * (L * ‖k‖) :=
    (A'.le_opNorm₂ _ _).trans (by gcongr)
  have e₅ : ‖A' (J' h) ((J - J') k)‖ ≤ N * (L * ‖h‖) * (σ * d * ‖k‖) :=
    (A'.le_opNorm₂ _ _).trans (by gcongr)
  calc _ ≤ ‖(B - B') (S h k)‖ + ‖B' ((S - S') h k)‖ + ‖(A - A') (J h) (J k)‖ +
        ‖A' ((J - J') h) (J k)‖ + ‖A' (J' h) ((J - J') k)‖ :=
        (norm_add_le _ _).trans (add_le_add_left norm_add₄_le _)
    _ ≤ N * (L * d) * (σ * ‖h‖ * ‖k‖) + N * (η * d ^ α * ‖h‖ * ‖k‖) +
        N * (L ^ α * d ^ α) * (L * ‖h‖) * (L * ‖k‖) + N * (σ * d * ‖h‖) * (L * ‖k‖) +
        N * (L * ‖h‖) * (σ * d * ‖k‖) := by gcongr
    _ = ((N * η + N * L ^ α * L ^ 2) * d ^ α + 3 * N * L * σ * d) * ‖h‖ * ‖k‖ := by ring

/-- **The second derivative of the carried temperature is `α`-Hölder** on the closed half-plane,
with constant `N η + N L ^ α L ^ 2 + max (3 N L σ) (2 (N σ + N L ^ 2))`. -/
theorem norm_fderiv_fderiv_carriedTemperature_sub_le
    (hb : IsBoundedFlowOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b α V
      K₁ L δ σ η)
    (hv : IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {t : ℝ} (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x -
        fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x'‖ ≤
      (N * η + N * L ^ α * L ^ 2 + max (3 * N * L * σ) (2 * (N * σ + N * L ^ 2))) *
        ‖x - x'‖ ^ α := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans
    (hd.norm_fderiv_dataTemperature_le (hb.flowOn_mem h0 ht hx))
  have hL0 := hb.zero_le_L h0
  have hη0 := hb.zero_le_η h0
  have hσ0 := hb.zero_le_σ h0
  have hb₁ := (hb.carriedTemperature_bounds hv h0 hd ht hx).2.2
  have hb₂ := (hb.carriedTemperature_bounds hv h0 hd ht hx').2.2
  refine le_add_max_mul_rpow (by positivity) hα0 hα1 (norm_nonneg _)
    (hb.norm_fderiv_fderiv_carriedTemperature_sub_le_add hv h0 hd hα0 ht hx hx') ?_
    (by positivity)
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x‖ +
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x'‖ :=
        norm_sub_le (fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x)
          (fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ ω a b z t)) x')
    _ ≤ 2 * (N * σ + N * L ^ 2) := by linarith

end IsBoundedFlowOn

end Boussinesq.HalfPlane
