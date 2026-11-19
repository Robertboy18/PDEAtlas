/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.LevelK
public import PDE.Fluid.Incompressible.HalfPlane.FlowHigher
import PDE.Fluid.Boussinesq.HalfPlane.CarriedBounds

/-!
# The carried temperature and the forcing at level `k`

Let `(ω₀, θ₀)` be data of order `k ≥ 2` with bound `N` (`IsHolderDataOf k`) and `ω` a `C^{k,α}`
history on `[-T, T]` with lower-order bound `Nlow` and top-order majorant `P`
(`IsTopBoundedHistory`). With `v r = extendedVelocity (k + 1) (ω r)`, `Y_t = flowOn v 0 t` the
label map at time `t` and `X_r = flowOn v r 0` the position map at time `r`, and
`Ψ(t) = |∫ₜ⁰ P(|r|) dr| = ∫₀^{|t|} P`, the carried temperature and the forcing in label form
have Hölder bounds on the closed half-plane `H̄` whose top-order constants are affine in `Ψ`.

## Main definitions

* `temperatureBound`: the bound of the derivatives of orders `1 ≤ j ≤ k` of the carried
  temperature, depending only on `k, α, R₁, N, Nlow, T`.
* `temperatureHolder`: their Hölder constant.
* `temperatureTopConst`: the constant term of the bound of the derivative of order `k + 1`.
* `temperatureTopSlope`: the coefficient of `Ψ(t)` in that bound.
* `forcingBound`: the bound of the derivatives of orders `1 ≤ j < k` of the forcing.
* `forcingHolder`: their Hölder constant.

## Main results

* `hasHolderBounds_comp_flowOn`: the temperature `θ₀ ∘ Y_t` has `C^{k+1,α}` bounds on `H̄` with
  constants `temperatureBound`, `temperatureHolder` below the top order and top-order constants
  `temperatureTopConst + temperatureTopSlope Ψ(t)` and
  `temperatureTopHolderConst + temperatureTopHolderSlope Ψ(t)`.
* `hasHolderBounds_carriedTemperature`: the carried temperature, which agrees with `θ₀ ∘ Y_t` on
  `H̄`, has the same bounds.
* `hasHolderBounds_forcing`: the forcing in label form `G(·, r) = ∂₀(θ₀ ∘ Y_r) ∘ X_r` has
  `C^{k,α}` bounds with constants `forcingBound`, `forcingHolder` below the top order and top-order
  constants affine in `Ψ(r)`.
* `labelForcing_historyField_eq`: the label forcing of the iteration agrees with
  `∂₀(θ₀ ∘ Y_r) ∘ X_r` on `H̄`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open IncompressibleFlow PDE.Analysis PDE.Analysis.ODE PDE.Hyperbolic.Transport

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The data -/

namespace IsHolderDataOf

variable {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {α R N : ℝ}

/-- The temperature datum of order `k` has `C^{k+1,α}` bounds `N, 2N, N, N`. -/
theorem hasHolderBounds_temperature (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : HasHolderBounds (k + 1) θ₀ α N (2 * N) N N where
  contDiffOn := hd.temperature_contDiffOn
  norm_le _ _ hj z hz := hd.norm_temperature_le _ hj.le z hz
  holder _ _ hj _ _ hz hz' := hd.norm_iteratedFDerivWithin_temperature_sub_le hα0 hα1 hj.le hz hz'
  norm_top_le z hz := hd.norm_temperature_le (k + 1) le_rfl z hz
  holder_top := hd.holder_temperature

/-- The vorticity datum of order `k` has `C^{k,α}` bounds `N, 2N, N, N`. -/
theorem hasHolderBounds_vorticity (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : HasHolderBounds k ω₀ α N (2 * N) N N where
  contDiffOn := hd.vorticity_contDiffOn
  norm_le _ _ hj z hz := hd.norm_vorticity_le _ hj.le z hz
  holder _ _ hj _ _ hz hz' := hd.norm_iteratedFDerivWithin_vorticity_sub_le hα0 hα1 hj.le hz hz'
  norm_top_le z hz := hd.norm_vorticity_le k le_rfl z hz
  holder_top := hd.holder_vorticity

end IsHolderDataOf

/-! ### The constants -/

section Constants

variable (k : ℕ) (α R₁ N Nlow T : ℝ)

/-- The bound of the derivatives of orders `1 ≤ j ≤ k` of the carried temperature. -/
def temperatureBound : ℝ :=
  compBound (k + 1) N (flowBound k α R₁ Nlow T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j ≤ k` of the carried temperature. -/
def temperatureHolder : ℝ :=
  compHolder (k + 1) α N (2 * N) (flowBound k α R₁ Nlow T) (flowHolder k α R₁ Nlow T)
    (flowBound k α R₁ Nlow T)

/-- The constant term of the bound of the derivative of order `k + 1` of the carried
temperature. -/
def temperatureTopConst : ℝ :=
  compTopBound (k + 1) N N (flowBound k α R₁ Nlow T) (flowTopConst k α R₁ Nlow T)

/-- The coefficient of `Ψ(t)` in the bound of the derivative of order `k + 1` of the carried
temperature. -/
def temperatureTopSlope : ℝ :=
  N * flowTopSlope k α R₁ Nlow T

/-- The constant term of the Hölder constant of the derivative of order `k + 1` of the carried
temperature. -/
def temperatureTopHolderConst : ℝ :=
  compTopHolder (k + 1) α N (2 * N) N N (flowBound k α R₁ Nlow T) (flowHolder k α R₁ Nlow T)
    (flowTopConst k α R₁ Nlow T) (flowTopHolderConst k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The coefficient of `Ψ(t)` in the Hölder constant of the derivative of order `k + 1` of the
carried temperature. -/
def temperatureTopHolderSlope : ℝ :=
  N * flowTopHolderSlope k α R₁ Nlow T +
    2 * N * flowBound k α R₁ Nlow T ^ α * flowTopSlope k α R₁ Nlow T

/-- The bound of the derivatives of orders `1 ≤ j < k` of the forcing. -/
def forcingBound : ℝ :=
  compBound k (temperatureBound k α R₁ N Nlow T) (flowBound k α R₁ Nlow T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the forcing. -/
def forcingHolder : ℝ :=
  compHolder k α (temperatureBound k α R₁ N Nlow T) (temperatureHolder k α R₁ N Nlow T)
    (flowBound k α R₁ Nlow T) (flowHolder k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The constant term of the bound of the derivative of order `k` of the forcing. -/
def forcingTopConst : ℝ :=
  compTopBound k (temperatureBound k α R₁ N Nlow T) (temperatureTopConst k α R₁ N Nlow T)
    (flowBound k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The coefficient of `Ψ(r)` in the bound of the derivative of order `k` of the forcing. -/
def forcingTopSlope : ℝ :=
  temperatureTopSlope k α R₁ N Nlow T * flowBound k α R₁ Nlow T ^ k

/-- The constant term of the Hölder constant of the derivative of order `k` of the forcing. -/
def forcingTopHolderConst : ℝ :=
  compTopHolder k α (temperatureBound k α R₁ N Nlow T) (temperatureHolder k α R₁ N Nlow T)
    (temperatureTopConst k α R₁ N Nlow T) (temperatureTopHolderConst k α R₁ N Nlow T)
    (flowBound k α R₁ Nlow T) (flowHolder k α R₁ Nlow T) (flowBound k α R₁ Nlow T)
    (flowHolder k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The coefficient of `Ψ(r)` in the Hölder constant of the derivative of order `k` of the
forcing. -/
def forcingTopHolderSlope : ℝ :=
  temperatureTopSlope k α R₁ N Nlow T * k * flowBound k α R₁ Nlow T ^ (k - 1) *
      flowHolder k α R₁ Nlow T +
    temperatureTopHolderSlope k α R₁ N Nlow T * flowBound k α R₁ Nlow T ^ α *
      flowBound k α R₁ Nlow T ^ k

end Constants

/-! ### The carried temperature -/

section Carried

variable {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ} {α R N T R₁ B Nlow : ℝ} {P : ℝ → ℝ}

/-- On the closed half-plane the flow of the field of the iteration is the flow of the field of
order `k + 1`. -/
theorem flowOn_historyField_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 1 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    flowOn (historyField ω) (-T) T s t x =
      flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t x :=
  flowOn_extendedVelocity_eq (h.history.toIsVorticityHistory hα.le hα1.le) hα hα1 (K := 2)
    (K' := k + 1) (by norm_num) (by omega)
    (fun t ht ↦ (h.history.contDiffOn_halfPlaneVelocity hα hα1 ht).of_le
      (by exact_mod_cast (by omega : 2 ≤ k + 1)))
    (fun t ht ↦ h.history.contDiffOn_halfPlaneVelocity hα hα1 ht) hs ht hx

/-- On the closed half-plane the first variation of the flow of the field of the iteration is
that of the field of order `k + 1`. -/
theorem variationOn_historyField_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 1 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    variationOn (historyField ω) (historyFieldDeriv ω) (-T) T s t x =
      variationOn (fun r ↦ extendedVelocity (k + 1) (ω r))
        (fun r y ↦ fderiv ℝ (extendedVelocity (k + 1) (ω r)) y) (-T) T s t x :=
  variationOn_extendedVelocity_eq (h.history.toIsVorticityHistory hα.le hα1.le) hα hα1 (K := 2)
    (K' := k + 1) (by norm_num) (by omega)
    (fun t ht ↦ (h.history.contDiffOn_halfPlaneVelocity hα hα1 ht).of_le
      (by exact_mod_cast (by omega : 2 ≤ k + 1)))
    (fun t ht ↦ h.history.contDiffOn_halfPlaneVelocity hα hα1 ht) hs ht hx

/-- On the closed half-plane the carried temperature at time `t` is `θ₀ ∘ Y_t`. -/
theorem carriedTemperature_eqOn (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    EqOn (fun x ↦ carriedTemperature θ₀ ω (-T) T x t)
      (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 t) H̄ := fun x hx ↦ by
  simp only [carriedTemperature, Function.comp_apply]
  rw [flowOn_historyField_eq h hα hα1 hk (zero_mem_Icc_neg_of_mem ht) ht hx,
    dataTemperature_of_nonneg θ₀ (h.mapsTo_flowOn hα hα1 (zero_mem_Icc_neg_of_mem ht) ht hx)]

/-- **The `C^{k+1,α}` bounds of the temperature carried by the flow of order `k + 1`.** -/
theorem hasHolderBounds_comp_flowOn (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 t) α
      (temperatureBound k α R₁ N Nlow T) (temperatureHolder k α R₁ N Nlow T)
      (temperatureTopConst k α R₁ N Nlow T +
        temperatureTopSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|)
      (temperatureTopHolderConst k α R₁ N Nlow T +
        temperatureTopHolderSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hc := (hd.hasHolderBounds_temperature hα.le hα1.le).comp
    (h.hasHolderBounds_flowOn_succ hα hα1 hk h0 ht) (h.mapsTo_flowOn hα hα1 h0 ht)
    (IsTopBoundedHistory.flowBound_nonneg (by omega))
    (fun z z' hz hz' ↦ h.norm_flowOn_sub_le hα hα1 (by omega) h0 ht hz hz') (by omega) hα.le
  rw [compTopBound_inner_affine, compTopHolder_inner_affine] at hc
  exact hc

/-- **The `C^{k+1,α}` bounds of the carried temperature** at a time `t ∈ [-T, T]`. -/
theorem hasHolderBounds_carriedTemperature (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (fun x ↦ carriedTemperature θ₀ ω (-T) T x t) α
      (temperatureBound k α R₁ N Nlow T) (temperatureHolder k α R₁ N Nlow T)
      (temperatureTopConst k α R₁ N Nlow T +
        temperatureTopSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|)
      (temperatureTopHolderConst k α R₁ N Nlow T +
        temperatureTopHolderSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|) :=
  (hasHolderBounds_comp_flowOn h hd hα hα1 hk ht).congr
    (carriedTemperature_eqOn h hα hα1 (by omega) ht)

/-- The carried temperature is bounded by `N` on the closed half-plane. -/
theorem abs_carriedTemperature_le (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedTemperature θ₀ ω (-T) T x t| ≤ N := by
  have he : carriedTemperature θ₀ ω (-T) T x t = _ := carriedTemperature_eqOn h hα hα1 hk ht hx
  rw [he, Function.comp_apply]
  have h0 := hd.norm_temperature_le 0 (Nat.zero_le _) _
    (h.mapsTo_flowOn hα hα1 (zero_mem_Icc_neg_of_mem ht) ht hx)
  rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at h0

/-! ### The forcing -/

/-- At a label `y` of the closed half-plane and a time `r ∈ [-T, T]`, the derivative within `H̄`
of `θ₀` at `y` applied to the inverse first variation along the particle is the derivative within
`H̄` of `θ₀ ∘ Y_r` at the position `X_r y`. -/
theorem fderivWithin_apply_variationOn_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) {r : ℝ}
    (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) (e : ℝ^2) :
    fderivWithin ℝ θ₀ H̄ y (variationOn (fun r ↦ extendedVelocity (k + 1) (ω r))
        (fun r y ↦ fderiv ℝ (extendedVelocity (k + 1) (ω r)) y) (-T) T 0 r
        (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0 y) e) =
      fderivWithin ℝ (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 r) H̄
        (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0 y) e := by
  set v := fun r ↦ extendedVelocity (k + 1) (ω r)
  have h0 := zero_mem_Icc_neg_of_mem hr
  have hv := h.history.isC1FieldOn_extendedVelocity hα hα1
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  set z := flowOn v (-T) T r 0 y
  have hz : 0 ≤ z 1 := h.mapsTo_flowOn hα hα1 hr h0 hy
  have hzy : flowOn v (-T) T 0 r z = y := hv.isLipschitzFieldOn.flowOn_flowOn_self hr h0 y
  have hθ : DifferentiableOn ℝ θ₀ H̄ :=
    hd.temperature_contDiffOn.differentiableOn (by exact_mod_cast (show k + 1 ≠ 0 by omega))
  have hY : HasFDerivAt (flowOn v (-T) T 0 r)
      (variationOn v (fun r y ↦ fderiv ℝ (v r) y) (-T) T 0 r z) z := hv.hasFDerivAt_flowOn h0 hr z
  rw [fderivWithin_comp z (hθ _ (by rw [hzy]; exact hy)) hY.differentiableAt.differentiableWithinAt
      (h.mapsTo_flowOn hα hα1 h0 hr) (hU z hz),
    hY.differentiableAt.fderivWithin (hU z hz), hY.fderiv, hzy]
  rfl

/-- **The label forcing of the iteration** at a label `y` of the closed half-plane and a time
`r ∈ [-T, T]` is `∂₀(θ₀ ∘ Y_r)` at the position `X_r y`, with the flow of order `k + 1`. -/
theorem labelForcing_historyField_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) {r : ℝ}
    (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    labelForcing (historyField ω) (historyFieldDeriv ω) (-T) T (dataTemperature θ₀)
        (EuclideanSpace.single 0 1) y r =
      fderivWithin ℝ (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 r) H̄
        (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0 y)
        (EuclideanSpace.single 0 1) := by
  have h0 := zero_mem_Icc_neg_of_mem hr
  unfold labelForcing
  rw [flowOn_historyField_eq h hα hα1 hk hr h0 hy, variationOn_historyField_eq h hα hα1 hk h0 hr
      (h.mapsTo_flowOn hα hα1 hr h0 hy),
    (hd.toIsHolderData (by omega) hα.le hα1.le).fderiv_dataTemperature hy]
  exact fderivWithin_apply_variationOn_eq h hd hα hα1 hr hy _

/-- **The `C^{k,α}` bounds of the forcing in label form** `∂₀(θ₀ ∘ Y_r) ∘ X_r` at a time
`r ∈ [-T, T]`, with top-order constants affine in `Ψ(r) = |∫₀ʳ P(|r'|) dr'|`. -/
theorem hasHolderBounds_forcing (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {r : ℝ}
    (hr : r ∈ Icc (-T) T) :
    HasHolderBounds k ((fun z ↦ fderivWithin ℝ
        (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 r) H̄ z
          (EuclideanSpace.single 0 1)) ∘
        flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0) α
      (forcingBound k α R₁ N Nlow T) (forcingHolder k α R₁ N Nlow T)
      (forcingTopConst k α R₁ N Nlow T +
        forcingTopSlope k α R₁ N Nlow T * |∫ r' in r..0, P (|r'|)|)
      (forcingTopHolderConst k α R₁ N Nlow T +
        forcingTopHolderSlope k α R₁ N Nlow T * |∫ r' in r..0, P (|r'|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem hr
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  have hθ := (hasHolderBounds_comp_flowOn h hd hα hα1 hk hr).fderivWithin_apply
    (EuclideanSpace.single 0 1)
  simp only [he, one_mul] at hθ
  have hc := hθ.comp (h.hasHolderBounds_flowOn hα hα1 hk hr h0) (h.mapsTo_flowOn hα hα1 hr h0)
    (IsTopBoundedHistory.flowBound_nonneg (by omega))
    (fun z z' hz hz' ↦ h.norm_flowOn_sub_le hα hα1 (by omega) hr h0 hz hz') hk hα.le
  rw [compTopBound_outer_affine, compTopHolder_outer_affine] at hc
  exact hc

end Carried

end Boussinesq.HalfPlane
