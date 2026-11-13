/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.CarriedBoundsHigher
public import PDE.Analysis.Calculus.SmoothFamilyIntegral
public import PDE.Analysis.ODE.Flow.VariationInverse
public import PDE.Analysis.Calculus.HolderUniform
import PDE.Analysis.Calculus.IntegralMajorant
import PDE.Fluid.Boussinesq.HalfPlane.IterationBounds

/-!
# The amplitude and the carried vorticity at level `k`

Let `(ω₀, θ₀)` be data of order `k ≥ 2` vanishing outside the disc of radius `R`, with bound `N`
(`IsHolderDataOf k`), and `ω` a `C^{k,α}` history on `[-T, T]` with support radius `R₁`, bound `B`,
lower-order bound `Nlow` and top-order majorant `P` (`IsTopBoundedHistory`). With
`v r = extendedVelocity (k + 1) (ω r)`, `Y_t = flowOn v 0 t` the label map and `X_r = flowOn v r 0`
the position map, we bound the amplitude of the particles and the vorticity carried by the flow of
`v` in `C^{k,α}` on the closed half-plane `H̄`, with top-order constants affine in
`Φ(t) = ∫₀^{|t|} P`. The carried history is then again a `C^{k,α}` history.

## Main definitions

* `labelForcingOf`: the forcing in label form `Dθ̃₀(y) (W e₀)`, with
  `θ̃₀ = weightedReflectionFun 1 (k + 1) θ₀`, `e₀ = EuclideanSpace.single 0 1` and `W` the inverse
  first variation along the particle of label `y`.
* `amplitudeOf`: the amplitude `ω̃₀(y) + ∫₀ᵗ labelForcingOf k ω T θ₀ y r dr`, with
  `ω̃₀ = weightedReflectionFun 1 k ω₀`.
* `vorticityBound`, `vorticityTopConst`, `vorticityTopSlope` and their Hölder counterparts: the
  constants of the bounds of the carried vorticity, functions of `k, α, R₁, N, Nlow, T` only.
* `carriedBound`: a bound of the carried vorticity at all times of `[-T, T]`, built from `∫₀ᵀ P`.

## Main results

* `hasHolderBounds_amplitudeOf`: the amplitude at time `t` has `C^{k,α}` bounds on `H̄` with
  top-order constants affine in `Φ(t)`, written there as `|∫ₜ⁰ P(|r|) dr|` (`abs_integral_eq`).
* `carriedVorticity_bounds`: the carried vorticity at time `t` has `C^{k,α}` bounds on `H̄` with
  `vorticityBound`, `vorticityHolder` below the top order and the top-order constants
  `vorticityTopConst + vorticityTopSlope Φ(t)`,
  `vorticityTopHolderConst + vorticityTopHolderSlope Φ(t)`; its values are at most
  `vorticityValueBound` (`abs_carriedVorticity_le_vorticityValueBound`).
* `carriedTemperature_bounds`: the carried temperature has `C^{k+1,α}` bounds of the same form; its
  values are at most `N` (`abs_carriedTemperature_le`).
* `uniform_carriedTemperature`: the derivatives of order at most `k + 1` of the carried temperature
  are continuous in time uniformly on `H̄`.
* `isCkVorticityHistory_carriedHistory`: the carried history is a `C^{k,α}` history on `[-T, T]`
  with support radius `R + (1 + R₁²) B T` and bound `carriedBound`.

## How it works

The forcing is a smooth family of order `k` in time (`isSmoothFamilyOn_labelForcingOf`), since `W`
is the ring inverse of the derivative of the position map
(`IsC1FieldOn.isSmoothFamilyOn_variationOn_flowOn`). We may therefore differentiate under the
integral: the derivatives of order `j ≤ k` of the amplitude are those of `ω̃₀` plus the integrals of
those of the forcing (`iteratedFDeriv_amplitudeOf`). On `H̄` the forcing at `y` is the derivative of
`θ₀ ∘ Y_r` in the direction `e₀` at `X_r(y)` (`labelForcingOf_eq`), so the bounds
`hasHolderBounds_forcing` integrate over the times `r` between `0` and `t`, where `Φ(r) ≤ Φ(t)`
(`abs_integral_le_of_mem`). The carried vorticity is the amplitude at the label `Y_t(x)`
(`carriedVorticity_eq`), and the composition bounds `HasHolderBounds.comp` with the bounds
`IsTopBoundedHistory.hasHolderBounds_flowOn` of the label map give
`hasHolderBounds_carriedVorticity`, the top-order constants staying affine
(`compTopBound_outer_affine`, `compTopHolder_outer_affine`). For
`isCkVorticityHistory_carriedHistory` we bound each affine constant by its value at `∫₀ᵀ P`, take
the support from `IsBoundedFlowOn.carried_eq_zero`, and get the continuity in time of the
derivatives from the uniform Hölder bounds and that of the values
(`uniform_iteratedFDerivWithin_of_holder`).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open IncompressibleFlow PDE.Analysis PDE.Analysis.ODE PDE.Hyperbolic.Transport
open SobolevSpace.GraphSpace.HigherOrderReflection
open scoped Interval

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The forcing in label form of the field `extendedVelocity (k + 1) (ω r)` and of the extension
of order `k + 1` of the temperature datum, on the times `[-T, T]`. -/
def labelForcingOf (k : ℕ) (ω : ℝ → ℝ^2 → ℝ) (T : ℝ) (θ₀ : ℝ^2 → ℝ) : ℝ^2 → ℝ → ℝ :=
  labelForcing (fun r ↦ extendedVelocity (k + 1) (ω r))
    (fun r y ↦ fderiv ℝ (extendedVelocity (k + 1) (ω r)) y) (-T) T
    (weightedReflectionFun 1 (k + 1) θ₀) (EuclideanSpace.single 0 1)

/-- The amplitude at level `k`: `ω̃₀(y) + ∫₀ᵗ labelForcingOf k ω T θ₀ y r dr` with the extension
of order `k` of the vorticity datum. -/
def amplitudeOf (k : ℕ) (ω₀ θ₀ : ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (T : ℝ) : ℝ^2 → ℝ → ℝ :=
  forcedAmplitude (weightedReflectionFun 1 k ω₀) (labelForcingOf k ω T θ₀)

section Constants

variable (k : ℕ) (α R₁ N Nlow T : ℝ)

/-- The bound of the derivatives of orders `1 ≤ j < k` of the amplitude. -/
def amplitudeBound : ℝ :=
  N + T * forcingBound k α R₁ N Nlow T

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the amplitude. -/
def amplitudeHolder : ℝ :=
  2 * N + T * forcingHolder k α R₁ N Nlow T

/-- The constant term of the bound of the derivative of order `k` of the amplitude. -/
def amplitudeTopConst : ℝ :=
  N + T * forcingTopConst k α R₁ N Nlow T

/-- The coefficient of `Ψ(t)` in the bound of the derivative of order `k` of the amplitude. -/
def amplitudeTopSlope : ℝ :=
  T * forcingTopSlope k α R₁ N Nlow T

/-- The constant term of the Hölder constant of the derivative of order `k` of the amplitude. -/
def amplitudeTopHolderConst : ℝ :=
  N + T * forcingTopHolderConst k α R₁ N Nlow T

/-- The coefficient of `Ψ(t)` in the Hölder constant of the derivative of order `k` of the
amplitude. -/
def amplitudeTopHolderSlope : ℝ :=
  T * forcingTopHolderSlope k α R₁ N Nlow T

/-- The bound of the derivatives of orders `1 ≤ j < k` of the carried vorticity. -/
def vorticityBound : ℝ :=
  compBound k (amplitudeBound k α R₁ N Nlow T) (flowBound k α R₁ Nlow T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the carried vorticity. -/
def vorticityHolder : ℝ :=
  compHolder k α (amplitudeBound k α R₁ N Nlow T) (amplitudeHolder k α R₁ N Nlow T)
    (flowBound k α R₁ Nlow T) (flowHolder k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The constant term of the bound of the derivative of order `k` of the carried vorticity. -/
def vorticityTopConst : ℝ :=
  compTopBound k (amplitudeBound k α R₁ N Nlow T) (amplitudeTopConst k α R₁ N Nlow T)
    (flowBound k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The coefficient of `Ψ(t)` in the bound of the derivative of order `k` of the carried
vorticity. -/
def vorticityTopSlope : ℝ :=
  amplitudeTopSlope k α R₁ N Nlow T * flowBound k α R₁ Nlow T ^ k

/-- The constant term of the Hölder constant of the derivative of order `k` of the carried
vorticity. -/
def vorticityTopHolderConst : ℝ :=
  compTopHolder k α (amplitudeBound k α R₁ N Nlow T) (amplitudeHolder k α R₁ N Nlow T)
    (amplitudeTopConst k α R₁ N Nlow T) (amplitudeTopHolderConst k α R₁ N Nlow T)
    (flowBound k α R₁ Nlow T) (flowHolder k α R₁ Nlow T) (flowBound k α R₁ Nlow T)
    (flowHolder k α R₁ Nlow T) (flowBound k α R₁ Nlow T)

/-- The coefficient of `Ψ(t)` in the Hölder constant of the derivative of order `k` of the
carried vorticity. -/
def vorticityTopHolderSlope : ℝ :=
  amplitudeTopSlope k α R₁ N Nlow T * k * flowBound k α R₁ Nlow T ^ (k - 1) *
      flowHolder k α R₁ Nlow T +
    amplitudeTopHolderSlope k α R₁ N Nlow T * flowBound k α R₁ Nlow T ^ α *
      flowBound k α R₁ Nlow T ^ k

/-- The bound of the values of the carried vorticity. -/
def vorticityValueBound : ℝ :=
  N + T * temperatureBound k α R₁ N Nlow T

/-- A common bound of the derivatives of order at most `k` and of the Hölder constant of the
derivative of order `k` of the carried vorticity at all times of `[-T, T]`, with
`Φ = ∫₀ᵀ P`. -/
def carriedBound (Φ : ℝ) : ℝ :=
  vorticityValueBound k α R₁ N Nlow T + vorticityBound k α R₁ N Nlow T +
    (|vorticityTopConst k α R₁ N Nlow T| + |vorticityTopSlope k α R₁ N Nlow T| * Φ) +
    (|vorticityTopHolderConst k α R₁ N Nlow T| + |vorticityTopHolderSlope k α R₁ N Nlow T| * Φ)

end Constants

section Amplitude

variable {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ} {α R N T R₁ B Nlow : ℝ} {P : ℝ → ℝ}

/-- **The forcing at level `k` is a smooth family of order `k`** on `[-T, T]`. -/
theorem isSmoothFamilyOn_labelForcingOf (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) :
    IsSmoothFamilyOn k (fun r y ↦ labelForcingOf k ω T θ₀ y r) (Icc (-T) T) := by
  have hv := h.history.isC1FieldOn_extendedVelocity hα hα1
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hW := hv.isSmoothFamilyOn_variationOn_flowOn (h.isSmoothFamilyOn hα hα1) h0
  have hθ : ContDiff ℝ (k + 1 : ℕ) (weightedReflectionFun 1 (k + 1) θ₀) :=
    contDiff_weightedReflectionFun 1 (by omega) hd.temperature_contDiffOn
  have hDθ : IsSmoothFamilyOn k (fun (_ : ℝ) y ↦ fderiv ℝ (weightedReflectionFun 1 (k + 1) θ₀) y)
      (Icc (-T) T) :=
    isSmoothFamilyOn_const (hθ.fderiv_right (by push_cast; exact le_rfl))
  have hWe := hW.clm_comp (ContinuousLinearMap.apply ℝ (ℝ^2) (EuclideanSpace.single 0 1))
  refine (hDθ.bilinear (ContinuousLinearMap.id ℝ (ℝ^2 →L[ℝ] ℝ)) hWe).congr fun r _ ↦ ?_
  funext y
  rfl

/-- On the closed half-plane the forcing at level `k` is `∂₀(θ₀ ∘ Y_r) ∘ X_r`. -/
theorem labelForcingOf_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) {r : ℝ}
    (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    labelForcingOf k ω T θ₀ y r =
      fderivWithin ℝ (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 r) H̄
        (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0 y)
        (EuclideanSpace.single 0 1) := by
  unfold labelForcingOf labelForcing
  rw [fderiv_weightedReflectionFun_of_nonneg 1 (k := k + 1) (by omega)
    hd.temperature_contDiffOn hy]
  exact fderivWithin_apply_variationOn_eq h hd hα hα1 hr hy _

/-- **The carried vorticity is the amplitude at level `k` at the label**, on the closed
half-plane. -/
theorem carriedVorticity_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    carriedVorticity ω₀ θ₀ ω (-T) T x t = amplitudeOf k ω₀ θ₀ ω T
      (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 t x) t := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  unfold carriedVorticity amplitudeOf forcedAmplitude
  rw [flowOn_historyField_eq h hα hα1 hk h0 ht hx]
  set Y := flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 t x
  have hY : 0 ≤ Y 1 := h.mapsTo_flowOn hα hα1 h0 ht hx
  congr 1
  · rw [dataVorticity_of_nonneg ω₀ hY, weightedReflectionFun_eq_of_nonneg 1 k ω₀ Y hY]
  · refine intervalIntegral.integral_congr fun r hr ↦ ?_
    have hr' : r ∈ Icc (-T) T := uIcc_subset_Icc h0 ht hr
    rw [labelForcing_historyField_eq h hd hα hα1 hk hr' hY, labelForcingOf_eq h hd hα hα1 hr' hY]

/-- The amplitude at level `k` is `C^k` in the label. -/
theorem contDiff_amplitudeOf (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ContDiff ℝ k fun y ↦ amplitudeOf k ω₀ θ₀ ω T y t := by
  unfold amplitudeOf forcedAmplitude
  exact (contDiff_weightedReflectionFun 1 hk hd.vorticity_contDiffOn).add
    ((isSmoothFamilyOn_labelForcingOf h hd hα hα1 hT).contDiff_integral (zero_mem_Icc_neg_of_mem
        ht) ht)

/-- The derivatives of order `j ≤ k` of the amplitude are those of `ω̃₀` plus the integrals of
those of the forcing. -/
theorem iteratedFDeriv_amplitudeOf (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (-T) T) {j : ℕ} (hj : j ≤ k) (y : ℝ^2) :
    iteratedFDeriv ℝ j (fun y ↦ amplitudeOf k ω₀ θ₀ ω T y t) y =
      iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) y +
        ∫ r in (0)..t, iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) y := by
  have hG := isSmoothFamilyOn_labelForcingOf h hd hα hα1 hT
  have h1 : ContDiff ℝ j (weightedReflectionFun 1 k ω₀) :=
    (contDiff_weightedReflectionFun 1 hk hd.vorticity_contDiffOn).of_le (by exact_mod_cast hj)
  have h2 : ContDiff ℝ j fun y ↦ ∫ r in (0)..t, labelForcingOf k ω T θ₀ y r :=
    (hG.contDiff_integral (zero_mem_Icc_neg_of_mem ht) ht).of_le (by exact_mod_cast hj)
  have e : (fun y ↦ amplitudeOf k ω₀ θ₀ ω T y t) =
      weightedReflectionFun 1 k ω₀ + fun y ↦ ∫ r in (0)..t, labelForcingOf k ω T θ₀ y r := by
    funext y; unfold amplitudeOf forcedAmplitude; rfl
  rw [e, iteratedFDeriv_add_apply h1.contDiffAt h2.contDiffAt,
    iteratedFDeriv_integral_of_isSmoothFamilyOn hG (zero_mem_Icc_neg_of_mem ht) ht hj y]

/-- The coefficients of `Ψ` in the top-order constants of the forcing are nonnegative. -/
theorem forcingSlopes_nonneg (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) (hT : 0 ≤ T) :
    0 ≤ forcingTopSlope k α R₁ N Nlow T ∧ 0 ≤ forcingTopHolderSlope k α R₁ N Nlow T := by
  have hN := hd.nonneg
  have hNlow := h.low_nonneg hT
  have hF0 : 0 ≤ flowBound k α R₁ Nlow T := IsTopBoundedHistory.flowBound_nonneg hk
  have hcv := velocityConst_nonneg k hα R₁
  have hch := velocityHolderConst_nonneg k hα hα1
  have hc0 : 0 ≤ fieldBound k α R₁ Nlow := h.fieldBound_nonneg hα hT
  have hτ0 : 0 ≤ T - -T := by linarith
  have hHf : 0 ≤ flowHolder k α R₁ Nlow T := flowHolder_nonneg hc0 hF0 hch hNlow hτ0
  have hC₃ := flowTopSlope_nonneg (Nlow := Nlow) (T := T) hcv hF0
  have hB' := flowTopRateSlope_nonneg hcv hch hF0
  have hC₄ : 0 ≤ flowTopHolderSlope k α R₁ Nlow T := by unfold flowTopHolderSlope; positivity
  have hTS : 0 ≤ temperatureTopSlope k α R₁ N Nlow T := by unfold temperatureTopSlope; positivity
  have hTHS : 0 ≤ temperatureTopHolderSlope k α R₁ N Nlow T := by
    unfold temperatureTopHolderSlope; positivity
  exact ⟨by unfold forcingTopSlope; positivity, by unfold forcingTopHolderSlope; positivity⟩

/-- Between `0` and `t` the integral `|∫₀ʳ P(|r'|) dr'|` is at most its value at `t`. -/
theorem abs_integral_le_of_mem (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) {t r : ℝ}
    (ht : t ∈ Icc (-T) T) (hr : r ∈ uIcc 0 t) :
    |∫ r' in r..0, P (|r'|)| ≤ |∫ r' in t..0, P (|r'|)| := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  rw [intervalIntegral.integral_symm 0 r, abs_neg, intervalIntegral.integral_symm 0 t, abs_neg]
  exact abs_integral_le_of_mem_uIcc (h.intervalIntegrable_abs ht h0)
    (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc h0 ht hr)) hr

/-- `|∫ₜ⁰ P(|r|) dr| = ∫₀^{|t|} P`. -/
theorem abs_integral_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) {t : ℝ}
    (ht : t ∈ Icc (-T) T) : |∫ r in t..0, P (|r|)| = ∫ r in (0)..(|t|), P r := by
  rw [intervalIntegral.integral_symm, abs_neg]
  exact abs_integral_comp_abs fun r hr ↦ h.nonneg r ⟨hr.1, hr.2.trans
    (IsTopBoundedHistory.abs_mem_Icc ht).2⟩

/-- On the closed half-plane the derivatives of order `j ≤ k` of the forcing at level `k` are
those of `∂₀(θ₀ ∘ Y_r) ∘ X_r` within the closed half-plane. -/
theorem iteratedFDeriv_labelForcingOf_eq (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) {r : ℝ}
    (hr : r ∈ Icc (-T) T) {j : ℕ} (hj : j ≤ k) {y : ℝ^2} (hy : 0 ≤ y 1) :
    iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) y =
      iteratedFDerivWithin ℝ j ((fun z ↦ fderivWithin ℝ
        (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 r) H̄ z
          (EuclideanSpace.single 0 1)) ∘
        flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0) H̄ y := by
  rw [← iteratedFDerivWithin_closedUpper_eq
    ((isSmoothFamilyOn_labelForcingOf h hd hα hα1 hT).contDiff hr) hj hy]
  have heq : EqOn (fun y ↦ labelForcingOf k ω T θ₀ y r) ((fun z ↦ fderivWithin ℝ
      (θ₀ ∘ flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T 0 r) H̄ z
        (EuclideanSpace.single 0 1)) ∘
      flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0) H̄ := fun z hz ↦
    labelForcingOf_eq h hd hα hα1 hr hz
  exact iteratedFDerivWithin_congr heq hy j

/-- **The `C^{k,α}` bounds of the amplitude at level `k`** at a time `t ∈ [-T, T]`, with top-order
constants affine in `Ψ(t) = |∫ₜ⁰ P(|r|) dr|`. -/
theorem hasHolderBounds_amplitudeOf (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k (fun y ↦ amplitudeOf k ω₀ θ₀ ω T y t) α
      (amplitudeBound k α R₁ N Nlow T) (amplitudeHolder k α R₁ N Nlow T)
      (amplitudeTopConst k α R₁ N Nlow T +
        amplitudeTopSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|)
      (amplitudeTopHolderConst k α R₁ N Nlow T +
        amplitudeTopHolderSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hG := isSmoothFamilyOn_labelForcingOf h hd hα hα1 hT
  have hω₀ := hd.vorticity_contDiffOn
  have hN := hd.nonneg
  have htT : |t - 0| ≤ T := by rw [sub_zero]; exact abs_le.mpr ⟨ht.1, ht.2⟩
  have hFt := hasHolderBounds_forcing h hd hα hα1 hk ht
  have hd0 (z z' : ℝ^2) : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  obtain ⟨hfTS, hfTHS⟩ := forcingSlopes_nonneg h hd hα hα1 (by omega) hT
  have hr' {r : ℝ} (hr : r ∈ Ι 0 t) : r ∈ Icc (-T) T := uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)
  have hΨ {r : ℝ} (hr : r ∈ Ι 0 t) : |∫ r' in r..0, P (|r'|)| ≤ |∫ r' in t..0, P (|r'|)| :=
    abs_integral_le_of_mem h ht (uIoc_subset_uIcc hr)
  have hint (j : ℕ) (hj : j ≤ k) (z : ℝ^2) : IntervalIntegrable
      (fun r ↦ iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z) volume 0 t :=
    ((continuousOn_iteratedFDeriv_slice hG hj z).mono (uIcc_subset_Icc h0 ht)).intervalIntegrable
  have hint_le {j : ℕ} {C : ℝ} (hC : 0 ≤ C)
      {f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ ℝ^2) ℝ}
      (hf : ∀ r ∈ Ι 0 t, ‖f r‖ ≤ C) : ‖∫ r in (0)..t, f r‖ ≤ T * C :=
    (intervalIntegral.norm_integral_le_of_norm_le_const hf).trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right htT hC)
  have hdiff {j : ℕ} (hj : j ≤ k) (z z' : ℝ^2) :
      (iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z +
          ∫ r in (0)..t, iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z) -
        (iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z' +
          ∫ r in (0)..t, iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z') =
      (iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z -
          iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z') +
        ∫ r in (0)..t, (iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z -
          iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z') := by
    rw [intervalIntegral.integral_sub (hint j hj z) (hint j hj z')]
    abel
  refine HasHolderBounds.of_contDiff (contDiff_amplitudeOf h hd hα hα1 (by omega) hT ht)
    (fun j hj hjk z hz ↦ ?_) (fun j hj hjk z z' hz hz' ↦ ?_) (fun z hz ↦ ?_)
    (fun z z' hz hz' ↦ ?_)
  · rw [iteratedFDeriv_amplitudeOf h hd hα hα1 (by omega) hT ht hjk.le,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ hjk.le hz]
    refine (norm_add_le _ _).trans (add_le_add (hd.norm_vorticity_le j hjk.le z hz)
      (hint_le (hFt.bound_nonneg hk)
        (f := fun r ↦ iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z) fun r hr ↦ ?_))
    rw [iteratedFDeriv_labelForcingOf_eq h hd hα hα1 hT (hr' hr) hjk.le hz]
    exact (hasHolderBounds_forcing h hd hα hα1 hk (hr' hr)).norm_le j hj hjk z hz
  · rw [iteratedFDeriv_amplitudeOf h hd hα hα1 (by omega) hT ht hjk.le,
      iteratedFDeriv_amplitudeOf h hd hα hα1 (by omega) hT ht hjk.le, hdiff hjk.le,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ hjk.le hz,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ hjk.le hz']
    refine (norm_add_le _ _).trans ?_
    have h2 := hint_le (mul_nonneg (hFt.holder_nonneg hk) (hd0 z z'))
      (f := fun r ↦ iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z -
        iteratedFDeriv ℝ j (fun y ↦ labelForcingOf k ω T θ₀ y r) z') fun r hr ↦ by
      rw [iteratedFDeriv_labelForcingOf_eq h hd hα hα1 hT (hr' hr) hjk.le hz,
        iteratedFDeriv_labelForcingOf_eq h hd hα hα1 hT (hr' hr) hjk.le hz']
      exact (hasHolderBounds_forcing h hd hα hα1 hk (hr' hr)).holder j hj hjk z z' hz hz'
    simp only [amplitudeHolder]
    linarith [hd.norm_iteratedFDerivWithin_vorticity_sub_le hα.le hα1.le hjk.le hz hz']
  · rw [iteratedFDeriv_amplitudeOf h hd hα hα1 (by omega) hT ht le_rfl,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ le_rfl hz]
    refine (norm_add_le _ _).trans ?_
    have h2 := hint_le hFt.top_nonneg
      (f := fun r ↦ iteratedFDeriv ℝ k (fun y ↦ labelForcingOf k ω T θ₀ y r) z) fun r hr ↦ by
      rw [iteratedFDeriv_labelForcingOf_eq h hd hα hα1 hT (hr' hr) le_rfl hz]
      exact ((hasHolderBounds_forcing h hd hα hα1 hk (hr' hr)).norm_top_le z hz).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hΨ hr) hfTS))
    simp only [amplitudeTopConst, amplitudeTopSlope]
    linarith [hd.norm_vorticity_le k le_rfl z hz]
  · rw [iteratedFDeriv_amplitudeOf h hd hα hα1 (by omega) hT ht le_rfl,
      iteratedFDeriv_amplitudeOf h hd hα hα1 (by omega) hT ht le_rfl, hdiff le_rfl,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ le_rfl hz,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ le_rfl hz']
    refine (norm_add_le _ _).trans ?_
    have h2 := hint_le (mul_nonneg hFt.holder_top_nonneg (hd0 z z'))
      (f := fun r ↦ iteratedFDeriv ℝ k (fun y ↦ labelForcingOf k ω T θ₀ y r) z -
        iteratedFDeriv ℝ k (fun y ↦ labelForcingOf k ω T θ₀ y r) z') fun r hr ↦ by
      rw [iteratedFDeriv_labelForcingOf_eq h hd hα hα1 hT (hr' hr) le_rfl hz,
        iteratedFDeriv_labelForcingOf_eq h hd hα hα1 hT (hr' hr) le_rfl hz']
      exact ((hasHolderBounds_forcing h hd hα hα1 hk (hr' hr)).holder_top z z' hz hz').trans
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (hΨ hr) hfTHS)) (hd0 z z'))
    simp only [amplitudeTopHolderConst, amplitudeTopHolderSlope]
    linarith [hd.holder_vorticity z z' hz hz']

/-- **The values of the amplitude** are at most `N + T temperatureBound` on the closed
half-plane. -/
theorem abs_amplitudeOf_le (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    |amplitudeOf k ω₀ θ₀ ω T y t| ≤ vorticityValueBound k α R₁ N Nlow T := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  have hθt := hasHolderBounds_comp_flowOn h hd hα hα1 hk ht
  have hTb : 0 ≤ temperatureBound k α R₁ N Nlow T := hθt.bound_nonneg (by omega)
  unfold amplitudeOf forcedAmplitude
  have h1 : |weightedReflectionFun 1 k ω₀ y| ≤ N := by
    rw [weightedReflectionFun_eq_of_nonneg 1 k ω₀ y hy]
    have := hd.norm_vorticity_le 0 (Nat.zero_le _) y hy
    rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at this
  have h2 : ‖∫ r in (0)..t, labelForcingOf k ω T θ₀ y r‖ ≤
      temperatureBound k α R₁ N Nlow T * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    have hr' : r ∈ Icc (-T) T := uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)
    have hθ := hasHolderBounds_comp_flowOn h hd hα hα1 hk hr'
    set X := flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T r 0 y
    have hX : 0 ≤ X 1 := h.mapsTo_flowOn hα hα1 hr' h0 hy
    rw [labelForcingOf_eq h hd hα hα1 hr' hy]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
    rw [he, mul_one, ← norm_iteratedFDerivWithin_one _ (hU X hX)]
    exact hθ.norm_le 1 le_rfl (by omega) X hX
  have htT : |t - 0| ≤ T := by rw [sub_zero]; exact abs_le.mpr ⟨ht.1, ht.2⟩
  rw [Real.norm_eq_abs] at h2
  simp only [vorticityValueBound]
  linarith [mul_le_mul_of_nonneg_left htT hTb, abs_add_le (weightedReflectionFun 1 k ω₀ y)
    (∫ r in (0)..t, labelForcingOf k ω T θ₀ y r)]

/-- **The `C^{k,α}` bounds of the carried vorticity** at a time `t ∈ [-T, T]`, with top-order
constants affine in `Ψ(t) = |∫ₜ⁰ P(|r|) dr|`. -/
theorem hasHolderBounds_carriedVorticity (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k (fun x ↦ carriedVorticity ω₀ θ₀ ω (-T) T x t) α
      (vorticityBound k α R₁ N Nlow T) (vorticityHolder k α R₁ N Nlow T)
      (vorticityTopConst k α R₁ N Nlow T +
        vorticityTopSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|)
      (vorticityTopHolderConst k α R₁ N Nlow T +
        vorticityTopHolderSlope k α R₁ N Nlow T * |∫ r in t..0, P (|r|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hc := (hasHolderBounds_amplitudeOf h hd hα hα1 hk hT ht).comp
    (h.hasHolderBounds_flowOn hα hα1 hk h0 ht) (h.mapsTo_flowOn hα hα1 h0 ht)
    (IsTopBoundedHistory.flowBound_nonneg (by omega))
    (fun z z' hz hz' ↦ h.norm_flowOn_sub_le hα hα1 (by omega) h0 ht hz hz') hk hα.le
  rw [compTopBound_outer_affine, compTopHolder_outer_affine] at hc
  exact hc.congr fun x hx ↦ carriedVorticity_eq h hd hα hα1 (by omega) ht hx

/-- The carried vorticity is bounded by `vorticityValueBound` on the closed half-plane. -/
theorem abs_carriedVorticity_le_vorticityValueBound (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity ω₀ θ₀ ω (-T) T x t| ≤ vorticityValueBound k α R₁ N Nlow T := by
  rw [carriedVorticity_eq h hd hα hα1 (by omega) ht hx]
  exact abs_amplitudeOf_le h hd hα hα1 hk ht (h.mapsTo_flowOn hα hα1 (zero_mem_Icc_neg_of_mem ht)
      ht hx)

/-- `|∫ₜ⁰ P(|r|) dr| ≤ ∫₀ᵀ P` for `t ∈ [-T, T]`. -/
theorem abs_integral_le_integral (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) {t : ℝ}
    (ht : t ∈ Icc (-T) T) : |∫ r in t..0, P (|r|)| ≤ ∫ r in (0)..T, P r := by
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  rw [abs_integral_eq h ht]
  have hP : ∀ r ∈ uIcc 0 T, 0 ≤ P r := fun r hr ↦ h.nonneg r (by rwa [uIcc_of_le hT] at hr)
  have hi : IntervalIntegrable P volume 0 T :=
    (h.continuousOn.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hm := abs_integral_le_of_mem_uIcc hi hP (r := |t|)
    (by rw [uIcc_of_le hT]; exact IsTopBoundedHistory.abs_mem_Icc ht)
  have h1 : 0 ≤ ∫ r in (0)..(|t|), P r := intervalIntegral.integral_nonneg (abs_nonneg t)
    fun r hr ↦ h.nonneg r ⟨hr.1, hr.2.trans (IsTopBoundedHistory.abs_mem_Icc ht).2⟩
  rwa [abs_of_nonneg h1, abs_of_nonneg (intervalIntegral.integral_nonneg hT fun r hr ↦
    h.nonneg r hr)] at hm

/-- An affine function `a + b Ψ(t)` of `Ψ(t) = |∫ₜ⁰ P(|r|) dr|` is at most `|a| + |b| ∫₀ᵀ P` on
`[-T, T]`. -/
private theorem affine_le_abs_affine (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (a b : ℝ) {t : ℝ}
    (ht : t ∈ Icc (-T) T) : a + b * |∫ r in t..0, P (|r|)| ≤ |a| + |b| * ∫ r in (0)..T, P r :=
  add_le_add (le_abs_self a) ((mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (abs_integral_le_integral h ht) (abs_nonneg _)))

/-- **The level-`k` bounds of the carried vorticity**, with `Φ(t) = ∫₀^{|t|} P`: at a time
`t ∈ [-T, T]` it has `C^{k,α}` bounds on the closed half-plane with the constants
`vorticityBound`, `vorticityHolder` below the top order and top-order constants
`vorticityTopConst + vorticityTopSlope Φ(t)` and
`vorticityTopHolderConst + vorticityTopHolderSlope Φ(t)`, all of them functions of
`k, α, R₁, N, Nlow, T` only. -/
theorem carriedVorticity_bounds (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k (fun x ↦ carriedVorticity ω₀ θ₀ ω (-T) T x t) α
      (vorticityBound k α R₁ N Nlow T) (vorticityHolder k α R₁ N Nlow T)
      (vorticityTopConst k α R₁ N Nlow T +
        vorticityTopSlope k α R₁ N Nlow T * ∫ r in (0)..(|t|), P r)
      (vorticityTopHolderConst k α R₁ N Nlow T +
        vorticityTopHolderSlope k α R₁ N Nlow T * ∫ r in (0)..(|t|), P r) := by
  have hb := hasHolderBounds_carriedVorticity h hd hα hα1 hk hT ht
  rwa [abs_integral_eq h ht] at hb

/-- **The level-`k` bounds of the carried temperature**, with `Φ(t) = ∫₀^{|t|} P`: at a time
`t ∈ [-T, T]` it has `C^{k+1,α}` bounds on the closed half-plane with the constants
`temperatureBound`, `temperatureHolder` below the top order and top-order constants
`temperatureTopConst + temperatureTopSlope Φ(t)` and
`temperatureTopHolderConst + temperatureTopHolderSlope Φ(t)`. -/
theorem carriedTemperature_bounds (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (fun x ↦ carriedTemperature θ₀ ω (-T) T x t) α
      (temperatureBound k α R₁ N Nlow T) (temperatureHolder k α R₁ N Nlow T)
      (temperatureTopConst k α R₁ N Nlow T +
        temperatureTopSlope k α R₁ N Nlow T * ∫ r in (0)..(|t|), P r)
      (temperatureTopHolderConst k α R₁ N Nlow T +
        temperatureTopHolderSlope k α R₁ N Nlow T * ∫ r in (0)..(|t|), P r) := by
  have hb := hasHolderBounds_carriedTemperature h hd hα hα1 hk ht
  rwa [abs_integral_eq h ht] at hb

/-- **Continuity in time of the derivatives of the carried temperature**, uniformly on the closed
half-plane, for every order at most `k + 1`. -/
theorem uniform_carriedTemperature (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) (hT : 0 ≤ T)
    (hR₁ : 0 ≤ R₁) : ∀ j ≤ k + 1, ∀ t ∈ Icc (-T) T, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (-T) T,
      |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
        ‖iteratedFDerivWithin ℝ j (fun x ↦ carriedTemperature θ₀ ω (-T) T x s) H̄ y -
          iteratedFDerivWithin ℝ j (fun x ↦ carriedTemperature θ₀ ω (-T) T x t) H̄ y‖ ≤ ε := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hω1 := h.history.toIsC1VorticityHistory (by omega) hα.le hα1.le
  have hb := IsC1VorticityHistory.isBoundedFlowOn hω1 hα hα1 hR₁ (by linarith)
  have hv := (IsC1VorticityHistory.isC2FieldOn_historyField hω1 hα hα1).toIsC1FieldOn
  have hN := hd.nonneg
  have hθ := hd.hasHolderBounds_temperature hα.le hα1.le
  set Φ := ∫ r in (0)..T, P r
  have hΦ : 0 ≤ Φ := intervalIntegral.integral_nonneg hT fun r hr ↦ h.nonneg r hr
  have h0b := hasHolderBounds_carriedTemperature h hd hα hα1 hk h0
  refine uniform_iteratedFDerivWithin_of_holder (f := fun s x ↦ carriedTemperature θ₀ ω (-T) T x s)
    (M := temperatureHolder k α R₁ N Nlow T + (|temperatureTopHolderConst k α R₁ N Nlow T| +
      |temperatureTopHolderSlope k α R₁ N Nlow T| * Φ)) hα
    (by have := h0b.holder_nonneg (by omega); positivity)
    (fun s hs ↦ (hasHolderBounds_carriedTemperature h hd hα hα1 hk hs).contDiffOn)
    (fun s hs j hj hjk y z hy hz ↦ ?_) (fun t ht ε hε ↦ ?_)
  · have hbs := hasHolderBounds_carriedTemperature h hd hα hα1 hk hs
    have hd0 : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hab : 0 ≤ |temperatureTopHolderConst k α R₁ N Nlow T| +
        |temperatureTopHolderSlope k α R₁ N Nlow T| * Φ := by positivity
    rcases hjk.lt_or_eq with hjk' | rfl
    · exact (hbs.holder j hj hjk' y z hy hz).trans (mul_le_mul_of_nonneg_right (by linarith) hd0)
    · refine (hbs.holder_top y z hy hz).trans (mul_le_mul_of_nonneg_right ?_ hd0)
      have : _ ≤ _ + _ * Φ := affine_le_abs_affine h (temperatureTopHolderConst k α R₁ N Nlow T)
        (temperatureTopHolderSlope k α R₁ N Nlow T) hs
      linarith [h0b.holder_nonneg (by omega)]
  · have hL := hb.zero_le_L h0
    have hV := hb.zero_le_V h0
    set c := N * Real.exp (katoBound α R₁ B (2 * B) * (T - -T)) * ((1 + R₁ ^ 2) * B)
    have hc : 0 ≤ c := by positivity
    refine ⟨ε / (c + 1), by positivity, fun s hs hst y hy ↦ ?_⟩
    have hYs := hb.flowOn_mem h0 hs hy
    have hYt := hb.flowOn_mem h0 ht hy
    simp only [carriedTemperature]
    rw [dataTemperature_of_nonneg θ₀ hYs, dataTemperature_of_nonneg θ₀ hYt]
    refine (hθ.norm_sub_le (by omega) hYs hYt).trans ?_
    have hl := hb.norm_label_sub_le hv h0 hs ht hy
    calc N * ‖flowOn (historyField ω) (-T) T 0 s y - flowOn (historyField ω) (-T) T 0 t y‖
        ≤ N * (Real.exp (katoBound α R₁ B (2 * B) * (T - -T)) * ((1 + R₁ ^ 2) * B * |s - t|)) :=
          mul_le_mul_of_nonneg_left hl hN
      _ = c * |s - t| := by simp only [c]; ring
      _ ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hst.le hc
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          linarith

/-- **The carried history is again a `C^{k,α}` history.** For `k ≥ 2` and `0 < α < 1`, the
vorticity carried by the flow of a `C^{k,α}` history with a top-order majorant is a `C^{k,α}`
history on `[-T, T]`, supported on the closed half-plane in the disc of radius
`R + (1 + R₁²) B T`, with the bound `carriedBound` built from `Φ = ∫₀ᵀ P`. -/
theorem isCkVorticityHistory_carriedHistory (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) (hT : 0 ≤ T)
    (hR₁ : 0 ≤ R₁) :
    IsCkVorticityHistory k (carriedHistory ω₀ θ₀ (-T) T ω) (-T) T α (R + (1 + R₁ ^ 2) * B * T)
      (carriedBound k α R₁ N Nlow T (∫ r in (0)..T, P r)) := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hω1 := h.history.toIsC1VorticityHistory (by omega) hα.le hα1.le
  have hb := IsC1VorticityHistory.isBoundedFlowOn hω1 hα hα1 hR₁ (by linarith)
  have hv2 := IsC1VorticityHistory.isC2FieldOn_historyField hω1 hα hα1
  have hd1 := hd.toIsHolderData (by omega) hα.le hα1.le
  set Φ := ∫ r in (0)..T, P r
  have hΦ : 0 ≤ Φ := intervalIntegral.integral_nonneg hT fun r hr ↦ h.nonneg r hr
  have hb0 := hasHolderBounds_carriedVorticity h hd hα hα1 hk hT h0
  have hVB : 0 ≤ vorticityValueBound k α R₁ N Nlow T :=
    (abs_nonneg _).trans (abs_carriedVorticity_le_vorticityValueBound h hd hα hα1 hk h0
      (x := 0) (by simp))
  have hvB : 0 ≤ vorticityBound k α R₁ N Nlow T := hb0.bound_nonneg hk
  have hvH : 0 ≤ vorticityHolder k α R₁ N Nlow T := hb0.holder_nonneg hk
  have hA1 : 0 ≤ |vorticityTopConst k α R₁ N Nlow T| +
      |vorticityTopSlope k α R₁ N Nlow T| * Φ := by positivity
  have hA2 : 0 ≤ |vorticityTopHolderConst k α R₁ N Nlow T| +
      |vorticityTopHolderSlope k α R₁ N Nlow T| * Φ := by positivity
  have haffine (a b : ℝ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
      a + b * |∫ r in t..0, P (|r|)| ≤ |a| + |b| * Φ :=
    affine_le_abs_affine h a b ht
  refine ⟨fun t ht ↦ (hasHolderBounds_carriedVorticity h hd hα hα1 hk hT ht).contDiffOn,
    fun t ht y hy hyR ↦ (hb.carried_eq_zero h0 hd1 ht
      (abs_le.mpr ⟨ht.1, ht.2⟩) hy hyR).1, fun t ht j hj y hy ↦ ?_, fun t ht y z hy hz ↦ ?_,
    ?_⟩
  · have hbt := hasHolderBounds_carriedVorticity h hd hα hα1 hk hT ht
    change ‖iteratedFDerivWithin ℝ j (fun x ↦ carriedVorticity ω₀ θ₀ ω (-T) T x t) H̄ y‖ ≤ _
    simp only [carriedBound]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      linarith [abs_carriedVorticity_le_vorticityValueBound h hd hα hα1 hk ht hy]
    rcases hj.lt_or_eq with hjk | hjk
    · linarith [hbt.norm_le j hj0 hjk y hy]
    · rw [hjk]
      linarith [(hbt.norm_top_le y hy).trans (haffine _ _ ht)]
  · have hbt := hasHolderBounds_carriedVorticity h hd hα hα1 hk hT ht
    refine (hbt.holder_top y z hy hz).trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (norm_nonneg _) α))
    simp only [carriedBound]
    linarith [haffine (vorticityTopHolderConst k α R₁ N Nlow T)
      (vorticityTopHolderSlope k α R₁ N Nlow T) ht]
  · refine uniform_iteratedFDerivWithin_of_holder (f := carriedHistory ω₀ θ₀ (-T) T ω)
      (M := vorticityHolder k α R₁ N Nlow T + (|vorticityTopHolderConst k α R₁ N Nlow T| +
        |vorticityTopHolderSlope k α R₁ N Nlow T| * Φ)) hα (by positivity)
      (fun s hs ↦ (hasHolderBounds_carriedVorticity h hd hα hα1 hk hT hs).contDiffOn)
      (fun s hs j hj hjk y z hy hz ↦ ?_) (fun t ht ε hε ↦ ?_)
    · have hbs := hasHolderBounds_carriedVorticity h hd hα hα1 hk hT hs
      have hd0 : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      rcases hjk.lt_or_eq with hjk' | hjk'
      · exact (hbs.holder j hj hjk' y z hy hz).trans
          (mul_le_mul_of_nonneg_right (by linarith) hd0)
      · rw [hjk']
        refine (hbs.holder_top y z hy hz).trans (mul_le_mul_of_nonneg_right ?_ hd0)
        linarith [haffine (vorticityTopHolderConst k α R₁ N Nlow T)
          (vorticityTopHolderSlope k α R₁ N Nlow T) hs]
    · obtain ⟨δ, hδ, hδε⟩ := hb.exists_abs_carriedVorticity_sub_le hv2 h0 hd1 ht hε
      exact ⟨δ, hδ, fun s hs hst y hy ↦ by
        rw [Real.norm_eq_abs]; exact hδε s hs hst y hy⟩

end Amplitude

end Boussinesq.HalfPlane
