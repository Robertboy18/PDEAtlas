/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.CarriedHigherForcing
public import PDE.Fluid.HalfPlaneSystem.Iteration
public import PDE.Analysis.Calculus.SmoothFamilyIntegral
public import PDE.Analysis.ODE.Flow.VariationInverse
public import PDE.Analysis.Calculus.HolderUniform
import PDE.Analysis.Calculus.IntegralMajorant
import PDE.Analysis.ODE.Flow.Basic

/-!
# The amplitude and the carried vorticity at level `k`

The iteration map of the local existence proof sends a vorticity history to the vorticity that its
velocity field carries. This module shows that when the data and the history have `k ≥ 2`
derivatives with a Hölder condition, the carried vorticity has them too, with a top-order bound
affine in the time integral of the top-order bound of the history. This is what lets the regularity
of a solution be propagated by a linear Grönwall inequality.

With the notation of `CarriedHigherForcing.lean`, the weighted forcing in label form of a field `v`
with level-`k` bounds and of the extension `θ̃₀ = weightedReflectionFun 1 (k + 1) θ₀` of the
temperature datum, `forcingOf k v T κ θ₀ y r = κ(X_r y) Dθ̃₀(y) (W e₀)`, `W` the inverse first
variation along the particle of label `y`, is a smooth family of order `k` in time
(`IsTopBoundedField.isSmoothFamilyOn_forcingOf`), and on the closed half-plane it is
`(κ ∂₀(θ₀ ∘ Y_r)) ∘ X_r` (`IsTopBoundedField.forcingOf_eq`). The amplitude
`amplitudeOf k v T κ ω₀ θ₀ y t = ω̃₀(y) + ∫₀ᵗ forcingOf k v T κ θ₀ y r dr`,
`ω̃₀ = weightedReflectionFun 1 k ω₀`, is `C^k` in the label and has `C^{k,α}` bounds on `H̄` with
top-order constants affine in `Ψ(t) = |∫ₜ⁰ P(|r|) dr|`: the derivatives in the label pass under the
time integral, and the bounds of the forcing are integrated over a time of length at most `T`.

For a velocity law `U` and a `C^{k,α}` history `ω` with a top-order majorant `P`, the carried
vorticity of the iteration is the amplitude of the extensions of order `k + 1` of the fields of the
law at the label (`carriedVorticity_eq`), so its bounds are those of a composition of the amplitude
with the label map. The constants are compositions of the constants of the chain rule and are not
simplified.

## Main results

With `Φ(t) = ∫₀^{|t|} P`, `c = lawConst C k α · Nlow`, `c' = lawConst C k α` and constants depending
only on `Bκ, k, α, c, c', N, T`:

* `carriedVorticity_holderBounds`: the carried vorticity at time `t` has `C^{k,α}` bounds on `H̄`
  with `carriedVorticityBound`, `vorticityHolder` below the top order and the top-order constants
  `vorticityTopConst + vorticityTopSlope Φ(t)`,
  `vorticityTopHolderConst + vorticityTopHolderSlope Φ(t)`.
* `carriedTemperature_holderBounds`: the carried temperature has `C^{k+1,α}` bounds of the same
  form.
* `uniform_carriedTemperature`: the derivatives of order at most `k + 1` of the carried temperature
  are continuous in time uniformly on `H̄`.
* `isCkVorticityHistory_carriedHistory`: the carried history is a `C^{k,α}` history on `[-T, T]`,
  supported in the disc of radius `R + C 0 0 B T`, with the bound `carriedBound`.
* `forcingOf`, `amplitudeOf`, `IsTopBoundedField.hasHolderBounds_amplitudeOf`,
  `IsTopBoundedField.abs_amplitudeOf_le`: the forcing and the amplitude at level `k` and the bounds
  of the amplitude, for every field with level-`k` bounds.
* `carriedVorticity_eq`: on `H̄` the carried vorticity is the amplitude at the label.

`IterationHigher.lean` uses the four theorems on the carried fields: with the affine bounds, a
solution that is a fixed point of the iteration map has a top-order bound that satisfies a linear
integral inequality. The level `k = 1` is the class of the local existence theorem
(`Iteration.lean`).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open IncompressibleFlow PDE.Analysis PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane
open SobolevSpace.GraphSpace.HigherOrderReflection
open scoped Interval

open PDE.Analysis.ODE (zero_mem_Icc_neg_of_mem)
namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The weighted forcing in label form of the field `v` on the times `[-T, T]`, with the forcing
coefficient `κ` and the extension of order `k + 1` of the temperature datum. -/
def forcingOf (k : ℕ) (v : ℝ → ℝ^2 → ℝ^2) (T : ℝ) (κ θ₀ : ℝ^2 → ℝ) : ℝ^2 → ℝ → ℝ :=
  weightedForcing v (fun r y ↦ fderiv ℝ (v r) y) (-T) T κ (weightedReflectionFun 1 (k + 1) θ₀)
    (EuclideanSpace.single 0 1)

/-- The amplitude at level `k`: `ω̃₀(y) + ∫₀ᵗ forcingOf k v T κ θ₀ y r dr` with the extension of
order `k` of the vorticity datum. -/
def amplitudeOf (k : ℕ) (v : ℝ → ℝ^2 → ℝ^2) (T : ℝ) (κ ω₀ θ₀ : ℝ^2 → ℝ) : ℝ^2 → ℝ → ℝ :=
  forcedAmplitude (weightedReflectionFun 1 k ω₀) (forcingOf k v T κ θ₀)

section Constants

variable (Bκ : ℕ → ℝ) (k : ℕ) (α c c' N T : ℝ)

/-- The bound of the derivatives of orders `1 ≤ j < k` of the amplitude. -/
def amplitudeBound : ℝ :=
  N + T * forcingBound Bκ k c N T

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the amplitude. -/
def amplitudeHolder : ℝ :=
  2 * N + T * forcingHolder Bκ k α c N T

/-- The constant term of the bound of the derivative of order `k` of the amplitude. -/
def amplitudeTopConst : ℝ :=
  N + T * forcingTopConst Bκ k c N T

/-- The coefficient of `Ψ(t)` in the bound of the derivative of order `k` of the amplitude. -/
def amplitudeTopSlope : ℝ :=
  T * forcingTopSlope Bκ k c c' N T

/-- The constant term of the Hölder constant of the derivative of order `k` of the amplitude. -/
def amplitudeTopHolderConst : ℝ :=
  N + T * forcingTopHolderConst Bκ k α c N T

/-- The coefficient of `Ψ(t)` in the Hölder constant of the derivative of order `k` of the
amplitude. -/
def amplitudeTopHolderSlope : ℝ :=
  T * forcingTopHolderSlope Bκ k α c c' N T

/-- The bound of the derivatives of orders `1 ≤ j < k` of the carried vorticity. -/
def carriedVorticityBound : ℝ :=
  compBound k (amplitudeBound Bκ k c N T) (flowBound k c T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the carried vorticity. -/
def vorticityHolder : ℝ :=
  compHolder k α (amplitudeBound Bκ k c N T) (amplitudeHolder Bκ k α c N T) (flowBound k c T)
    (flowHolder k α c T) (flowBound k c T)

/-- The constant term of the bound of the derivative of order `k` of the carried vorticity. -/
def vorticityTopConst : ℝ :=
  compTopBound k (amplitudeBound Bκ k c N T) (amplitudeTopConst Bκ k c N T) (flowBound k c T)
    (flowBound k c T)

/-- The coefficient of `Ψ(t)` in the bound of the derivative of order `k` of the carried
vorticity. -/
def vorticityTopSlope : ℝ :=
  amplitudeTopSlope Bκ k c c' N T * flowBound k c T ^ k

/-- The constant term of the Hölder constant of the derivative of order `k` of the carried
vorticity. -/
def vorticityTopHolderConst : ℝ :=
  compTopHolder k α (amplitudeBound Bκ k c N T) (amplitudeHolder Bκ k α c N T)
    (amplitudeTopConst Bκ k c N T) (amplitudeTopHolderConst Bκ k α c N T) (flowBound k c T)
    (flowHolder k α c T) (flowBound k c T) (flowHolder k α c T) (flowBound k c T)

/-- The coefficient of `Ψ(t)` in the Hölder constant of the derivative of order `k` of the
carried vorticity. -/
def vorticityTopHolderSlope : ℝ :=
  amplitudeTopSlope Bκ k c c' N T * k * flowBound k c T ^ (k - 1) * flowHolder k α c T +
    amplitudeTopHolderSlope Bκ k α c c' N T * flowBound k c T ^ α * flowBound k c T ^ k

/-- The bound of the values of the carried vorticity. -/
def vorticityValueBound : ℝ :=
  N + T * (Bκ 0 * temperatureBound k c N T)

/-- A common bound of the derivatives of order at most `k` and of the Hölder constant of the
derivative of order `k` of the carried vorticity at all times of `[-T, T]`, with
`Φ = ∫₀ᵀ P`. -/
def carriedBound (Φ : ℝ) : ℝ :=
  vorticityValueBound Bκ k c N T + carriedVorticityBound Bκ k c N T +
    (|vorticityTopConst Bκ k c N T| + |vorticityTopSlope Bκ k c c' N T| * Φ) +
    (|vorticityTopHolderConst Bκ k α c N T| + |vorticityTopHolderSlope Bκ k α c c' N T| * Φ)

end Constants

/-! ### The amplitude of a field with level-`k` bounds -/

namespace IsTopBoundedField

variable {k : ℕ} {v : ℝ → ℝ^2 → ℝ^2} {T α c c' : ℝ} {P : ℝ → ℝ}
variable {κ ω₀ θ₀ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ} {R N : ℝ}

/-- **The weighted forcing at level `k` is a smooth family of order `k`** on `[-T, T]`. -/
theorem isSmoothFamilyOn_forcingOf (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hT : 0 ≤ T) :
    IsSmoothFamilyOn k (fun r y ↦ forcingOf k v T κ θ₀ y r) (Icc (-T) T) := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hW := hv.isSmoothFamilyOn_variationOn_flowOn h.smooth h0
  have hθ : ContDiff ℝ (k + 1 : ℕ) (weightedReflectionFun 1 (k + 1) θ₀) :=
    contDiff_weightedReflectionFun 1 (by omega) hd.temperature_contDiffOn
  have hDθ : IsSmoothFamilyOn k (fun (_ : ℝ) y ↦ fderiv ℝ (weightedReflectionFun 1 (k + 1) θ₀) y)
      (Icc (-T) T) :=
    isSmoothFamilyOn_const (hθ.fderiv_right (by push_cast; exact le_rfl))
  have hWe := hW.clm_comp (ContinuousLinearMap.apply ℝ (ℝ^2) (EuclideanSpace.single 0 1))
  have hlab := hDθ.bilinear (ContinuousLinearMap.id ℝ (ℝ^2 →L[ℝ] ℝ)) hWe
  have hX := hv.isSmoothFamilyOn_flowOn (h.smooth.mono (Nat.le_succ k)) h0
  have hκX := (isSmoothFamilyOn_const (I := Icc (-T) T)
    (hκ.contDiff.of_le (by exact_mod_cast le_top) : ContDiff ℝ k κ)).comp hX
  refine (hκX.bilinear (ContinuousLinearMap.mul ℝ ℝ) hlab).congr fun r _ ↦ ?_
  funext y
  rfl

/-- On the closed half-plane the weighted forcing at level `k` is `(κ ∂₀(θ₀ ∘ Y_r)) ∘ X_r`. -/
theorem forcingOf_eq (h : IsTopBoundedField k v T α c c' P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    {r : ℝ} (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    forcingOf k v T κ θ₀ y r =
      ((fun z ↦ κ z * fderivWithin ℝ (θ₀ ∘ flowOn v (-T) T 0 r) H̄ z
        (EuclideanSpace.single 0 1)) ∘ flowOn v (-T) T r 0) y := by
  have hθ : DifferentiableOn ℝ θ₀ H̄ :=
    hd.temperature_contDiffOn.differentiableOn (by exact_mod_cast (show k + 1 ≠ 0 by omega))
  unfold forcingOf weightedForcing labelForcing
  rw [fderiv_weightedReflectionFun_of_nonneg 1 (k := k + 1) (by omega)
    hd.temperature_contDiffOn hy, h.fderivWithin_apply_variationOn_eq hθ hr hy]
  rfl

/-- The amplitude at level `k` is `C^k` in the label. -/
theorem contDiff_amplitudeOf (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hk : 1 ≤ k)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ContDiff ℝ k fun y ↦ amplitudeOf k v T κ ω₀ θ₀ y t := by
  unfold amplitudeOf forcedAmplitude
  exact (contDiff_weightedReflectionFun 1 hk hd.vorticity_contDiffOn).add
    ((h.isSmoothFamilyOn_forcingOf hd hκ hT).contDiff_integral (zero_mem_Icc_neg_of_mem ht) ht)

/-- The derivatives of order `j ≤ k` of the amplitude are those of `ω̃₀` plus the integrals of
those of the forcing. -/
theorem iteratedFDeriv_amplitudeOf (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hk : 1 ≤ k)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (-T) T) {j : ℕ} (hj : j ≤ k) (y : ℝ^2) :
    iteratedFDeriv ℝ j (fun y ↦ amplitudeOf k v T κ ω₀ θ₀ y t) y =
      iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) y +
        ∫ r in (0)..t, iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) y := by
  have hG := h.isSmoothFamilyOn_forcingOf hd hκ hT
  have h1 : ContDiff ℝ j (weightedReflectionFun 1 k ω₀) :=
    (contDiff_weightedReflectionFun 1 hk hd.vorticity_contDiffOn).of_le (by exact_mod_cast hj)
  have h2 : ContDiff ℝ j fun y ↦ ∫ r in (0)..t, forcingOf k v T κ θ₀ y r :=
    (hG.contDiff_integral (zero_mem_Icc_neg_of_mem ht) ht).of_le (by exact_mod_cast hj)
  have e : (fun y ↦ amplitudeOf k v T κ ω₀ θ₀ y t) =
      weightedReflectionFun 1 k ω₀ + fun y ↦ ∫ r in (0)..t, forcingOf k v T κ θ₀ y r := by
    funext y; unfold amplitudeOf forcedAmplitude; rfl
  rw [e, iteratedFDeriv_add_apply h1.contDiffAt h2.contDiffAt,
    iteratedFDeriv_integral_of_isSmoothFamilyOn hG (zero_mem_Icc_neg_of_mem ht) ht hj y]

/-- The coefficients of `Ψ` in the top-order constants of the forcing are nonnegative. -/
theorem forcingSlopes_nonneg (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hk : 1 ≤ k)
    (hT : 0 ≤ T) :
    0 ≤ forcingTopSlope Bκ k c c' N T ∧ 0 ≤ forcingTopHolderSlope Bκ k α c c' N T := by
  have hN := hd.nonneg
  have hc0 := h.const_nonneg hT
  have hc' := h.slope_nonneg
  have hF0 : 0 ≤ flowBound k c T := flowBound_nonneg c T hk
  have hτ0 : 0 ≤ T - -T := by linarith
  have hHf : 0 ≤ flowHolder k α c T := flowHolder_nonneg hc0 hF0 hτ0
  have hC₃ := flowTopSlope_nonneg (k := k) (c := c) (T := T) hc' hF0
  have hC₄ := flowTopHolderSlope_nonneg (k := k) (α := α) (c := c) (T := T) hc0 hc' hF0 hτ0
  have hW : 0 ≤ coefficientBound Bκ k := Finset.sum_nonneg fun i _ ↦ hκ.bound_nonneg i
  have hTS : 0 ≤ temperatureTopSlope k c c' N T := by unfold temperatureTopSlope; positivity
  have hTHS : 0 ≤ temperatureTopHolderSlope k α c c' N T := by
    unfold temperatureTopHolderSlope; positivity
  have hES : 0 ≤ eulerForcingTopSlope Bκ k c c' N T := by
    unfold eulerForcingTopSlope; positivity
  have hEHS : 0 ≤ eulerForcingTopHolderSlope Bκ k α c c' N T := by
    unfold eulerForcingTopHolderSlope; positivity
  exact ⟨by unfold forcingTopSlope; positivity, by unfold forcingTopHolderSlope; positivity⟩

/-- Between `0` and `t` the integral `|∫₀ʳ P(|r'|) dr'|` is at most its value at `t`. -/
theorem abs_integral_le_of_mem (h : IsTopBoundedField k v T α c c' P) {t r : ℝ}
    (ht : t ∈ Icc (-T) T) (hr : r ∈ uIcc 0 t) :
    |∫ r' in r..0, P (|r'|)| ≤ |∫ r' in t..0, P (|r'|)| := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  rw [intervalIntegral.integral_symm 0 r, abs_neg, intervalIntegral.integral_symm 0 t, abs_neg]
  exact abs_integral_le_of_mem_uIcc (h.intervalIntegrable_abs ht h0)
    (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc h0 ht hr)) hr

/-- `|∫ₜ⁰ P(|r|) dr| = ∫₀^{|t|} P`. -/
theorem abs_integral_eq (h : IsTopBoundedField k v T α c c' P) {t : ℝ}
    (ht : t ∈ Icc (-T) T) : |∫ r in t..0, P (|r|)| = ∫ r in (0)..(|t|), P r := by
  rw [intervalIntegral.integral_symm, abs_neg]
  exact abs_integral_comp_abs fun r hr ↦ h.nonneg r ⟨hr.1, hr.2.trans
    (IsTopBoundedHistory.abs_mem_Icc ht).2⟩

/-- `|∫ₜ⁰ P(|r|) dr| ≤ ∫₀ᵀ P` for `t ∈ [-T, T]`. -/
theorem abs_integral_le_integral (h : IsTopBoundedField k v T α c c' P) {t : ℝ}
    (ht : t ∈ Icc (-T) T) : |∫ r in t..0, P (|r|)| ≤ ∫ r in (0)..T, P r := by
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  rw [h.abs_integral_eq ht]
  have hP : ∀ r ∈ uIcc 0 T, 0 ≤ P r := fun r hr ↦ h.nonneg r (by rwa [uIcc_of_le hT] at hr)
  have hi : IntervalIntegrable P volume 0 T :=
    (h.continuousOn.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hm := abs_integral_le_of_mem_uIcc hi hP (r := |t|)
    (by rw [uIcc_of_le hT]; exact IsTopBoundedHistory.abs_mem_Icc ht)
  have h1 : 0 ≤ ∫ r in (0)..(|t|), P r := intervalIntegral.integral_nonneg (abs_nonneg t)
    fun r hr ↦ h.nonneg r ⟨hr.1, hr.2.trans (IsTopBoundedHistory.abs_mem_Icc ht).2⟩
  rwa [abs_of_nonneg h1, abs_of_nonneg (intervalIntegral.integral_nonneg hT fun r hr ↦
    h.nonneg r hr)] at hm

/-- On the closed half-plane the derivatives of order `j ≤ k` of the forcing at level `k` are
those of `(κ ∂₀(θ₀ ∘ Y_r)) ∘ X_r` within the closed half-plane. -/
theorem iteratedFDeriv_forcingOf_eq (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hT : 0 ≤ T) {r : ℝ}
    (hr : r ∈ Icc (-T) T) {j : ℕ} (hj : j ≤ k) {y : ℝ^2} (hy : 0 ≤ y 1) :
    iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) y =
      iteratedFDerivWithin ℝ j ((fun z ↦ κ z * fderivWithin ℝ (θ₀ ∘ flowOn v (-T) T 0 r) H̄ z
        (EuclideanSpace.single 0 1)) ∘ flowOn v (-T) T r 0) H̄ y := by
  rw [← iteratedFDerivWithin_closedUpper_eq
    ((h.isSmoothFamilyOn_forcingOf hd hκ hT).contDiff hr) hj hy]
  have heq : EqOn (fun y ↦ forcingOf k v T κ θ₀ y r) ((fun z ↦ κ z * fderivWithin ℝ
      (θ₀ ∘ flowOn v (-T) T 0 r) H̄ z (EuclideanSpace.single 0 1)) ∘ flowOn v (-T) T r 0) H̄ :=
    fun z hz ↦ h.forcingOf_eq hd hr hz
  exact iteratedFDerivWithin_congr heq hy j

/-- **The `C^{k,α}` bounds of the amplitude at level `k`** at a time `t ∈ [-T, T]`, with
top-order constants affine in `Ψ(t) = |∫ₜ⁰ P(|r|) dr|`. The carried vorticity is this amplitude
at the label. Proof: a derivative of the amplitude in the label is the derivative of the
extended datum plus the time integral of the derivative of the forcing; the bounds of the
forcing are integrated over a time of length at most `T`, and `Ψ` is monotone in `|t|`. -/
theorem hasHolderBounds_amplitudeOf (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k (fun y ↦ amplitudeOf k v T κ ω₀ θ₀ y t) α
      (amplitudeBound Bκ k c N T) (amplitudeHolder Bκ k α c N T)
      (amplitudeTopConst Bκ k c N T + amplitudeTopSlope Bκ k c c' N T * |∫ r in t..0, P (|r|)|)
      (amplitudeTopHolderConst Bκ k α c N T +
        amplitudeTopHolderSlope Bκ k α c c' N T * |∫ r in t..0, P (|r|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hG := h.isSmoothFamilyOn_forcingOf hd hκ hT
  have hω₀ := hd.vorticity_contDiffOn
  have htT : |t - 0| ≤ T := by rw [sub_zero]; exact abs_le.mpr ⟨ht.1, ht.2⟩
  have hFt := h.hasHolderBounds_forcing hd hκ hα hα1 hk ht
  obtain ⟨hfTS, hfTHS⟩ := h.forcingSlopes_nonneg hd hκ (by omega) hT
  have hr' {r : ℝ} (hr : r ∈ Ι 0 t) : r ∈ Icc (-T) T := uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)
  have hΨ {r : ℝ} (hr : r ∈ Ι 0 t) : |∫ r' in r..0, P (|r'|)| ≤ |∫ r' in t..0, P (|r'|)| :=
    h.abs_integral_le_of_mem ht (uIoc_subset_uIcc hr)
  have hint (j : ℕ) (hj : j ≤ k) (z : ℝ^2) : IntervalIntegrable
      (fun r ↦ iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z) volume 0 t :=
    ((continuousOn_iteratedFDeriv_slice hG hj z).mono (uIcc_subset_Icc h0 ht)).intervalIntegrable
  have hint_le {j : ℕ} {C : ℝ} (hC : 0 ≤ C)
      {f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ ℝ^2) ℝ}
      (hf : ∀ r ∈ Ι 0 t, ‖f r‖ ≤ C) : ‖∫ r in (0)..t, f r‖ ≤ T * C :=
    (intervalIntegral.norm_integral_le_of_norm_le_const hf).trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right htT hC)
  have hdiff {j : ℕ} (hj : j ≤ k) (z z' : ℝ^2) :
      (iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z +
          ∫ r in (0)..t, iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z) -
        (iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z' +
          ∫ r in (0)..t, iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z') =
      (iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z -
          iteratedFDeriv ℝ j (weightedReflectionFun 1 k ω₀) z') +
        ∫ r in (0)..t, (iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z -
          iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z') := by
    rw [intervalIntegral.integral_sub (hint j hj z) (hint j hj z')]
    abel
  refine HasHolderBounds.of_contDiff (h.contDiff_amplitudeOf hd hκ (by omega) hT ht)
    (fun j hj hjk z hz ↦ ?_) (fun j hj hjk z z' hz hz' ↦ ?_) (fun z hz ↦ ?_)
    (fun z z' hz hz' ↦ ?_)
  -- The size of the derivatives of orders `1 ≤ j < k`: the datum plus the integral of the
  -- bound of the forcing.
  · rw [h.iteratedFDeriv_amplitudeOf hd hκ (by omega) hT ht hjk.le,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ hjk.le hz]
    refine (norm_add_le _ _).trans (add_le_add (hd.norm_vorticity_le j hjk.le z hz)
      (hint_le (hFt.bound_nonneg hk)
        (f := fun r ↦ iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z) fun r hr ↦ ?_))
    rw [h.iteratedFDeriv_forcingOf_eq hd hκ hT (hr' hr) hjk.le hz]
    exact (h.hasHolderBounds_forcing hd hκ hα hα1 hk (hr' hr)).norm_le j hj hjk z hz
  -- Their Hölder constants.
  · rw [h.iteratedFDeriv_amplitudeOf hd hκ (by omega) hT ht hjk.le,
      h.iteratedFDeriv_amplitudeOf hd hκ (by omega) hT ht hjk.le, hdiff hjk.le,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ hjk.le hz,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ hjk.le hz']
    have hd0 : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    refine (norm_add_le _ _).trans ?_
    have h1 := hd.norm_iteratedFDerivWithin_vorticity_sub_le hα.le hα1 hjk.le hz hz'
    have h2 := hint_le (mul_nonneg (hFt.holder_nonneg hk) hd0)
      (f := fun r ↦ iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z -
        iteratedFDeriv ℝ j (fun y ↦ forcingOf k v T κ θ₀ y r) z') fun r hr ↦ by
      rw [h.iteratedFDeriv_forcingOf_eq hd hκ hT (hr' hr) hjk.le hz,
        h.iteratedFDeriv_forcingOf_eq hd hκ hT (hr' hr) hjk.le hz']
      exact (h.hasHolderBounds_forcing hd hκ hα hα1 hk (hr' hr)).holder j hj hjk z z' hz hz'
    simp only [amplitudeHolder]
    linarith
  -- The size of the derivative of order `k`: the bound of the forcing at the time `r` is affine
  -- in `Ψ(r) ≤ Ψ(t)`.
  · rw [h.iteratedFDeriv_amplitudeOf hd hκ (by omega) hT ht le_rfl,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ le_rfl hz]
    refine (norm_add_le _ _).trans ?_
    have h2 := hint_le hFt.top_nonneg
      (f := fun r ↦ iteratedFDeriv ℝ k (fun y ↦ forcingOf k v T κ θ₀ y r) z) fun r hr ↦ by
      rw [h.iteratedFDeriv_forcingOf_eq hd hκ hT (hr' hr) le_rfl hz]
      exact ((h.hasHolderBounds_forcing hd hκ hα hα1 hk (hr' hr)).norm_top_le z hz).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hΨ hr) hfTS))
    have h1 := hd.norm_vorticity_le k le_rfl z hz
    simp only [amplitudeTopConst, amplitudeTopSlope]
    nlinarith
  -- Its Hölder constant, in the same way.
  · rw [h.iteratedFDeriv_amplitudeOf hd hκ (by omega) hT ht le_rfl,
      h.iteratedFDeriv_amplitudeOf hd hκ (by omega) hT ht le_rfl, hdiff le_rfl,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ le_rfl hz,
      iteratedFDeriv_weightedReflectionFun_of_nonneg 1 (by omega) hω₀ le_rfl hz']
    have hd0 : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    refine (norm_add_le _ _).trans ?_
    have h1 := hd.holder_vorticity z z' hz hz'
    have h2 := hint_le (mul_nonneg hFt.holder_top_nonneg hd0)
      (f := fun r ↦ iteratedFDeriv ℝ k (fun y ↦ forcingOf k v T κ θ₀ y r) z -
        iteratedFDeriv ℝ k (fun y ↦ forcingOf k v T κ θ₀ y r) z') fun r hr ↦ by
      rw [h.iteratedFDeriv_forcingOf_eq hd hκ hT (hr' hr) le_rfl hz,
        h.iteratedFDeriv_forcingOf_eq hd hκ hT (hr' hr) le_rfl hz']
      exact ((h.hasHolderBounds_forcing hd hκ hα hα1 hk (hr' hr)).holder_top z z' hz hz').trans
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (hΨ hr) hfTHS)) hd0)
    simp only [amplitudeTopHolderConst, amplitudeTopHolderSlope]
    nlinarith

/-- **The values of the amplitude** are at most `N + T Bκ₀ temperatureBound` on the closed
half-plane. -/
theorem abs_amplitudeOf_le (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    |amplitudeOf k v T κ ω₀ θ₀ y t| ≤ vorticityValueBound Bκ k c N T := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  have hθt := h.hasHolderBounds_comp_flowOn hd hα.le hα1 hk ht
  have hTb : 0 ≤ temperatureBound k c N T := hθt.bound_nonneg (by omega)
  have hB0 := hκ.bound_nonneg 0
  unfold amplitudeOf forcedAmplitude
  have h1 : |weightedReflectionFun 1 k ω₀ y| ≤ N := by
    rw [weightedReflectionFun_eq_of_nonneg 1 k ω₀ y hy]
    have := hd.norm_vorticity_le 0 (Nat.zero_le _) y hy
    rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at this
  have h2 : ‖∫ r in (0)..t, forcingOf k v T κ θ₀ y r‖ ≤
      Bκ 0 * temperatureBound k c N T * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    have hr' : r ∈ Icc (-T) T := uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)
    have hθ := h.hasHolderBounds_comp_flowOn hd hα.le hα1 hk hr'
    set X := flowOn v (-T) T r 0 y
    have hX : 0 ≤ X 1 := h.mapsTo r hr' 0 h0 hy
    rw [h.forcingOf_eq hd hr' hy, Function.comp_apply, norm_mul]
    refine mul_le_mul (by rw [Real.norm_eq_abs]; exact hκ.abs_le X) ?_ (norm_nonneg _) hB0
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
    rw [he, mul_one, ← norm_iteratedFDerivWithin_one _ (hU X hX)]
    exact hθ.norm_le 1 le_rfl (by omega) X hX
  have htT : |t - 0| ≤ T := by rw [sub_zero]; exact abs_le.mpr ⟨ht.1, ht.2⟩
  rw [Real.norm_eq_abs] at h2
  simp only [vorticityValueBound]
  have := mul_le_mul_of_nonneg_left htT (mul_nonneg hB0 hTb)
  calc _ ≤ |weightedReflectionFun 1 k ω₀ y| + |∫ r in (0)..t, forcingOf k v T κ θ₀ y r| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith

end IsTopBoundedField

/-! ### The carried vorticity of a velocity law -/

section Law

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {k : ℕ} {κ ω₀ θ₀ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ} {ω : ℝ → ℝ^2 → ℝ}
  {α R N T R₁ B Nlow : ℝ} {P : ℝ → ℝ}

/-- **The carried vorticity is the amplitude at level `k` at the label**, on the closed
half-plane, with the extensions of order `k + 1` of the fields of the law. -/
theorem carriedVorticity_eq (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (-T) T)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t =
      amplitudeOf k (fun r ↦ extendedField (k + 1) (U (ω r))) T κ ω₀ θ₀
        (flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T 0 t x) t := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hv := h.isTopBoundedField_law hU hR₁ hk hα hα1
  unfold carriedVorticity amplitudeOf forcedAmplitude
  rw [flowOn_lawField_eq hU h.history hR₁ (by omega) hα hα1 h0 ht hx]
  set Y := flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T 0 t x
  have hY : 0 ≤ Y 1 := hv.mapsTo 0 h0 t ht hx
  congr 1
  · rw [dataVorticity_of_nonneg ω₀ hY, weightedReflectionFun_eq_of_nonneg 1 k ω₀ Y hY]
  · refine intervalIntegral.integral_congr fun r hr ↦ ?_
    have hr' : r ∈ Icc (-T) T := uIcc_subset_Icc h0 ht hr
    rw [weightedForcing_lawField_eq hU h hd hR₁ hk hα hα1 hr' hY, hv.forcingOf_eq hd hr' hY]

/-- **The `C^{k,α}` bounds of the carried vorticity** at a time `t ∈ [-T, T]`, with top-order
constants affine in `Ψ(t) = |∫ₜ⁰ P(|r|) dr|`. -/
theorem hasHolderBounds_carriedVorticity (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k
      (fun x ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t) α
      (carriedVorticityBound Bκ k (lawConst C k α * Nlow) N T)
      (vorticityHolder Bκ k α (lawConst C k α * Nlow) N T)
      (vorticityTopConst Bκ k (lawConst C k α * Nlow) N T +
        vorticityTopSlope Bκ k (lawConst C k α * Nlow) (lawConst C k α) N T *
          |∫ r in t..0, P (|r|)|)
      (vorticityTopHolderConst Bκ k α (lawConst C k α * Nlow) N T +
        vorticityTopHolderSlope Bκ k α (lawConst C k α * Nlow) (lawConst C k α) N T *
          |∫ r in t..0, P (|r|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hv := h.isTopBoundedField_law hU hR₁ hk hα hα1
  have hc := (hv.hasHolderBounds_amplitudeOf hd hκ hα hα1.le hk hT ht).comp
    (hv.hasHolderBounds_flowOn hα.le hα1.le hk h0 ht) (hv.mapsTo 0 h0 t ht)
    (flowBound_nonneg _ T (by omega))
    (fun z z' hz hz' ↦ hv.norm_flowOn_sub_le (by omega) h0 ht hz hz') hk hα.le
  rw [compTopBound_outer_affine, compTopHolder_outer_affine] at hc
  exact hc.congr fun x hx ↦ carriedVorticity_eq hU h hd hR₁ hk hα hα1 ht hx

/-- The carried vorticity is bounded by `vorticityValueBound` on the closed half-plane. -/
theorem abs_carriedVorticity_le_vorticityValueBound (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t| ≤
      vorticityValueBound Bκ k (lawConst C k α * Nlow) N T := by
  have hv := h.isTopBoundedField_law hU hR₁ hk hα hα1
  rw [carriedVorticity_eq hU h hd hR₁ hk hα hα1 ht hx]
  exact hv.abs_amplitudeOf_le hd hκ hα hα1.le hk ht
    (hv.mapsTo 0 (zero_mem_Icc_neg_of_mem ht) t ht hx)

/-- **The level-`k` bounds of the carried vorticity**, with `Φ(t) = ∫₀^{|t|} P`: at a time
`t ∈ [-T, T]` it has `C^{k,α}` bounds on the closed half-plane with the constants
`carriedVorticityBound`, `vorticityHolder` below the top order and top-order constants
`vorticityTopConst + vorticityTopSlope Φ(t)` and
`vorticityTopHolderConst + vorticityTopHolderSlope Φ(t)`, with `c = lawConst C k α · Nlow` and
`c' = lawConst C k α`. The top order is affine in the integral of the majorant, which is what
the propagation of regularity needs. Proof: the carried vorticity is the amplitude at level `k`
composed with the label map (`carriedVorticity_eq`), and the bounds of a composition apply. -/
theorem carriedVorticity_holderBounds (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k
      (fun x ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t) α
      (carriedVorticityBound Bκ k (lawConst C k α * Nlow) N T)
      (vorticityHolder Bκ k α (lawConst C k α * Nlow) N T)
      (vorticityTopConst Bκ k (lawConst C k α * Nlow) N T +
        vorticityTopSlope Bκ k (lawConst C k α * Nlow) (lawConst C k α) N T *
          ∫ r in (0)..(|t|), P r)
      (vorticityTopHolderConst Bκ k α (lawConst C k α * Nlow) N T +
        vorticityTopHolderSlope Bκ k α (lawConst C k α * Nlow) (lawConst C k α) N T *
          ∫ r in (0)..(|t|), P r) := by
  have hb := hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT ht
  rwa [(h.isTopBoundedField_law hU hR₁ hk hα hα1).abs_integral_eq ht] at hb

/-- **The level-`k` bounds of the carried temperature**, with `Φ(t) = ∫₀^{|t|} P`. -/
theorem carriedTemperature_holderBounds (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (fun x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x t) α
      (temperatureBound k (lawConst C k α * Nlow) N T)
      (temperatureHolder k α (lawConst C k α * Nlow) N T)
      (temperatureTopConst k (lawConst C k α * Nlow) N T +
        temperatureTopSlope k (lawConst C k α * Nlow) (lawConst C k α) N T *
          ∫ r in (0)..(|t|), P r)
      (temperatureTopHolderConst k α (lawConst C k α * Nlow) N T +
        temperatureTopHolderSlope k α (lawConst C k α * Nlow) (lawConst C k α) N T *
          ∫ r in (0)..(|t|), P r) := by
  have hb := hasHolderBounds_carriedTemperature hU h hd hR₁ hk hα hα1 ht
  rwa [(h.isTopBoundedField_law hU hR₁ hk hα hα1).abs_integral_eq ht] at hb

/-- **Continuity in time of the derivatives of the carried temperature**, uniformly on the closed
half-plane, for every order at most `k + 1`. -/
theorem uniform_carriedTemperature (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) :
    ∀ j ≤ k + 1, ∀ t ∈ Icc (-T) T, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (-T) T, |s - t| < δ →
      ∀ y : ℝ^2, 0 ≤ y 1 →
        ‖iteratedFDerivWithin ℝ j (fun x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x s) H̄ y -
          iteratedFDerivWithin ℝ j (fun x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x t) H̄
            y‖ ≤ ε := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hω1 := h.history.toIsC1VorticityHistory (by omega) hα.le hα1.le
  have hb := isBoundedFlowOn_lawField hU hω1 hR₁ hα hα1 (by linarith)
  have hv := (hω1.isC2FieldOn_lawField hU hR₁ hα hα1).toIsC1FieldOn
  have hN := hd.nonneg
  have hθ := hd.hasHolderBounds_temperature hα.le hα1.le
  have hf := h.isTopBoundedField_law hU hR₁ hk hα hα1
  set Φ := ∫ r in (0)..T, P r
  have hΦ : 0 ≤ Φ := intervalIntegral.integral_nonneg hT fun r hr ↦ h.nonneg r hr
  have h0b := hasHolderBounds_carriedTemperature hU h hd hR₁ hk hα hα1 h0
  refine uniform_iteratedFDerivWithin_of_holder
    (f := fun s x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x s)
    (M := temperatureHolder k α (lawConst C k α * Nlow) N T +
      (|temperatureTopHolderConst k α (lawConst C k α * Nlow) N T| +
        |temperatureTopHolderSlope k α (lawConst C k α * Nlow) (lawConst C k α) N T| * Φ)) hα
    (by have := h0b.holder_nonneg (by omega); positivity)
    (fun s hs ↦ (hasHolderBounds_carriedTemperature hU h hd hR₁ hk hα hα1 hs).contDiffOn)
    (fun s hs j hj hjk y z hy hz ↦ ?_) (fun t ht ε hε ↦ ?_)
  · have hbs := hasHolderBounds_carriedTemperature hU h hd hR₁ hk hα hα1 hs
    have hd0 : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hab : 0 ≤ |temperatureTopHolderConst k α (lawConst C k α * Nlow) N T| +
        |temperatureTopHolderSlope k α (lawConst C k α * Nlow) (lawConst C k α) N T| * Φ := by
      positivity
    rcases hjk.lt_or_eq with hjk' | rfl
    · exact (hbs.holder j hj hjk' y z hy hz).trans (mul_le_mul_of_nonneg_right (by linarith) hd0)
    · refine (hbs.holder_top y z hy hz).trans (mul_le_mul_of_nonneg_right ?_ hd0)
      have hΨ := hf.abs_integral_le_integral hs
      have hΨ0 : 0 ≤ |∫ r in s..0, P (|r|)| := abs_nonneg _
      have h1 := le_abs_self (temperatureTopHolderConst k α (lawConst C k α * Nlow) N T)
      have h2 : temperatureTopHolderSlope k α (lawConst C k α * Nlow) (lawConst C k α) N T *
          |∫ r in s..0, P (|r|)| ≤
          |temperatureTopHolderSlope k α (lawConst C k α * Nlow) (lawConst C k α) N T| * Φ :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) hΨ0).trans
          (mul_le_mul_of_nonneg_left hΨ (abs_nonneg _))
      have := h0b.holder_nonneg (by omega)
      linarith
  · have hL := hb.zero_le_L h0
    have hV := hb.zero_le_V h0
    set c := N * Real.exp (C 0 α * (1 + B * Real.log (2 + 2 * B) + B) * (T - -T)) * (C 0 0 * B)
    have hc : 0 ≤ c := mul_nonneg (mul_nonneg hN (Real.exp_pos _).le) hV
    refine ⟨ε / (c + 1), by positivity, fun s hs hst y hy ↦ ?_⟩
    have hYs := hb.flowOn_mem h0 hs hy
    have hYt := hb.flowOn_mem h0 ht hy
    simp only [carriedTemperature]
    rw [dataTemperature_of_nonneg θ₀ hYs, dataTemperature_of_nonneg θ₀ hYt]
    refine (hθ.norm_sub_le (by omega) hYs hYt).trans ?_
    have hl := hb.norm_label_sub_le hv h0 hs ht hy
    calc N * ‖flowOn (lawField U ω) (-T) T 0 s y - flowOn (lawField U ω) (-T) T 0 t y‖
        ≤ N * (Real.exp (C 0 α * (1 + B * Real.log (2 + 2 * B) + B) * (T - -T)) *
            (C 0 0 * B * |s - t|)) :=
          mul_le_mul_of_nonneg_left hl hN
      _ = c * |s - t| := by simp only [c]; ring
      _ ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hst.le hc
      _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith

/-- **The carried history is again a `C^{k,α}` history.** For `k ≥ 2` and `0 < α < 1`, the
vorticity carried by the flow of the field of a `C^{k,α}` history with a top-order majorant,
supported in the disc of radius `R₁ ≤ R₀`, is a `C^{k,α}` history on `[-T, T]`, supported on the
closed half-plane in the disc of radius `R + C 0 0 B T`, with the bound `carriedBound` built from
`Φ = ∫₀ᵀ P`. So the iteration map keeps the regularity of order `k`. Proof: the `C^{k,α}` bounds
of the carried vorticity at each time, with `Ψ(t) ≤ Φ`; the continuity in time of the
derivatives follows from the continuity of the values and the uniform Hölder bounds. -/
theorem isCkVorticityHistory_carriedHistory (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsTopBoundedHistory k ω T α R₁ B Nlow P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) (hT : 0 ≤ T) :
    IsCkVorticityHistory k (carriedHistory U κ ω₀ θ₀ (-T) T ω) (-T) T α (R + C 0 0 * B * T)
      (carriedBound Bκ k α (lawConst C k α * Nlow) (lawConst C k α) N T
        (∫ r in (0)..T, P r)) := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hω1 := h.history.toIsC1VorticityHistory (by omega) hα.le hα1.le
  have hb := isBoundedFlowOn_lawField hU hω1 hR₁ hα hα1 (by linarith)
  have hv2 := hω1.isC2FieldOn_lawField hU hR₁ hα hα1
  have hd1 := hd.toIsHolderData (by omega) hα.le hα1.le
  have hf := h.isTopBoundedField_law hU hR₁ hk hα hα1
  set c := lawConst C k α * Nlow
  set c' := lawConst C k α
  set Φ := ∫ r in (0)..T, P r
  have hΦ : 0 ≤ Φ := intervalIntegral.integral_nonneg hT fun r hr ↦ h.nonneg r hr
  have hb0 := hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT h0
  have hVB : 0 ≤ vorticityValueBound Bκ k c N T :=
    (abs_nonneg _).trans (abs_carriedVorticity_le_vorticityValueBound hU hκ h hd hR₁ hk hα hα1
      h0 (x := 0) (by simp))
  have hvB : 0 ≤ carriedVorticityBound Bκ k c N T := hb0.bound_nonneg hk
  have hvH : 0 ≤ vorticityHolder Bκ k α c N T := hb0.holder_nonneg hk
  have hA1 : 0 ≤ |vorticityTopConst Bκ k c N T| + |vorticityTopSlope Bκ k c c' N T| * Φ := by
    positivity
  have hA2 : 0 ≤ |vorticityTopHolderConst Bκ k α c N T| +
      |vorticityTopHolderSlope Bκ k α c c' N T| * Φ := by positivity
  have haffine (a b : ℝ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
      a + b * |∫ r in t..0, P (|r|)| ≤ |a| + |b| * Φ :=
    add_le_add (le_abs_self a) ((mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hf.abs_integral_le_integral ht) (abs_nonneg _)))
  refine ⟨fun t ht ↦ (hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT
    ht).contDiffOn, fun t ht y hy hyR ↦ (carried_eq_zero hb h0 hd1 ht
      (abs_le.mpr ⟨ht.1, ht.2⟩) hy hyR).1, fun t ht j hj y hy ↦ ?_,
    fun t ht y z hy hz ↦ ?_, ?_⟩
  -- The derivatives of order `j ≤ k` are bounded: the values, the orders below `k`, the order `k`.
  · have hbt := hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT ht
    change ‖iteratedFDerivWithin ℝ j
      (fun x ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) (-T) T x t) H̄ y‖ ≤ _
    simp only [carriedBound]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      have := abs_carriedVorticity_le_vorticityValueBound hU hκ h hd hR₁ hk hα hα1 ht hy
      linarith
    rcases hj.lt_or_eq with hjk | hjk
    · have := hbt.norm_le j hj0 hjk y hy
      linarith
    · rw [hjk]
      have := (hbt.norm_top_le y hy).trans (haffine _ _ ht)
      linarith
  -- The derivative of order `k` is Hölder.
  · have hbt := hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT ht
    refine (hbt.holder_top y z hy hz).trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (norm_nonneg _) α))
    simp only [carriedBound]
    have := haffine (vorticityTopHolderConst Bκ k α c N T)
      (vorticityTopHolderSlope Bκ k α c c' N T) ht
    linarith
  -- Continuity in time of the derivatives, uniformly on the closed half-plane: from the
  -- continuity of the values and the uniform Hölder bounds.
  · refine uniform_iteratedFDerivWithin_of_holder (f := carriedHistory U κ ω₀ θ₀ (-T) T ω)
      (M := vorticityHolder Bκ k α c N T + (|vorticityTopHolderConst Bκ k α c N T| +
        |vorticityTopHolderSlope Bκ k α c c' N T| * Φ)) hα (by positivity)
      (fun s hs ↦ (hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT hs).contDiffOn)
      (fun s hs j hj hjk y z hy hz ↦ ?_) (fun t ht ε hε ↦ ?_)
    · have hbs := hasHolderBounds_carriedVorticity hU hκ h hd hR₁ hk hα hα1 hT hs
      have hd0 : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      rcases hjk.lt_or_eq with hjk' | hjk'
      · exact (hbs.holder j hj hjk' y z hy hz).trans
          (mul_le_mul_of_nonneg_right (by linarith) hd0)
      · rw [hjk']
        refine (hbs.holder_top y z hy hz).trans (mul_le_mul_of_nonneg_right ?_ hd0)
        have := haffine (vorticityTopHolderConst Bκ k α c N T)
          (vorticityTopHolderSlope Bκ k α c c' N T) hs
        linarith
    · obtain ⟨δ, hδ, hδε⟩ := exists_abs_carriedVorticity_sub_le hb hv2 h0 hd1 hκ ht hε
      exact ⟨δ, hδ, fun s hs hst y hy ↦ by
        rw [Real.norm_eq_abs]; exact hδε s hs hst y hy⟩

end Law

end HalfPlaneSystem
