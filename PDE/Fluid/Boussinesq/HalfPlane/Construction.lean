/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Solution
public import PDE.Hyperbolic.Transport.Lagrangian
public import PDE.Fluid.Incompressible.HalfPlane.VelocityComparison

/-!
# The Lagrangian construction of half-plane Boussinesq fields from a vorticity history

Local existence is proved by iterating a map on vorticity histories. A history `ω : ℝ → ℝ² → ℝ`
gives the velocity field `historyField ω t = extendedVelocity 2 (ω t)`: the half-plane
Biot-Savart velocity of `ω t`, extended across the boundary by the weighted reflection of order
two. Its flow on the times `[a, b]` carries the data: the temperature
`carriedTemperature θ₀ ω a b x t = θ̃₀(Y)` and the vorticity
`carriedVorticity ω₀ θ₀ ω a b x t = ω̃₀(Y) + ∫₀ᵗ ∂₀θ(X(r, Y), r) dr` at the label `Y` of the
particle at `x` at time `t`, where `ω̃₀` and `θ̃₀` are the data extended across the boundary by the
weighted reflections of orders one and two, and the forcing is written in label form
(`PDE.Hyperbolic.Transport.labelForcing`). A history is a solution exactly when it is a fixed
point of `ω ↦ carriedVorticity ω₀ θ₀ ω a b` on the closed half-plane.

The data class `IsHolderData ω₀ θ₀ α R N` is the regularity of the local theorem:
`ω₀ ∈ C^{1,α}` and `θ₀ ∈ C^{2,α}` within the closed half-plane, vanishing there outside the disc of
radius `R`, with all norms at most `N`.

## Main definitions

* `IsHolderData`, `IsRegularSolutionOn`, `dataVorticity`, `dataTemperature`.
* `historyField`, `historyFieldDeriv`, `historyFieldDeriv₂`.
* `carriedTemperature`, `carriedVorticity`, `carriedHistory`.

## Main results

* `historyField_congr`: the field depends only on the history on the closed half-plane.
* `IsC1VorticityHistory.isC2FieldOn_historyField`: a `C^{1,α}` history gives a `C²` field.
* `carriedVorticity_zero`, `carriedTemperature_zero`: the carried fields start from the data.
-/

@[expose] public section

noncomputable section

open Set
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- Data `ω₀ ∈ C^{1,α}` and `θ₀ ∈ C^{2,α}` within the closed half-plane, vanishing there outside
the disc of radius `R`, with the values, the derivatives and the top Hölder constants at most
`N`. -/
structure IsHolderData (ω₀ θ₀ : ℝ^2 → ℝ) (α R N : ℝ) : Prop where
  /-- The vorticity is `C¹` within the closed half-plane. -/
  vorticity_contDiffOn : ContDiffOn ℝ 1 ω₀ H̄
  /-- The temperature is `C²` within the closed half-plane. -/
  temperature_contDiffOn : ContDiffOn ℝ 2 θ₀ H̄
  /-- Both vanish on the closed half-plane outside the disc of radius `R`. -/
  eq_zero : ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ → ω₀ x = 0 ∧ θ₀ x = 0
  /-- The vorticity is bounded by `N`. -/
  abs_vorticity_le : ∀ x : ℝ^2, 0 ≤ x 1 → |ω₀ x| ≤ N
  /-- The gradient of the vorticity is bounded by `N`. -/
  norm_fderivWithin_vorticity_le : ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderivWithin ℝ ω₀ H̄ x‖ ≤ N
  /-- The gradient of the vorticity is `α`-Hölder with constant `N`. -/
  holder_vorticity : ∀ x y : ℝ^2, 0 ≤ x 1 → 0 ≤ y 1 →
    ‖fderivWithin ℝ ω₀ H̄ x - fderivWithin ℝ ω₀ H̄ y‖ ≤ N * ‖x - y‖ ^ α
  /-- The temperature is bounded by `N`. -/
  abs_temperature_le : ∀ x : ℝ^2, 0 ≤ x 1 → |θ₀ x| ≤ N
  /-- The gradient of the temperature is bounded by `N`. -/
  norm_fderivWithin_temperature_le : ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderivWithin ℝ θ₀ H̄ x‖ ≤ N
  /-- The second derivative of the temperature is bounded by `N`. -/
  norm_fderivWithin_fderivWithin_temperature_le : ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖fderivWithin ℝ (fderivWithin ℝ θ₀ H̄) H̄ x‖ ≤ N
  /-- The second derivative of the temperature is `α`-Hölder with constant `N`. -/
  holder_temperature : ∀ x y : ℝ^2, 0 ≤ x 1 → 0 ≤ y 1 →
    ‖fderivWithin ℝ (fderivWithin ℝ θ₀ H̄) H̄ x - fderivWithin ℝ (fderivWithin ℝ θ₀ H̄) H̄ y‖ ≤
      N * ‖x - y‖ ^ α

/-- A solution whose time slices are data of the class `IsHolderData` with support radius and
bounds uniform on every compact subinterval of the times. The local solutions of
`exists_isSolutionOn_Ioo` are regular. -/
structure IsRegularSolutionOn (sol : VorticityStreamFields) (I : Set ℝ) (α : ℝ) : Prop
    extends IsSolutionOn sol I where
  /-- Uniform `C^{1,α} × C^{2,α}` bounds of the slices on compact subintervals. -/
  holderData : ∀ a b : ℝ, Icc a b ⊆ I → ∃ R N : ℝ, ∀ t ∈ Icc a b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N

/-- The vorticity datum extended across the boundary by the weighted reflection of order one. -/
def dataVorticity (ω₀ : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  weightedReflectionFun 1 1 ω₀

/-- The temperature datum extended across the boundary by the weighted reflection of order two. -/
def dataTemperature (θ₀ : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  weightedReflectionFun 1 2 θ₀

/-- The velocity field of a vorticity history: at time `t` the half-plane Biot-Savart velocity
of `ω t`, extended across the boundary by the weighted reflection of order two. -/
def historyField (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) : ℝ^2 → ℝ^2 :=
  extendedVelocity 2 (ω t)

/-- The spatial derivative of the velocity field of a history. -/
def historyFieldDeriv (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 :=
  fderiv ℝ (historyField ω t) x

/-- The second spatial derivative of the velocity field of a history. -/
def historyFieldDeriv₂ (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2 :=
  fderiv ℝ (fderiv ℝ (historyField ω t)) x

/-- The temperature carried by the flow of the velocity field of `ω` on the times `[a, b]`: the
extended datum at the label of the particle at `x` at time `t`. -/
def carriedTemperature (θ₀ : ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (a b : ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  dataTemperature θ₀ (flowOn (historyField ω) a b 0 t x)

/-- The vorticity carried by the flow of the velocity field of `ω` on the times `[a, b]` with the
forcing `∂₀θ` in label form: `ω̃₀(Y) + ∫₀ᵗ ∂₀θ(X(r, Y), r) dr` at the label `Y` of `(x, t)`. -/
def carriedVorticity (ω₀ θ₀ : ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (a b : ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  forcedAmplitude (dataVorticity ω₀)
    (labelForcing (historyField ω) (historyFieldDeriv ω) a b (dataTemperature θ₀)
      (EuclideanSpace.single 0 1))
    (flowOn (historyField ω) a b 0 t x) t

/-- The carried vorticity as a vorticity history: the iteration map of the local existence proof
on the times `[a, b]`. -/
def carriedHistory (ω₀ θ₀ : ℝ^2 → ℝ) (a b : ℝ) (ω : ℝ → ℝ^2 → ℝ) : ℝ → ℝ^2 → ℝ :=
  fun t x ↦ carriedVorticity ω₀ θ₀ ω a b x t

/-- The extended vorticity datum agrees with the datum on the closed half-plane. -/
theorem dataVorticity_of_nonneg (ω₀ : ℝ^2 → ℝ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    dataVorticity ω₀ x = ω₀ x :=
  weightedReflectionFun_eq_of_nonneg 1 1 ω₀ x hx

/-- The extended temperature datum agrees with the datum on the closed half-plane. -/
theorem dataTemperature_of_nonneg (θ₀ : ℝ^2 → ℝ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    dataTemperature θ₀ x = θ₀ x :=
  weightedReflectionFun_eq_of_nonneg 1 2 θ₀ x hx

/-- The extended vorticity datum is `C¹`. -/
theorem contDiff_dataVorticity {ω₀ : ℝ^2 → ℝ} (h : ContDiffOn ℝ 1 ω₀ H̄) :
    ContDiff ℝ 1 (dataVorticity ω₀) :=
  PDE.Analysis.contDiff_weightedReflectionFun (k := 1) 1 le_rfl (by exact_mod_cast h)

/-- The extended temperature datum is `C²`. -/
theorem contDiff_dataTemperature {θ₀ : ℝ^2 → ℝ} (h : ContDiffOn ℝ 2 θ₀ H̄) :
    ContDiff ℝ 2 (dataTemperature θ₀) :=
  PDE.Analysis.contDiff_weightedReflectionFun (k := 2) 1 (by norm_num) (by exact_mod_cast h)

/-- On the closed half-plane the field of a history is the half-plane velocity. -/
theorem historyField_of_nonneg (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    historyField ω t x = halfPlaneVelocity (ω t) x :=
  extendedVelocity_of_nonneg 2 (ω t) hx

/-- The velocity field of a history is tangent to the boundary at the times of the history. -/
theorem historyField_normal_eq_zero {ω : ℝ → ℝ^2 → ℝ} {a b α R₁ B M : ℝ}
    (hω : IsVorticityHistory ω a b α R₁ B M) {r : ℝ} (hr : r ∈ Icc a b) {x : ℝ^2}
    (hx : x 1 = 0) : historyField ω r x 1 = 0 :=
  extendedVelocity_normal_eq_zero 2 (hω.continuousOn r hr) (hω.eq_zero r hr) hx

/-- On the closed half-plane the velocity field of a history is bounded by `(1 + R₀²) B`,
`R₀ = max R₁ 0`. -/
theorem norm_historyField_le {ω : ℝ → ℝ^2 → ℝ} {a b α R₁ B M : ℝ}
    (hω : IsVorticityHistory ω a b α R₁ B M) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2}
    (hy : 0 ≤ y 1) : ‖historyField ω r y‖ ≤ (1 + max R₁ 0 ^ 2) * B := by
  rw [historyField_of_nonneg ω r hy]
  exact norm_halfPlaneVelocity_le_of_abs_le (hω.continuousOn r hr) (hω.eq_zero_max hr)
    (le_max_right R₁ 0) (hω.abs_le r hr) y

/-- The field of a history depends only on the values of the history on the closed
half-plane. -/
theorem historyField_congr {ω ω' : ℝ → ℝ^2 → ℝ} {t : ℝ}
    (h : ∀ x : ℝ^2, 0 ≤ x 1 → ω t x = ω' t x) : historyField ω t = historyField ω' t := by
  have hv : halfPlaneVelocity (ω t) = halfPlaneVelocity (ω' t) := by
    unfold halfPlaneVelocity
    rw [GreenFunction.halfSpaceGreenPotential_congr fun y hy ↦ h y (le_of_lt hy)]
  funext x
  simp only [historyField, extendedVelocity, hv]

/-- The carried fields depend only on the values of the history on the closed half-plane. -/
theorem carriedVorticity_congr {ω₀ θ₀ : ℝ^2 → ℝ} {ω ω' : ℝ → ℝ^2 → ℝ} {a b : ℝ}
    (h : ∀ t, ∀ x : ℝ^2, 0 ≤ x 1 → ω t x = ω' t x) :
    carriedVorticity ω₀ θ₀ ω a b = carriedVorticity ω₀ θ₀ ω' a b := by
  have hf : historyField ω = historyField ω' := funext fun t ↦ historyField_congr (h t)
  have hd : historyFieldDeriv ω = historyFieldDeriv ω' := by
    funext t x
    simp only [historyFieldDeriv, hf]
  funext x t
  simp only [carriedVorticity, hf, hd]

/-- The carried temperature depends only on the values of the history on the closed
half-plane. -/
theorem carriedTemperature_congr {θ₀ : ℝ^2 → ℝ} {ω ω' : ℝ → ℝ^2 → ℝ} {a b : ℝ}
    (h : ∀ t, ∀ x : ℝ^2, 0 ≤ x 1 → ω t x = ω' t x) :
    carriedTemperature θ₀ ω a b = carriedTemperature θ₀ ω' a b := by
  have hf : historyField ω = historyField ω' := funext fun t ↦ historyField_congr (h t)
  funext x t
  simp only [carriedTemperature, hf]

/-- The velocity field of a `C^{1,α}` vorticity history is a `C²` field, with first derivatives
bounded by `2 reflectionBound 2 1 · katoBound α R₀ B M` and second derivatives by
`2 reflectionBound 2 2 · secondDerivBound α R₀ B B₁ M₁`, `R₀ = max R 0`. -/
theorem IsC1VorticityHistory.isC2FieldOn_historyField {ω : ℝ → ℝ^2 → ℝ}
    {a b α R B M B₁ M₁ : ℝ} (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hα : 0 < α)
    (hα1 : α < 1) :
    IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 * katoBound α (max R 0) B M))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R 0) B B₁ M₁)) :=
  hω.isC2FieldOn hα hα1

/-- On the closed half-plane the derivative of the field of a `C^{1,α}` history is the derivative
of the half-plane velocity within the closed half-plane. -/
theorem IsC1VorticityHistory.historyFieldDeriv_eq {ω : ℝ → ℝ^2 → ℝ}
    {a b α R B M B₁ M₁ : ℝ} (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) (hα : 0 < α)
    (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    historyFieldDeriv ω r y = fderivWithin ℝ (halfPlaneVelocity (ω r)) H̄ y :=
  fderiv_extendedVelocity_of_nonneg (K := 2) (by norm_num)
    (hω.contDiffOn_halfPlaneVelocity_two hα hα1 hr) hy

/-- At time zero the carried vorticity is the extended datum. -/
theorem carriedVorticity_zero (ω₀ θ₀ : ℝ^2 → ℝ) {ω : ℝ → ℝ^2 → ℝ} {a b : ℝ} {K : NNReal}
    (hv : IsLipschitzFieldOn (historyField ω) a b K) (h0 : (0 : ℝ) ∈ Icc a b) (x : ℝ^2) :
    carriedVorticity ω₀ θ₀ ω a b x 0 = dataVorticity ω₀ x := by
  simp [carriedVorticity, forcedAmplitude, hv.flowOn_self h0]

/-- At time zero the carried temperature is the extended datum: the flow from time `0` to
time `0` is the identity by its definition, whatever the field and the interval. -/
theorem carriedTemperature_zero (θ₀ : ℝ^2 → ℝ) {ω : ℝ → ℝ^2 → ℝ} {a b : ℝ} (x : ℝ^2) :
    carriedTemperature θ₀ ω a b x 0 = dataTemperature θ₀ x := by
  rw [carriedTemperature]
  congr 1
  unfold flowOn
  split_ifs with h
  exacts [h.choose_spec.1, rfl]

end Boussinesq.HalfPlane
