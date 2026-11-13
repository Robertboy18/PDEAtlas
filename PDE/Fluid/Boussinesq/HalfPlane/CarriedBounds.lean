/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Construction
public import PDE.Analysis.ODE.Flow.Estimates
import PDE.Analysis.Calculus.HolderInterpolation
import PDE.Analysis.Calculus.SliceDerivative

/-!
# Flow bounds and the amplitude of the carried vorticity

The iteration of the local existence proof replaces a vorticity history `ω` by the vorticity
`carriedVorticity ω₀ θ₀ ω a b` carried by the flow of its velocity field. Its estimates are stated
in terms of the data norms `N` of `IsHolderData` and of bounds of the flow kept as parameters
(`IsBoundedFlowOn`): the first variation is at most `L`, at distance at most `δ` from the identity,
the second variation is at most `σ` and `α`-Hölder in the initial point with constant `η`, the field
is at most `V` and its derivative at most `K₁` on the closed half-plane. For short times the flow
bounds come from the general flow estimates such as `IsC1FieldOn.norm_variationOn_le_of_invariant`;
along a solution with integrable velocity gradient they come from the same equations with a
time-dependent coefficient.

We bound the forcing and the amplitude: `Ω y t = ω̃₀(y) + ∫₀ᵗ G(y, r) dr` is the amplitude of the
particle of label `y`, with `G(y, r) = Dθ̃₀(y) (W e₀)` and `W` the inverse first variation along
that particle. All these bounds hold on the closed half-plane.

## Main definitions

* `IsBoundedFlowOn`: the bounds `V`, `K₁`, `L`, `δ`, `σ`, `η` of a flow on `[a, b]` on the
  closed half-plane.
* `forcingDerivBound`: the bound `N L (1 + L σ)` of the derivative of the forcing in the label.
* `forcingDerivHolderConst`: the `α`-Hölder constant in the label of that derivative.

## Main results

* `abs_labelForcing_le`: the forcing is at most `N L`.
* `norm_labelForcingDeriv_le`: the derivative of the forcing in the label is at most
  `N L (1 + L σ)`.
* `norm_labelForcingDeriv_sub_le`: that derivative is `α`-Hölder in the label with constant
  `forcingDerivHolderConst N L σ η`.
* `norm_fderiv_amplitude_le`: `‖DΩ‖ ≤ N + |t| c₀` with `c₀ = forcingDerivBound N L σ`.
* `norm_fderiv_amplitude_sub_le`: `‖DΩ(y) - DΩ(y')‖ ≤ (N + |t| c_α) ‖y - y'‖ ^ α` with
  `c_α = forcingDerivHolderConst N L σ η`.
* `abs_amplitude_sub_le`: the amplitude is Lipschitz in the label with constant `N + |t| c₀`.

## How it works

The derivative of the forcing in the label is `DG(y, r) = D²θ̃₀(y)[·, w] - Dθ̃₀(y)(W S[·, w])` with
`w = W e₀` and `S` the second variation, so `‖W‖ ≤ L`, `‖S‖ ≤ σ` and the data bound `N` give
`forcingDerivBound` (`norm_labelForcingDeriv_le`). At two labels the difference of `DG` is a Hölder
term from `D²θ̃₀` and `S` plus a Lipschitz term from `W` and `Dθ̃₀`
(`norm_labelForcingDeriv_sub_le_add`). A difference is also at most twice the bound, so the
Lipschitz term can be traded for a Hölder one (`norm_sub_le_add_max_mul_rpow`), which gives
`forcingDerivHolderConst`. The amplitude bounds follow by integration in time, since
`DΩ = Dω̃₀ + ∫₀ᵗ DG` (`hasFDerivAt_amplitude`).
-/
@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### Bounds of the flow on the closed half-plane -/

/-- Bounds on the closed half-plane, for all times of `[a, b]`, of the flow of a `C²` field: the
flow preserves the closed half-plane, the field is at most `V` and its derivative at most `K₁`
there, the first variation is at most `L` and at distance at most `δ` from the identity, and the
second variation is at most `σ` and `α`-Hölder in the initial point with constant `η`. -/
structure IsBoundedFlowOn (v : ℝ → ℝ^2 → ℝ^2) (Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2)
    (D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) (a b α V K₁ L δ σ η : ℝ) : Prop where
  /-- The flow preserves the closed half-plane. -/
  mapsTo : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) H̄ H̄
  /-- The field is bounded on the closed half-plane. -/
  norm_le : ∀ r ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → ‖v r y‖ ≤ V
  /-- The derivative of the field is bounded on the closed half-plane. -/
  norm_deriv_le : ∀ r ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → ‖Dv r y‖ ≤ K₁
  /-- The first variation is at most `L`. -/
  norm_variationOn_le : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖variationOn v Dv a b s t x‖ ≤ L
  /-- The first variation is at distance at most `δ` from the identity. -/
  norm_variationOn_sub_id_le : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖variationOn v Dv a b s t x - ContinuousLinearMap.id ℝ (ℝ^2)‖ ≤ δ
  /-- The second variation is at most `σ`. -/
  norm_secondVariationOn_le : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖secondVariationOn v Dv D2v a b s t x‖ ≤ σ
  /-- The second variation is `α`-Hölder in the initial point with constant `η`. -/
  holder_secondVariationOn : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x y : ℝ^2, 0 ≤ x 1 → 0 ≤ y 1 →
    ‖secondVariationOn v Dv D2v a b s t x - secondVariationOn v Dv D2v a b s t y‖ ≤
      η * ‖x - y‖ ^ α

namespace IsBoundedFlowOn

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0}

/-- The flow maps are `L`-Lipschitz on the closed half-plane. -/
theorem norm_flowOn_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC1FieldOn v Dv a b K) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x y : ℝ^2}
    (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖flowOn v a b s t x - flowOn v a b s t y‖ ≤ L * ‖x - y‖ :=
  PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := flowOn v a b s t) (f' := fun z ↦ variationOn v Dv a b s t z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn hs ht z).hasFDerivWithinAt)
    (fun z hz ↦ hb.norm_variationOn_le s hs t ht z hz) hy hx

/-- The first variation is `σ`-Lipschitz in the initial point on the closed half-plane. -/
theorem norm_variationOn_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖variationOn v Dv a b s t x - variationOn v Dv a b s t y‖ ≤ σ * ‖x - y‖ :=
  PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := variationOn v Dv a b s t) (f' := fun z ↦ secondVariationOn v Dv D2v a b s t z)
    (fun z _ ↦ (hv.hasFDerivAt_variationOn hs ht z).hasFDerivWithinAt)
    (fun z hz ↦ hb.norm_secondVariationOn_le s hs t ht z hz) hy hx

/-- The first variation is `α`-Hölder in the initial point on the closed half-plane with
constant `max σ (2 δ)`, which is small when the time span is short. -/
theorem norm_variationOn_sub_le_rpow (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖variationOn v Dv a b s t x - variationOn v Dv a b s t y‖ ≤ max σ (2 * δ) * ‖x - y‖ ^ α := by
  have h := PDE.Analysis.norm_sub_le_max_mul_rpow
    (f := fun z ↦ variationOn v Dv a b s t z - ContinuousLinearMap.id ℝ (ℝ^2)) (S := H̄)
    (L := σ) (M := δ) (fun z hz w hw ↦ by
      rw [sub_sub_sub_cancel_right, dist_eq_norm]
      exact hb.norm_variationOn_sub_le hv hs ht hz hw)
    (fun z hz ↦ hb.norm_variationOn_sub_id_le s hs t ht z hz) hα0 hα1 hx hy
  rwa [sub_sub_sub_cancel_right, dist_eq_norm] at h

end IsBoundedFlowOn

/-! ### The extended data on the closed half-plane -/

namespace IsHolderData

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R N : ℝ}

/-- The extended vorticity datum is `C¹`. -/
theorem contDiff_dataVorticity (hd : IsHolderData ω₀ θ₀ α R N) :
    ContDiff ℝ 1 (dataVorticity ω₀) :=
  Boussinesq.HalfPlane.contDiff_dataVorticity hd.vorticity_contDiffOn

/-- The extended temperature datum is `C²`. -/
theorem contDiff_dataTemperature (hd : IsHolderData ω₀ θ₀ α R N) :
    ContDiff ℝ 2 (dataTemperature θ₀) :=
  Boussinesq.HalfPlane.contDiff_dataTemperature hd.temperature_contDiffOn

/-- On the closed half-plane the derivative of the extended vorticity datum is the derivative
within the closed half-plane of the datum. -/
theorem fderiv_dataVorticity (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (dataVorticity ω₀) x = fderivWithin ℝ ω₀ H̄ x :=
  PDE.Analysis.fderiv_weightedReflectionFun_of_nonneg 1 (k := 1) le_rfl
    (by exact_mod_cast hd.vorticity_contDiffOn) hx

/-- On the closed half-plane the derivative of the extended temperature datum is the derivative
within the closed half-plane of the datum. -/
theorem fderiv_dataTemperature (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderiv ℝ (dataTemperature θ₀) x = fderivWithin ℝ θ₀ H̄ x :=
  PDE.Analysis.fderiv_weightedReflectionFun_of_nonneg 1 (k := 2) (by norm_num)
    (by exact_mod_cast hd.temperature_contDiffOn) hx

/-- On the closed half-plane the second derivative of the extended temperature datum is the
second derivative within the closed half-plane of the datum. -/
theorem fderiv_fderiv_dataTemperature (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) x = fderivWithin ℝ (fderivWithin ℝ θ₀ H̄) H̄ x :=
  PDE.Analysis.fderiv_fderiv_weightedReflectionFun_of_nonneg 1 (k := 2) le_rfl
    (by exact_mod_cast hd.temperature_contDiffOn) hx

/-- The extended vorticity datum is at most `N` on the closed half-plane. -/
theorem abs_dataVorticity_le (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |dataVorticity ω₀ x| ≤ N := by
  rw [dataVorticity_of_nonneg ω₀ hx]
  exact hd.abs_vorticity_le x hx

/-- The extended temperature datum is at most `N` on the closed half-plane. -/
theorem abs_dataTemperature_le (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |dataTemperature θ₀ x| ≤ N := by
  rw [dataTemperature_of_nonneg θ₀ hx]
  exact hd.abs_temperature_le x hx

/-- The derivative of the extended vorticity datum is at most `N` on the closed half-plane. -/
theorem norm_fderiv_dataVorticity_le (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2}
    (hx : 0 ≤ x 1) : ‖fderiv ℝ (dataVorticity ω₀) x‖ ≤ N := by
  rw [hd.fderiv_dataVorticity hx]
  exact hd.norm_fderivWithin_vorticity_le x hx

/-- The derivative of the extended vorticity datum is `α`-Hölder with constant `N` on the closed
half-plane. -/
theorem norm_fderiv_dataVorticity_sub_le (hd : IsHolderData ω₀ θ₀ α R N) {x y : ℝ^2}
    (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖fderiv ℝ (dataVorticity ω₀) x - fderiv ℝ (dataVorticity ω₀) y‖ ≤ N * ‖x - y‖ ^ α := by
  rw [hd.fderiv_dataVorticity hx, hd.fderiv_dataVorticity hy]
  exact hd.holder_vorticity x y hx hy

/-- The derivative of the extended temperature datum is at most `N` on the closed half-plane. -/
theorem norm_fderiv_dataTemperature_le (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2}
    (hx : 0 ≤ x 1) : ‖fderiv ℝ (dataTemperature θ₀) x‖ ≤ N := by
  rw [hd.fderiv_dataTemperature hx]
  exact hd.norm_fderivWithin_temperature_le x hx

/-- The second derivative of the extended temperature datum is at most `N` on the closed
half-plane. -/
theorem norm_fderiv_fderiv_dataTemperature_le (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2}
    (hx : 0 ≤ x 1) : ‖fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) x‖ ≤ N := by
  rw [hd.fderiv_fderiv_dataTemperature hx]
  exact hd.norm_fderivWithin_fderivWithin_temperature_le x hx

/-- The second derivative of the extended temperature datum is `α`-Hölder with constant `N` on the
closed half-plane. -/
theorem norm_fderiv_fderiv_dataTemperature_sub_le (hd : IsHolderData ω₀ θ₀ α R N) {x y : ℝ^2}
    (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) x - fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) y‖ ≤
      N * ‖x - y‖ ^ α := by
  rw [hd.fderiv_fderiv_dataTemperature hx, hd.fderiv_fderiv_dataTemperature hy]
  exact hd.holder_temperature x y hx hy

/-- The derivative of the extended temperature datum is `N`-Lipschitz on the closed
half-plane. -/
theorem norm_fderiv_dataTemperature_sub_le (hd : IsHolderData ω₀ θ₀ α R N) {x y : ℝ^2}
    (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖fderiv ℝ (dataTemperature θ₀) x - fderiv ℝ (dataTemperature θ₀) y‖ ≤ N * ‖x - y‖ := by
  have hθ := hd.contDiff_dataTemperature
  have hD : ∀ z, HasFDerivAt (fderiv ℝ (dataTemperature θ₀))
      (fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) z) z := fun z ↦
    ((hθ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z).hasFDerivAt
  exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ (hD z).hasFDerivWithinAt)
    (fun z hz ↦ hd.norm_fderiv_fderiv_dataTemperature_le hz) hy hx

/-- The extended data vanish on the closed half-plane outside the disc of radius `R`. -/
theorem data_eq_zero (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R < ‖x‖) : dataVorticity ω₀ x = 0 ∧ dataTemperature θ₀ x = 0 := by
  rw [dataVorticity_of_nonneg ω₀ hx, dataTemperature_of_nonneg θ₀ hx]
  exact hd.eq_zero x hx hxR

/-- The derivative of the extended temperature datum vanishes on the closed half-plane outside
the disc of radius `R`. -/
theorem fderiv_dataTemperature_eq_zero (hd : IsHolderData ω₀ θ₀ α R N) {x : ℝ^2}
    (hx : 0 ≤ x 1) (hxR : R < ‖x‖) : fderiv ℝ (dataTemperature θ₀) x = 0 :=
  PDE.Analysis.fderiv_slice_eq_zero (f := fun y (_ : ℝ) ↦ dataTemperature θ₀ y) (t := 0)
    (hd.contDiff_dataTemperature.differentiable two_ne_zero)
    (fun _ hy hyR ↦ (hd.data_eq_zero hy hyR).2) hx hxR

end IsHolderData

/-! ### Two elementary estimates -/

/-- A real `D` bounded by `A d ^ α + B d` and by `2 M` is at most `(A + max B (2 M)) d ^ α`. -/
theorem le_add_max_mul_rpow {D A B M d α : ℝ} (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hd0 : 0 ≤ d) (h₁ : D ≤ A * d ^ α + B * d) (h₂ : D ≤ 2 * M) (hM0 : 0 ≤ M) :
    D ≤ (A + max B (2 * M)) * d ^ α := by
  have hp0 : 0 ≤ d ^ α := Real.rpow_nonneg hd0 α
  have hmax : 0 ≤ max B (2 * M) := (by positivity : (0 : ℝ) ≤ 2 * M).trans (le_max_right _ _)
  rcases le_total d 1 with hd | hd
  · have hB : B * d ≤ max B (2 * M) * d ^ α :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0).trans
        (mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hd0 hd hα1) hmax)
    linarith
  · have := mul_le_mul_of_nonneg_left (Real.one_le_rpow hd hα0) hmax
    linarith [le_max_right B (2 * M), mul_nonneg hA hp0]

/-- A difference bounded by a Hölder term plus a Lipschitz term, of a function bounded by `M`, is
`α`-Hölder with constant `A + max B (2 M)`. -/
theorem norm_sub_le_add_max_mul_rpow {X F : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup F] {f : X → F} {S : Set X} {A B M α : ℝ} (hA : 0 ≤ A)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hf : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α + B * ‖x - y‖)
    (hM : ∀ x ∈ S, ‖f x‖ ≤ M) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f x - f y‖ ≤ (A + max B (2 * M)) * ‖x - y‖ ^ α :=
  le_add_max_mul_rpow hA hα0 hα1 (norm_nonneg _) (hf x hx y hy)
    ((norm_sub_le _ _).trans (by linarith [hM x hx, hM y hy])) ((norm_nonneg _).trans (hM x hx))

/-- The difference of two fourfold compositions of continuous linear maps. -/
theorem norm_comp_comp_comp_sub_le {E₁ E₂ E₃ E₄ F : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (B B' : E₄ →L[ℝ] F) (W W' : E₃ →L[ℝ] E₄) (P P' : E₂ →L[ℝ] E₃)
    (S S' : E₁ →L[ℝ] E₂) :
    ‖B.comp (W.comp (P.comp S)) - B'.comp (W'.comp (P'.comp S'))‖ ≤
      ‖B - B'‖ * ‖W‖ * ‖P‖ * ‖S‖ + ‖B'‖ * ‖W - W'‖ * ‖P‖ * ‖S‖ +
        ‖B'‖ * ‖W'‖ * ‖P - P'‖ * ‖S‖ + ‖B'‖ * ‖W'‖ * ‖P'‖ * ‖S - S'‖ := by
  have heq : B.comp (W.comp (P.comp S)) - B'.comp (W'.comp (P'.comp S')) =
      (B - B').comp (W.comp (P.comp S)) + B'.comp ((W - W').comp (P.comp S)) +
        B'.comp (W'.comp ((P - P').comp S)) + B'.comp (W'.comp (P'.comp (S - S'))) := by
    ext h
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  have hc (B : E₄ →L[ℝ] F) (W : E₃ →L[ℝ] E₄) (P : E₂ →L[ℝ] E₃) (S : E₁ →L[ℝ] E₂) :
      ‖B.comp (W.comp (P.comp S))‖ ≤ ‖B‖ * ‖W‖ * ‖P‖ * ‖S‖ := by
    refine (B.opNorm_comp_le _).trans ?_
    rw [mul_assoc, mul_assoc]
    gcongr
    exact (W.opNorm_comp_le _).trans (by gcongr; exact P.opNorm_comp_le _)
  rw [heq]
  exact norm_add₄_le.trans (add_le_add (add_le_add (add_le_add (hc ..) (hc ..)) (hc ..)) (hc ..))

/-- Evaluation at a vector has norm at most the norm of the vector. -/
theorem norm_apply_le' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (w : E) :
    ‖ContinuousLinearMap.apply ℝ F w‖ ≤ ‖w‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) fun T ↦ by
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact T.le_opNorm w

/-- A coordinate vector has norm one. -/
theorem norm_single_one (i : Fin 2) : ‖(EuclideanSpace.single i (1 : ℝ) : ℝ^2)‖ = 1 := by
  simp

/-! ### The forcing in label form -/

/-- The bound `N L (1 + L σ)` of the derivative in the label of the forcing. -/
def forcingDerivBound (N L σ : ℝ) : ℝ :=
  N * L * (1 + L * σ)

/-- The `α`-Hölder constant in the label of the derivative of the forcing. -/
def forcingDerivHolderConst (N L σ η : ℝ) : ℝ :=
  N * L * (1 + L * η) + max (N * L * σ * (1 + L + 2 * L * σ)) (2 * forcingDerivBound N L σ)

/-- The bound of the derivative of the forcing is nonnegative. -/
theorem forcingDerivBound_nonneg {N L σ : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 ≤ σ) :
    0 ≤ forcingDerivBound N L σ := by
  unfold forcingDerivBound; positivity

/-- The Hölder constant of the derivative of the forcing is nonnegative. -/
theorem forcingDerivHolderConst_nonneg {N L σ η : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hη : 0 ≤ η) : 0 ≤ forcingDerivHolderConst N L σ η := by
  unfold forcingDerivHolderConst
  have h := forcingDerivBound_nonneg hN hL hσ
  have : 0 ≤ max (N * L * σ * (1 + L + 2 * L * σ)) (2 * forcingDerivBound N L σ) :=
    (by positivity : (0 : ℝ) ≤ 2 * forcingDerivBound N L σ).trans (le_max_right _ _)
  positivity

namespace IsBoundedFlowOn

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0}
  {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ}

/-- The bound `L` of the first variation is nonnegative. -/
theorem zero_le_L (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (h0 : (0 : ℝ) ∈ Icc a b) :
    0 ≤ L :=
  (norm_nonneg _).trans (hb.norm_variationOn_le 0 h0 0 h0 0 (le_refl _))

/-- The bound `σ` of the second variation is nonnegative. -/
theorem zero_le_σ (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (h0 : (0 : ℝ) ∈ Icc a b) :
    0 ≤ σ :=
  (ContinuousLinearMap.opNorm_nonneg _).trans
    (hb.norm_secondVariationOn_le 0 h0 0 h0 0 (le_refl _))

/-- The bound `δ` of the distance of the first variation to the identity is nonnegative. -/
theorem zero_le_δ (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (h0 : (0 : ℝ) ∈ Icc a b) :
    0 ≤ δ :=
  (norm_nonneg _).trans (hb.norm_variationOn_sub_id_le 0 h0 0 h0 0 (le_refl _))

/-- The bound `V` of the field is nonnegative. -/
theorem zero_le_V (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (h0 : (0 : ℝ) ∈ Icc a b) :
    0 ≤ V :=
  (norm_nonneg _).trans (hb.norm_le 0 h0 0 (le_refl _))

/-- The bound `K₁` of the derivative of the field is nonnegative. -/
theorem zero_le_K₁ (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) : 0 ≤ K₁ :=
  (norm_nonneg _).trans (hb.norm_deriv_le 0 h0 0 (le_refl _))

/-- The Hölder constant `η` of the second variation is nonnegative. -/
theorem zero_le_η (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (h0 : (0 : ℝ) ∈ Icc a b) :
    0 ≤ η := by
  have h := hb.holder_secondVariationOn 0 h0 0 h0 0 (EuclideanSpace.single 1 1) (le_refl _)
    (by simp)
  rw [zero_sub, norm_neg, norm_single_one, Real.one_rpow, mul_one] at h
  exact (ContinuousLinearMap.opNorm_nonneg _).trans h

/-- The particle of label `y ∈ H̄` stays in the closed half-plane. -/
theorem flowOn_mem (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    0 ≤ flowOn v a b s t x 1 :=
  hb.mapsTo s hs t ht hx

/-- The inverse first variation along a particle is at most `L`. -/
theorem norm_inverse_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) {r : ℝ} (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖variationOn v Dv a b 0 r (flowOn v a b r 0 y)‖ ≤ L :=
  hb.norm_variationOn_le 0 h0 r hr _ (hb.flowOn_mem hr h0 hy)

/-- The inverse first variation along a particle is Lipschitz in the label. -/
theorem norm_inverse_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) {r : ℝ} (hr : r ∈ Icc a b)
    {y y' : ℝ^2} (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    ‖variationOn v Dv a b 0 r (flowOn v a b r 0 y) -
        variationOn v Dv a b 0 r (flowOn v a b r 0 y')‖ ≤ σ * L * ‖y - y'‖ := by
  calc _ ≤ σ * ‖flowOn v a b r 0 y - flowOn v a b r 0 y'‖ :=
        hb.norm_variationOn_sub_le hv h0 hr (hb.flowOn_mem hr h0 hy) (hb.flowOn_mem hr h0 hy')
    _ ≤ σ * (L * ‖y - y'‖) := mul_le_mul_of_nonneg_left
        (hb.norm_flowOn_sub_le hv.toIsC1FieldOn hr h0 hy hy') (hb.zero_le_σ h0)
    _ = σ * L * ‖y - y'‖ := by ring

/-- The forcing is at most `N L` on the closed half-plane. -/
theorem abs_labelForcing_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {r : ℝ} (hr : r ∈ Icc a b)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    |labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r| ≤ N * L := by
  have hW := hb.norm_inverse_le h0 hr hy
  have hN := hd.norm_fderiv_dataTemperature_le hy
  rw [labelForcing, ← Real.norm_eq_abs]
  refine ((fderiv ℝ (dataTemperature θ₀) y).le_opNorm _).trans ?_
  refine mul_le_mul hN ?_ (norm_nonneg _) ((norm_nonneg _).trans hN)
  refine ((variationOn v Dv a b 0 r _).le_opNorm _).trans ?_
  rw [norm_single_one, mul_one]
  exact hW

/-- The derivative of the forcing in the label is at most `N L (1 + L σ)` on the closed
half-plane. -/
theorem norm_labelForcingDeriv_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {r : ℝ} (hr : r ∈ Icc a b)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r‖ ≤
      forcingDerivBound N L σ := by
  set W := variationOn v Dv a b 0 r (flowOn v a b r 0 y)
  set S := secondVariationOn v Dv D2v a b r 0 y
  set w := W (EuclideanSpace.single 0 1)
  have hL0 := hb.zero_le_L h0
  have hW : ‖W‖ ≤ L := hb.norm_inverse_le h0 hr hy
  have hw : ‖w‖ ≤ L := (W.le_opNorm _).trans (by rw [norm_single_one, mul_one]; exact hW)
  have hS : ‖S‖ ≤ σ := hb.norm_secondVariationOn_le r hr 0 h0 y hy
  have hN1 := hd.norm_fderiv_dataTemperature_le hy
  have hN2 := hd.norm_fderiv_fderiv_dataTemperature_le hy
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hN1
  have hwR : ‖ContinuousLinearMap.apply ℝ ℝ w‖ ≤ L := (norm_apply_le' w).trans hw
  have hw2 : ‖ContinuousLinearMap.apply ℝ (ℝ^2) w‖ ≤ L := (norm_apply_le' w).trans hw
  have h₁ : ‖(ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) y)‖
      ≤ L * N := (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
  have h₂ : ‖(fderiv ℝ (dataTemperature θ₀) y).comp
      (W.comp ((ContinuousLinearMap.apply ℝ (ℝ^2) w).comp S))‖ ≤ N * (L * (L * σ)) := by
    have h₃ : ‖(ContinuousLinearMap.apply ℝ (ℝ^2) w).comp S‖ ≤ L * σ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
    have h₄ : ‖W.comp ((ContinuousLinearMap.apply ℝ (ℝ^2) w).comp S)‖ ≤ L * (L * σ) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by unfold forcingDerivBound; ring))

/-- The derivative of the forcing in the label: a Hölder term from `D²θ₀` and the second
variation, plus a Lipschitz term from the inverse first variation and `Dθ₀`. -/
theorem norm_labelForcingDeriv_sub_le_add (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {r : ℝ} (hr : r ∈ Icc a b) {y y' : ℝ^2} (hy : 0 ≤ y 1)
    (hy' : 0 ≤ y' 1) :
    ‖labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r -
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y' r‖ ≤
      N * L * (1 + L * η) * ‖y - y'‖ ^ α +
        N * L * σ * (1 + L + 2 * L * σ) * ‖y - y'‖ := by
  set e : ℝ^2 := EuclideanSpace.single 0 1
  set W := variationOn v Dv a b 0 r (flowOn v a b r 0 y)
  set W' := variationOn v Dv a b 0 r (flowOn v a b r 0 y')
  set S := secondVariationOn v Dv D2v a b r 0 y
  set S' := secondVariationOn v Dv D2v a b r 0 y'
  set A := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) y
  set A' := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) y'
  set B := fderiv ℝ (dataTemperature θ₀) y
  set B' := fderiv ℝ (dataTemperature θ₀) y'
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hd0 : 0 ≤ ‖y - y'‖ := norm_nonneg _
  have hp0 : 0 ≤ ‖y - y'‖ ^ α := Real.rpow_nonneg hd0 α
  have hW : ‖W‖ ≤ L := hb.norm_inverse_le h0 hr hy
  have hW' : ‖W'‖ ≤ L := hb.norm_inverse_le h0 hr hy'
  have hWW : ‖W - W'‖ ≤ σ * L * ‖y - y'‖ := hb.norm_inverse_sub_le hv h0 hr hy hy'
  have hve (U : ℝ^2 →L[ℝ] ℝ^2) : ‖U e‖ ≤ ‖U‖ :=
    (U.le_opNorm e).trans_eq (by rw [norm_single_one, mul_one])
  have hw : ‖W e‖ ≤ L := (hve W).trans hW
  have hw' : ‖W' e‖ ≤ L := (hve W').trans hW'
  have hww : ‖W e - W' e‖ ≤ σ * L * ‖y - y'‖ := by
    rw [← sub_apply]; exact (hve _).trans hWW
  have hS : ‖S‖ ≤ σ := hb.norm_secondVariationOn_le r hr 0 h0 y hy
  have hS' : ‖S'‖ ≤ σ := hb.norm_secondVariationOn_le r hr 0 h0 y' hy'
  have hSS : ‖S - S'‖ ≤ η * ‖y - y'‖ ^ α := hb.holder_secondVariationOn r hr 0 h0 y y' hy hy'
  have hA' : ‖A'‖ ≤ N := hd.norm_fderiv_fderiv_dataTemperature_le hy'
  have hAA : ‖A - A'‖ ≤ N * ‖y - y'‖ ^ α := hd.norm_fderiv_fderiv_dataTemperature_sub_le hy hy'
  have hB' : ‖B'‖ ≤ N := hd.norm_fderiv_dataTemperature_le hy'
  have hBB : ‖B - B'‖ ≤ N * ‖y - y'‖ := hd.norm_fderiv_dataTemperature_sub_le hy hy'
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hB'
  have hap (w : ℝ^2) : ‖ContinuousLinearMap.apply ℝ (ℝ^2) w‖ ≤ ‖w‖ := norm_apply_le' w
  have hapR (w : ℝ^2) : ‖ContinuousLinearMap.apply ℝ ℝ w‖ ≤ ‖w‖ := norm_apply_le' w
  -- the first term
  have h₁ : ‖(ContinuousLinearMap.apply ℝ ℝ (W e)).comp A -
      (ContinuousLinearMap.apply ℝ ℝ (W' e)).comp A'‖ ≤
        L * (N * ‖y - y'‖ ^ α) + σ * L * ‖y - y'‖ * N := by
    have heq : (ContinuousLinearMap.apply ℝ ℝ (W e)).comp A -
        (ContinuousLinearMap.apply ℝ ℝ (W' e)).comp A' =
        (ContinuousLinearMap.apply ℝ ℝ (W e)).comp (A - A') +
          (ContinuousLinearMap.apply ℝ ℝ (W e - W' e)).comp A' := by
      rw [map_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    have hq := (hapR (W e)).trans hw
    have hq' := (hapR (W e - W' e)).trans hww
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by gcongr)) ((ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)))
  -- the second term
  have h₂ : ‖B.comp (W.comp ((ContinuousLinearMap.apply ℝ (ℝ^2) (W e)).comp S)) -
      B'.comp (W'.comp ((ContinuousLinearMap.apply ℝ (ℝ^2) (W' e)).comp S'))‖ ≤
        N * ‖y - y'‖ * L * L * σ + N * (σ * L * ‖y - y'‖) * L * σ +
          N * L * (σ * L * ‖y - y'‖) * σ + N * L * L * (η * ‖y - y'‖ ^ α) := by
    refine (norm_comp_comp_comp_sub_le _ _ _ _ _ _ _ _).trans ?_
    have hPP : ‖ContinuousLinearMap.apply ℝ (ℝ^2) (W e) -
        ContinuousLinearMap.apply ℝ (ℝ^2) (W' e)‖ ≤ σ * L * ‖y - y'‖ := by
      rw [← map_sub (ContinuousLinearMap.apply ℝ (ℝ^2) :
        ℝ^2 →L[ℝ] (ℝ^2 →L[ℝ] ℝ^2) →L[ℝ] ℝ^2) (W e) (W' e)]
      exact (hap _).trans hww
    have hP : ‖ContinuousLinearMap.apply ℝ (ℝ^2) (W e)‖ ≤ L := (hap _).trans hw
    have hP' : ‖ContinuousLinearMap.apply ℝ (ℝ^2) (W' e)‖ ≤ L := (hap _).trans hw'
    have hn1 := ContinuousLinearMap.opNorm_nonneg W
    have hn2 := ContinuousLinearMap.opNorm_nonneg (ContinuousLinearMap.apply ℝ (ℝ^2) (W e))
    have hn3 := ContinuousLinearMap.opNorm_nonneg S
    have hn4 := ContinuousLinearMap.opNorm_nonneg B'
    have hn5 := ContinuousLinearMap.opNorm_nonneg W'
    have hn6 := ContinuousLinearMap.opNorm_nonneg (ContinuousLinearMap.apply ℝ (ℝ^2) (W' e))
    gcongr ?_ + ?_ + ?_ + ?_
    · exact mul_le_mul (mul_le_mul (mul_le_mul hBB hW hn1 (by positivity)) hP hn2
        (by positivity)) hS hn3 (by positivity)
    · exact mul_le_mul (mul_le_mul (mul_le_mul hB' hWW (norm_nonneg _) hN0) hP hn2
        (by positivity)) hS hn3 (by positivity)
    · exact mul_le_mul (mul_le_mul (mul_le_mul hB' hW' hn5 hN0) hPP (norm_nonneg _)
        (by positivity)) hS hn3 (by positivity)
    · exact mul_le_mul (mul_le_mul (mul_le_mul hB' hW' hn5 hN0) hP' hn6 (by positivity)) hSS
        (norm_nonneg _) (by positivity)
  have hsplit : labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) e y r -
      labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) e y' r =
      ((ContinuousLinearMap.apply ℝ ℝ (W e)).comp A -
        (ContinuousLinearMap.apply ℝ ℝ (W' e)).comp A') -
      (B.comp (W.comp ((ContinuousLinearMap.apply ℝ (ℝ^2) (W e)).comp S)) -
        B'.comp (W'.comp ((ContinuousLinearMap.apply ℝ (ℝ^2) (W' e)).comp S'))) := by
    simp only [labelForcingDeriv, W, W', S, S', A, A', B, B']
    abel
  rw [hsplit]
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- **The derivative of the forcing is `α`-Hölder in the label** on the closed half-plane, with
the constant `forcingDerivHolderConst N L σ η`. -/
theorem norm_labelForcingDeriv_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {r : ℝ} (hr : r ∈ Icc a b)
    {y y' : ℝ^2} (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    ‖labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r -
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y' r‖ ≤
      forcingDerivHolderConst N L σ η * ‖y - y'‖ ^ α := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hd.norm_fderiv_dataTemperature_le hy)
  have hL0 := hb.zero_le_L h0
  have hη0 := hb.zero_le_η h0
  exact norm_sub_le_add_max_mul_rpow (S := H̄) (by positivity) hα0 hα1
    (fun z hz w hw ↦ hb.norm_labelForcingDeriv_sub_le_add hv h0 hd hr hz hw)
    (fun z hz ↦ hb.norm_labelForcingDeriv_le h0 hd hr hz) hy hy'

end IsBoundedFlowOn

/-! ### The amplitude of a particle -/

/-- The integral over `[0, t] ⊆ [a, b]` of a family jointly continuous on `X × [a, b]` depends
continuously on the parameter. -/
theorem continuous_integral_of_continuousOn {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → ℝ → F} {a b : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (univ ×ˢ Icc a b)) (h0 : (0 : ℝ) ∈ Icc a b)
    {t : ℝ} (ht : t ∈ Icc a b) : Continuous fun y ↦ ∫ r in (0)..t, f y r := by
  have hab : a ≤ b := h0.1.trans h0.2
  have hc : Continuous fun p : X × ℝ ↦ f p.1 (projIcc a b hab p.2) :=
    hf.comp_continuous (continuous_fst.prodMk
      (continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp continuous_snd)))
      fun p ↦ ⟨mem_univ _, (projIcc a b hab p.2).2⟩
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y r ↦ f y (projIcc a b hab r)) hc 0 t (μ := MeasureTheory.volume)
  refine hi.congr fun y ↦ intervalIntegral.integral_congr fun r hr ↦ ?_
  rw [projIcc_of_mem hab (uIcc_subset_Icc h0 ht hr)]

/-- A time slice of a family jointly continuous on `X × [a, b]` is continuous on `[a, b]`. -/
theorem continuousOn_slice_of_continuousOn {X F : Type*} [TopologicalSpace X] [TopologicalSpace F]
    {f : X → ℝ → F} {a b : ℝ} (hf : ContinuousOn (fun p : X × ℝ ↦ f p.1 p.2) (univ ×ˢ Icc a b))
    (y : X) : ContinuousOn (f y) (Icc a b) :=
  hf.comp (continuous_const.prodMk continuous_id : Continuous fun r : ℝ ↦ (y, r)).continuousOn
    fun _ hr ↦ ⟨mem_univ _, hr⟩

/-- The integrals over `[0, s]` and `[0, t]` of a function bounded by `C` on `[a, b]` differ by at
most `C |s - t|`. -/
theorem norm_integral_sub_integral_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b C : ℝ} (hf : ContinuousOn f (Icc a b)) (h0 : (0 : ℝ) ∈ Icc a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hC : ∀ r ∈ Icc a b, ‖f r‖ ≤ C) :
    ‖(∫ r in (0)..s, f r) - ∫ r in (0)..t, f r‖ ≤ C * |s - t| := by
  rw [intervalIntegral.integral_interval_sub_left
    ((hf.mono (uIcc_subset_Icc h0 hs)).intervalIntegrable)
    ((hf.mono (uIcc_subset_Icc h0 ht)).intervalIntegrable)]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦
    hC r (uIcc_subset_Icc ht hs (uIoc_subset_uIcc hr))

namespace IsBoundedFlowOn

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0}
  {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ}

/-- **The amplitude is differentiable in the label**, with derivative
`Dω̃₀ + ∫₀ᵗ DG`. -/
theorem hasFDerivAt_amplitude (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b) (y : ℝ^2) :
    HasFDerivAt (fun z ↦ forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) z t)
      (fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r)
      y :=
  hasFDerivAt_forcedAmplitude
    (G := labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1))
    (DG := labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1))
    (hd.contDiff_dataVorticity.differentiable one_ne_zero)
    (continuousOn_labelForcing hv.toIsC1FieldOn h0
      (hd.contDiff_dataTemperature.of_le (by norm_num)))
    (fun r hr z ↦ hasFDerivAt_labelForcing hv h0 hd.contDiff_dataTemperature hr z)
    (continuousOn_labelForcingDeriv hv h0 hd.contDiff_dataTemperature) h0 ht y

/-- **The amplitude is `C¹` in the label** at every time of `[a, b]`. -/
theorem contDiff_amplitude (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 1 (fun z ↦ forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) z t) := by
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨_, ?_, fun y ↦ hasFDerivAt_amplitude hv h0 hd ht y⟩
  exact (hd.contDiff_dataVorticity.continuous_fderiv one_ne_zero).add
    (continuous_integral_of_continuousOn
      (f := labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1))
      (continuousOn_labelForcingDeriv hv h0 hd.contDiff_dataTemperature) h0 ht)

/-- The amplitude is bounded by `N + |t| N L` on the closed half-plane. -/
theorem abs_amplitude_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y t| ≤
      N + |t| * (N * L) := by
  rw [forcedAmplitude]
  refine (abs_add_le _ _).trans (add_le_add (hd.abs_dataVorticity_le hy) ?_)
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_).trans_eq
    (by rw [sub_zero, mul_comm])
  rw [Real.norm_eq_abs]
  exact hb.abs_labelForcing_le h0 hd (uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)) hy

/-- **The derivative of the amplitude in the label is at most `N + |t| c₀`** on the closed
half-plane, `c₀ = forcingDerivBound N L σ`. -/
theorem norm_fderiv_amplitude_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r‖ ≤
      N + |t| * forcingDerivBound N L σ := by
  refine (norm_add_le _ _).trans (add_le_add (hd.norm_fderiv_dataVorticity_le hy) ?_)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_).trans_eq
    (by rw [sub_zero, mul_comm])
  exact hb.norm_labelForcingDeriv_le h0 hd (uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)) hy

/-- **The derivative of the amplitude in the label is `α`-Hölder** on the closed half-plane with
constant `N + |t| c_α`, `c_α = forcingDerivHolderConst N L σ η`. -/
theorem norm_fderiv_amplitude_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {t : ℝ} (ht : t ∈ Icc a b)
    {y y' : ℝ^2} (hy : 0 ≤ y 1) (hy' : 0 ≤ y' 1) :
    ‖(fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r) -
      (fderiv ℝ (dataVorticity ω₀) y' + ∫ r in (0)..t,
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y' r)‖ ≤
      (N + |t| * forcingDerivHolderConst N L σ η) * ‖y - y'‖ ^ α := by
  set G := labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)
  have hGc : ContinuousOn (fun p : ℝ^2 × ℝ ↦ G p.1 p.2) (univ ×ˢ Icc a b) :=
    continuousOn_labelForcingDeriv hv h0 hd.contDiff_dataTemperature
  have hGr (z : ℝ^2) : IntervalIntegrable (G z) MeasureTheory.volume 0 t :=
    ((hGc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun r hr ↦ ⟨mem_univ _, hr⟩).mono (uIcc_subset_Icc h0 ht)).intervalIntegrable
  have hsplit : (fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t, G y r) -
      (fderiv ℝ (dataVorticity ω₀) y' + ∫ r in (0)..t, G y' r) =
      (fderiv ℝ (dataVorticity ω₀) y - fderiv ℝ (dataVorticity ω₀) y') +
        ∫ r in (0)..t, (G y r - G y' r) := by
    rw [intervalIntegral.integral_sub (hGr y) (hGr y')]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hI : ‖∫ r in (0)..t, (G y r - G y' r)‖ ≤
      forcingDerivHolderConst N L σ η * ‖y - y'‖ ^ α * |t| :=
    (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦
      hb.norm_labelForcingDeriv_sub_le hv h0 hd hα0 hα1
        (uIcc_subset_Icc h0 ht (uIoc_subset_uIcc hr)) hy hy').trans_eq (by rw [sub_zero])
  calc _ ≤ N * ‖y - y'‖ ^ α + forcingDerivHolderConst N L σ η * ‖y - y'‖ ^ α * |t| :=
        add_le_add (hd.norm_fderiv_dataVorticity_sub_le hy hy') hI
    _ = _ := by ring

/-- **The amplitude is Lipschitz in the label** on the closed half-plane with constant
`N + |t| c₀`. -/
theorem abs_amplitude_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b) {y y' : ℝ^2} (hy : 0 ≤ y 1)
    (hy' : 0 ≤ y' 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y t -
      forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y' t| ≤
      (N + |t| * forcingDerivBound N L σ) * ‖y - y'‖ := by
  rw [← Real.norm_eq_abs]
  exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ (hasFDerivAt_amplitude hv h0 hd ht z).hasFDerivWithinAt)
    (fun z hz ↦ hb.norm_fderiv_amplitude_le h0 hd ht hz) hy' hy

/-- The amplitude is Lipschitz in time with constant `N L` on the closed half-plane. -/
theorem abs_amplitude_time_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    |forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y s -
      forcedAmplitude (dataVorticity ω₀)
        (labelForcing v Dv a b (dataTemperature θ₀) (EuclideanSpace.single 0 1)) y t| ≤
      N * L * |s - t| := by
  have hGc := continuousOn_labelForcing (e := EuclideanSpace.single 0 1) hv.toIsC1FieldOn h0
    (hd.contDiff_dataTemperature.of_le (by norm_num))
  have hGy := continuousOn_slice_of_continuousOn hGc y
  have h := norm_integral_sub_integral_le hGy h0 hs ht fun r hr ↦ by
    rw [Real.norm_eq_abs]; exact hb.abs_labelForcing_le h0 hd hr hy
  rw [Real.norm_eq_abs] at h
  unfold forcedAmplitude
  rwa [add_sub_add_left_eq_sub]

/-- The derivative of the amplitude in the label is Lipschitz in time with constant `c₀` on the
closed half-plane. -/
theorem norm_fderiv_amplitude_time_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖(fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..s,
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r) -
      (fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
        labelForcingDeriv v Dv D2v a b (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r)‖ ≤
      forcingDerivBound N L σ * |s - t| := by
  have hGc := continuousOn_labelForcingDeriv (e := EuclideanSpace.single 0 1) hv h0
    hd.contDiff_dataTemperature
  have hGy := continuousOn_slice_of_continuousOn hGc y
  have h := norm_integral_sub_integral_le hGy h0 hs ht fun r hr ↦
    hb.norm_labelForcingDeriv_le h0 hd hr hy
  refine le_of_eq_of_le ?_ h
  congr 1
  abel

end IsBoundedFlowOn

end Boussinesq.HalfPlane
