/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Field
public import PDE.Fluid.HalfPlaneSystem.Forcing
public import PDE.Fluid.Boussinesq.HalfPlane.CarriedFields

/-!
# The vorticity carried by the flow of a field with the weighted forcing

If the velocity field of a half-plane system is frozen, the two transport equations are linear and
can be solved along the particle trajectories. This module defines the temperature and the vorticity
that a given field carries from the data and bounds them on the closed half-plane in terms of the
bounds of the flow. The carried vorticity is the map whose fixed point is a solution.

A field `v` on the times `[a, b]` carries the temperature `carriedTemperature θ₀ v a b x t = θ̃₀(Y)`
and the vorticity
`carriedVorticity κ ω₀ θ₀ v Dv a b x t = ω̃₀(Y) + ∫₀ᵗ κ(X(r, Y)) ∂₀θ(X(r, Y), r) dr` at the label
`Y` of the particle at `x` at time `t`, with the forcing in label form (`weightedForcing`); here
`ω̃₀`, `θ̃₀` are the data extended across the boundary. For the field of a vorticity history under a
velocity law the carried vorticity is the iteration map `carriedHistory U κ ω₀ θ₀ a b` of the local
existence proof. The definitions take a general field and coefficient; the library has the carried
fields of the Biot-Savart law with `κ = 1` in `Boussinesq.HalfPlane.carriedVorticity`.

The spatial derivative of the carried vorticity is the derivative of the amplitude in the label
composed with the first variation of the label map (`hasFDerivAt_carriedVorticity`). Its bound and
its Hölder constant follow from the bounds of the weighted forcing and of the flow, and the
continuity in time from the Lipschitz dependence of the label on the time. The bounds assume the
flow bounds `Boussinesq.HalfPlane.IsBoundedFlowOn` (constants `V`, `K₁`, `L`, `δ`, `σ`, `η`) and
data of the class `Boussinesq.HalfPlane.IsHolderData … α R N`; `Iteration.lean` proves the flow
bounds for the field of a `C^{1,α}` history.

## Main results

* `carriedTemperature`, `carriedVorticity`, `carriedHistory`: the carried fields and the iteration
  map; `carriedVorticity_zero`, `carriedTemperature_zero`: they start from the extended data.
* `abs_carriedVorticity_le`: `|ω(x, t)| ≤ N + |t| Bκ₀ N L`.
* `hasFDerivAt_carriedVorticity`, `contDiff_carriedVorticity`, `fderivWithin_carriedVorticity`: the
  spatial derivative, and `C¹` regularity in space for a `C²` field.
* `norm_fderiv_carriedVorticity_le`, `norm_fderiv_carriedVorticity_sub_le`: the bound and the Hölder
  constant of the spatial derivative.
* `carried_eq_zero`: the supports grow by at most `V` times the elapsed time.
* `exists_abs_carriedVorticity_sub_le`, `exists_norm_fderiv_carriedVorticity_sub_le`: continuity in
  time uniformly on the closed half-plane, of the vorticity and of its spatial derivative.

`Iteration.lean` shows that the iteration map keeps a class of histories, `Convergence.lean` proves
its difference estimate, and `Solution.lean` shows that its fixed point is a solution.
`CarriedTemperature.lean` bounds the carried temperature, and `CarriedHigher.lean` and
`CarriedHigherForcing.lean` the derivatives of higher order.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The temperature carried by the flow of `v` on the times `[a, b]`: the extended datum at the
label of the particle at `x` at time `t`. -/
def carriedTemperature (θ₀ : ℝ^2 → ℝ) (v : ℝ → ℝ^2 → ℝ^2) (a b : ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  dataTemperature θ₀ (flowOn v a b 0 t x)

/-- The vorticity carried by the flow of `v` on the times `[a, b]` with the weighted forcing
`κ ∂₀θ` in label form: `ω̃₀(Y) + ∫₀ᵗ G_κ(Y, r) dr` at the label `Y` of `(x, t)`. -/
def carriedVorticity (κ ω₀ θ₀ : ℝ^2 → ℝ) (v : ℝ → ℝ^2 → ℝ^2)
    (Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2) (a b : ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  forcedAmplitude (dataVorticity ω₀)
    (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1))
    (flowOn v a b 0 t x) t

/-- The iteration map of the local existence proof on the times `[a, b]`: the vorticity carried
by the field of the history `ω` under the velocity law `U`, as a history. -/
def carriedHistory (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (κ ω₀ θ₀ : ℝ^2 → ℝ) (a b : ℝ)
    (ω : ℝ → ℝ^2 → ℝ) : ℝ → ℝ^2 → ℝ :=
  fun t x ↦ carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) a b x t

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0}
  {κ ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} {Bκ : ℕ → ℝ}

/-- At time zero the carried vorticity is the extended datum. -/
theorem carriedVorticity_zero (κ ω₀ θ₀ : ℝ^2 → ℝ) (hv : IsLipschitzFieldOn v a b K)
    (h0 : (0 : ℝ) ∈ Icc a b) (x : ℝ^2) :
    carriedVorticity κ ω₀ θ₀ v Dv a b x 0 = dataVorticity ω₀ x := by
  simp [carriedVorticity, forcedAmplitude, hv.flowOn_self h0]

/-- At time zero the carried temperature is the extended datum. -/
theorem carriedTemperature_zero (θ₀ : ℝ^2 → ℝ) (hv : IsLipschitzFieldOn v a b K)
    (h0 : (0 : ℝ) ∈ Icc a b) (x : ℝ^2) :
    carriedTemperature θ₀ v a b x 0 = dataTemperature θ₀ x := by
  simp [carriedTemperature, hv.flowOn_self h0]

/-- **The carried vorticity is bounded** by `N + |t| Bκ₀ N L` on the closed half-plane. -/
theorem abs_carriedVorticity_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity κ ω₀ θ₀ v Dv a b x t| ≤ N + |t| * weightedForcingBound Bκ N L :=
  hb.abs_weightedAmplitude_le h0 hd hκ ht (hb.flowOn_mem h0 ht hx)

/-- The spatial derivative of the carried vorticity: the derivative of the amplitude at the
label composed with the first variation of the label map. -/
theorem hasFDerivAt_carriedVorticity (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ^2) :
    HasFDerivAt (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t)
      ((fderiv ℝ (dataVorticity ω₀) (flowOn v a b 0 t x) + ∫ r in (0)..t,
        weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
          (flowOn v a b 0 t x) r).comp (variationOn v Dv a b 0 t x)) x :=
  (hasFDerivAt_weightedAmplitude hv h0 hd hκ ht _).comp x
    (hv.toIsC1FieldOn.hasFDerivAt_flowOn h0 ht x)

/-- The carried vorticity is `C¹` in space at every time of `[a, b]`. -/
theorem contDiff_carriedVorticity (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 1 (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) :=
  (contDiff_weightedAmplitude hv h0 hd hκ ht).comp ((hv.contDiff_flowOn h0 ht).of_le (by norm_num))

/-- On the closed half-plane the derivative within the closed half-plane of the carried
vorticity is its derivative. -/
theorem fderivWithin_carriedVorticity (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) H̄ x =
      fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) x :=
  ((hasFDerivAt_carriedVorticity hv h0 hd hκ ht x).differentiableAt).fderivWithin
    (uniqueDiffOn_closedUpper x hx)

/-- **The spatial derivative of the carried vorticity is bounded** by `(N + |t| c₀) L` on the
closed half-plane, `c₀ = weightedForcingDerivBound Bκ N L σ`. -/
theorem norm_fderiv_carriedVorticity_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) {t : ℝ} (ht : t ∈ Icc a b)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) x‖ ≤
      (N + |t| * weightedForcingDerivBound Bκ N L σ) * L := by
  rw [(hasFDerivAt_carriedVorticity hv h0 hd hκ ht x).fderiv]
  have hA := hb.norm_fderiv_weightedAmplitude_le h0 hd hκ ht (hb.flowOn_mem h0 ht hx)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hA
    (hb.norm_variationOn_le 0 h0 t ht x hx) (norm_nonneg _) ((norm_nonneg _).trans hA))

/-- **The spatial derivative of the carried vorticity is `α`-Hölder** on the closed half-plane,
with constant `(N + |t| c_α) L ^ α L + (N + |t| c₀) max σ (2 δ)`. It is the top-order bound that
keeps the iteration map in a class of `C^{1,α}` histories. Proof: the derivative is `A(Y) ∘ J`,
with `A` the derivative of the amplitude at the label `Y` and `J` the first variation of the
label map; `A` is Hölder in the label, the label is Lipschitz in `x`, and `J` is Hölder in `x`. -/
theorem norm_fderiv_carriedVorticity_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {t : ℝ} (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) x -
        fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) x'‖ ≤
      ((N + |t| * weightedForcingDerivHolderConst Bκ N L σ η) * L ^ α * L +
        (N + |t| * weightedForcingDerivBound Bκ N L σ) * max σ (2 * δ)) * ‖x - x'‖ ^ α := by
  set A := fun y ↦ fderiv ℝ (dataVorticity ω₀) y + ∫ r in (0)..t,
    weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1) y r
  set Y := flowOn v a b 0 t x
  set Y' := flowOn v a b 0 t x'
  set J := variationOn v Dv a b 0 t x
  set J' := variationOn v Dv a b 0 t x'
  have hY : 0 ≤ Y 1 := hb.flowOn_mem h0 ht hx
  have hY' : 0 ≤ Y' 1 := hb.flowOn_mem h0 ht hx'
  have hL0 := hb.zero_le_L h0
  have hd0 : 0 ≤ ‖x - x'‖ := norm_nonneg _
  rw [(hasFDerivAt_carriedVorticity hv h0 hd hκ ht x).fderiv,
    (hasFDerivAt_carriedVorticity hv h0 hd hκ ht x').fderiv]
  change ‖(A Y).comp J - (A Y').comp J'‖ ≤ _
  -- Split the difference of the products: a difference of amplitudes and a difference of
  -- first variations.
  have hsplit : (A Y).comp J - (A Y').comp J' = (A Y - A Y').comp J + (A Y').comp (J - J') := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  have hAA : ‖A Y - A Y'‖ ≤
      (N + |t| * weightedForcingDerivHolderConst Bκ N L σ η) * ‖Y - Y'‖ ^ α :=
    hb.norm_fderiv_weightedAmplitude_sub_le hv h0 hd hκ hα0 hα1 ht hY hY'
  have hYY : ‖Y - Y'‖ ^ α ≤ L ^ α * ‖x - x'‖ ^ α := by
    rw [← Real.mul_rpow hL0 hd0]
    exact Real.rpow_le_rpow (norm_nonneg _)
      (hb.norm_flowOn_sub_le hv.toIsC1FieldOn h0 ht hx hx') hα0
  have hA' : ‖A Y'‖ ≤ N + |t| * weightedForcingDerivBound Bκ N L σ :=
    hb.norm_fderiv_weightedAmplitude_le h0 hd hκ ht hY'
  have hJJ : ‖J - J'‖ ≤ max σ (2 * δ) * ‖x - x'‖ ^ α :=
    hb.norm_variationOn_sub_le_rpow hv hα0 hα1 h0 ht hx hx'
  have hJ : ‖J‖ ≤ L := hb.norm_variationOn_le 0 h0 t ht x hx
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hd.norm_fderiv_dataVorticity_le hx)
  have hcα : 0 ≤ N + |t| * weightedForcingDerivHolderConst Bκ N L σ η :=
    add_nonneg hN0 (mul_nonneg (abs_nonneg t) (weightedForcingDerivHolderConst_nonneg hκ hN0 hL0
      (hb.zero_le_σ h0) (hb.zero_le_η h0)))
  calc ‖(A Y - A Y').comp J + (A Y').comp (J - J')‖
      ≤ ‖A Y - A Y'‖ * ‖J‖ + ‖A Y'‖ * ‖J - J'‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _))
    _ ≤ ((N + |t| * weightedForcingDerivHolderConst Bκ N L σ η) * (L ^ α * ‖x - x'‖ ^ α)) * L +
        (N + |t| * weightedForcingDerivBound Bκ N L σ) * (max σ (2 * δ) * ‖x - x'‖ ^ α) := by
        refine add_le_add (mul_le_mul (hAA.trans (mul_le_mul_of_nonneg_left hYY hcα)) hJ
          (norm_nonneg _) (mul_nonneg hcα (mul_nonneg (Real.rpow_nonneg hL0 α)
            (Real.rpow_nonneg hd0 α)))) (mul_le_mul hA' hJJ (norm_nonneg _)
          ((norm_nonneg _).trans hA'))
    _ = _ := by ring

/-- **Support of the carried fields.** At a time `t` with `|t| ≤ τ` the carried vorticity and
the carried temperature vanish on the closed half-plane outside the disc of radius `R + V τ`.
Proof: the label of such a point lies outside the support disc of the data, because a particle
moves by at most `V |t|`; there the data and the forcing vanish. -/
theorem carried_eq_zero (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {τ t : ℝ} (ht : t ∈ Icc a b) (htτ : |t| ≤ τ) {x : ℝ^2}
    (hx : 0 ≤ x 1) (hxR : R + V * τ < ‖x‖) :
    carriedVorticity κ ω₀ θ₀ v Dv a b x t = 0 ∧ carriedTemperature θ₀ v a b x t = 0 := by
  set Y := flowOn v a b 0 t x
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
  rw [carriedVorticity, forcedAmplitude, hω, zero_add]
  have hG : ∀ r, weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1)
      Y r = 0 := fun r ↦ by
    rw [weightedForcing, labelForcing, hd.fderiv_dataTemperature_eq_zero hY hYR, zero_apply,
      mul_zero]
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r _ ↦ hG r,
    intervalIntegral.integral_zero]

/-- The carried vorticity is Lipschitz in time on the closed half-plane. -/
theorem abs_carriedVorticity_time_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedVorticity κ ω₀ θ₀ v Dv a b x s - carriedVorticity κ ω₀ θ₀ v Dv a b x t| ≤
      (N + |s| * weightedForcingDerivBound Bκ N L σ) * (L * (V * |s - t|)) +
        weightedForcingBound Bκ N L * |s - t| := by
  set Ys := flowOn v a b 0 s x
  set Yt := flowOn v a b 0 t x
  have hYs : 0 ≤ Ys 1 := hb.flowOn_mem h0 hs hx
  have hYt : 0 ≤ Yt 1 := hb.flowOn_mem h0 ht hx
  rw [carriedVorticity, carriedVorticity]
  set Ω := forcedAmplitude (dataVorticity ω₀)
    (weightedForcing v Dv a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1))
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have h₁ : |Ω Ys s - Ω Yt s| ≤
      (N + |s| * weightedForcingDerivBound Bκ N L σ) * (L * (V * |s - t|)) := by
    refine (hb.abs_weightedAmplitude_sub_le hv h0 hd hκ hs hYs hYt).trans
      (mul_le_mul_of_nonneg_left (hb.norm_label_sub_le hv.toIsC1FieldOn h0 hs ht hx) ?_)
    exact add_nonneg hN0 (mul_nonneg (abs_nonneg s)
      (weightedForcingDerivBound_nonneg hκ hN0 (hb.zero_le_L h0) (hb.zero_le_σ h0)))
  have h₂ : |Ω Yt s - Ω Yt t| ≤ weightedForcingBound Bκ N L * |s - t| :=
    hb.abs_weightedAmplitude_time_sub_le hv h0 hd hκ hs ht hYt
  calc |Ω Ys s - Ω Yt t| = |(Ω Ys s - Ω Yt s) + (Ω Yt s - Ω Yt t)| := by ring_nf
    _ ≤ |Ω Ys s - Ω Yt s| + |Ω Yt s - Ω Yt t| := abs_add_le _ _
    _ ≤ _ := add_le_add h₁ h₂

/-- **Continuity in time of the carried vorticity**, uniformly on the closed half-plane. -/
theorem exists_abs_carriedVorticity_sub_le (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) {t : ℝ}
    (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ' > 0, ∀ s ∈ Icc a b, |s - t| < δ' → ∀ x : ℝ^2, 0 ≤ x 1 →
      |carriedVorticity κ ω₀ θ₀ v Dv a b x s - carriedVorticity κ ω₀ θ₀ v Dv a b x t| ≤ ε := by
  set τ := |a| + |b|
  set c := (N + τ * weightedForcingDerivBound Bκ N L σ) * (L * V) + weightedForcingBound Bκ N L
  have hm : ContinuousAt (fun h : ℝ ↦ c * |h|) 0 := by fun_prop
  obtain ⟨δ', hδ', hδ'ε⟩ := IsBoundedFlowOn.exists_forall_le_of_continuousAt hm (by simp) hε
  refine ⟨δ', hδ', fun s hs hst x hx ↦ ?_⟩
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have hL0 := hb.zero_le_L h0
  have hc₀ := weightedForcingDerivBound_nonneg hκ hN0 hL0 (hb.zero_le_σ h0)
  have hsτ : |s| ≤ τ := IsBoundedFlowOn.abs_le_add_abs_of_mem_Icc hs
  refine (abs_carriedVorticity_time_sub_le hb hv h0 hd hκ hs ht hx).trans
    (le_trans ?_ (hδ'ε (s - t) hst))
  have hV0 := hb.zero_le_V h0
  have h1 : (N + |s| * weightedForcingDerivBound Bκ N L σ) ≤
      N + τ * weightedForcingDerivBound Bκ N L σ := by
    gcongr
  calc (N + |s| * weightedForcingDerivBound Bκ N L σ) * (L * (V * |s - t|)) +
        weightedForcingBound Bκ N L * |s - t|
      ≤ (N + τ * weightedForcingDerivBound Bκ N L σ) * (L * (V * |s - t|)) +
        weightedForcingBound Bκ N L * |s - t| := by
        gcongr
    _ = c * |s - t| := by ring

/-- The spatial derivative of the carried vorticity moves continuously in time, with an explicit
modulus, on the closed half-plane. -/
theorem norm_fderiv_carriedVorticity_time_sub_le
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    ‖fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z s) x -
        fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) x‖ ≤
      (N + |s| * weightedForcingDerivHolderConst Bκ N L σ η) * (L * (V * |s - t|)) ^ α * L +
        weightedForcingDerivBound Bκ N L σ * |s - t| * L +
        (N + |t| * weightedForcingDerivBound Bκ N L σ) *
          (σ * (V * |s - t|) * L + L * (Real.exp (K₁ * |s - t|) - 1)) := by
  set A := fun (r : ℝ) (y : ℝ^2) ↦ fderiv ℝ (dataVorticity ω₀) y + ∫ q in (0)..r,
    weightedForcingDeriv v Dv D2v a b κ (dataTemperature θ₀) (EuclideanSpace.single 0 1) y q
  set Ys := flowOn v a b 0 s x
  set Yt := flowOn v a b 0 t x
  set Js := variationOn v Dv a b 0 s x
  set Jt := variationOn v Dv a b 0 t x
  have hYs : 0 ≤ Ys 1 := hb.flowOn_mem h0 hs hx
  have hYt : 0 ≤ Yt 1 := hb.flowOn_mem h0 ht hx
  have hL0 := hb.zero_le_L h0
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have hσ0 := hb.zero_le_σ h0
  have hc₀ := weightedForcingDerivBound_nonneg hκ hN0 hL0 hσ0
  have hcα := weightedForcingDerivHolderConst_nonneg hκ hN0 hL0 hσ0 (hb.zero_le_η h0)
  rw [(hasFDerivAt_carriedVorticity hv h0 hd hκ hs x).fderiv,
    (hasFDerivAt_carriedVorticity hv h0 hd hκ ht x).fderiv]
  change ‖(A s Ys).comp Js - (A t Yt).comp Jt‖ ≤ _
  have hsplit : (A s Ys).comp Js - (A t Yt).comp Jt =
      (A s Ys - A s Yt).comp Js + (A s Yt - A t Yt).comp Js + (A t Yt).comp (Js - Jt) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  have hJs : ‖Js‖ ≤ L := hb.norm_variationOn_le 0 h0 s hs x hx
  have h₁ : ‖A s Ys - A s Yt‖ ≤
      (N + |s| * weightedForcingDerivHolderConst Bκ N L σ η) * (L * (V * |s - t|)) ^ α :=
    (hb.norm_fderiv_weightedAmplitude_sub_le hv h0 hd hκ hα0 hα1 hs hYs hYt).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
        (hb.norm_label_sub_le hv.toIsC1FieldOn h0 hs ht hx) hα0)
        (add_nonneg hN0 (mul_nonneg (abs_nonneg s) hcα)))
  have h₂ : ‖A s Yt - A t Yt‖ ≤ weightedForcingDerivBound Bκ N L σ * |s - t| :=
    hb.norm_fderiv_weightedAmplitude_time_sub_le hv h0 hd hκ hs ht hYt
  have h₃ : ‖A t Yt‖ ≤ N + |t| * weightedForcingDerivBound Bκ N L σ :=
    hb.norm_fderiv_weightedAmplitude_le h0 hd hκ ht hYt
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
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η) (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ' > 0, ∀ s ∈ Icc a b, |s - t| < δ' → ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z s) x -
        fderiv ℝ (fun z ↦ carriedVorticity κ ω₀ θ₀ v Dv a b z t) x‖ ≤ ε := by
  set τ := |a| + |b|
  set cα := N + τ * weightedForcingDerivHolderConst Bκ N L σ η
  set c₀ := N + τ * weightedForcingDerivBound Bκ N L σ
  set m : ℝ → ℝ := fun h ↦ cα * (L * (V * |h|)) ^ α * L +
    weightedForcingDerivBound Bκ N L σ * |h| * L +
    c₀ * (σ * (V * |h|) * L + L * (Real.exp (K₁ * |h|) - 1))
  have hm : ContinuousAt m 0 := by
    have hr : Continuous fun h : ℝ ↦ (L * (V * |h|)) ^ α :=
      (Real.continuous_rpow_const hα0.le).comp (by fun_prop)
    exact (((continuous_const.mul hr).mul continuous_const).add (by fun_prop)).add
      (by fun_prop) |>.continuousAt
  have hm0 : m 0 = 0 := by simp [m, Real.zero_rpow hα0.ne']
  obtain ⟨δ', hδ', hδ'ε⟩ := IsBoundedFlowOn.exists_forall_le_of_continuousAt hm hm0 hε
  refine ⟨δ', hδ', fun s hs hst x hx ↦ ?_⟩
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_dataVorticity_le hx)
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hc₀ := weightedForcingDerivBound_nonneg hκ hN0 hL0 hσ0
  have hcα := weightedForcingDerivHolderConst_nonneg hκ hN0 hL0 hσ0 (hb.zero_le_η h0)
  have hτ (r : ℝ) (hr : r ∈ Icc a b) : |r| ≤ τ := IsBoundedFlowOn.abs_le_add_abs_of_mem_Icc hr
  refine (norm_fderiv_carriedVorticity_time_sub_le hb hv h0 hd hκ hα0.le hα1 hs ht hx).trans
    (le_trans ?_ (hδ'ε (s - t) hst))
  have hK₁ := hb.zero_le_K₁ h0
  have hV0 := hb.zero_le_V h0
  have hexp : 0 ≤ Real.exp (K₁ * |s - t|) - 1 := by
    have := Real.add_one_le_exp (K₁ * |s - t|)
    nlinarith [mul_nonneg hK₁ (abs_nonneg (s - t))]
  have hp : 0 ≤ (L * (V * |s - t|)) ^ α := Real.rpow_nonneg (by positivity) α
  have h1 : N + |s| * weightedForcingDerivHolderConst Bκ N L σ η ≤ cα :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (hτ s hs) hcα)
  have h2 : N + |t| * weightedForcingDerivBound Bκ N L σ ≤ c₀ :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (hτ t ht) hc₀)
  simp only [m]
  gcongr

end HalfPlaneSystem
