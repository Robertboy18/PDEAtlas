/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.CarriedVorticity

/-!
# Bounds of the carried temperature

The temperature of a half-plane system is transported without forcing, so for a frozen velocity
field it is the datum at the label of the particle: `θ̃₀(Y)` at the label `Y`. The vorticity
equation is forced by a derivative of the temperature, so its bounds are needed one order above the
vorticity. This module bounds the first and second spatial derivatives of the carried temperature
and the Hölder constant of the second, in terms of the bounds of the flow.

On the closed half-plane, for a `C²` field with the flow bounds
`Boussinesq.HalfPlane.IsBoundedFlowOn` (constants `L`, `σ`, `η` of the first variation, the second
variation and its Hölder constant) and data of the class
`Boussinesq.HalfPlane.IsHolderData … α R N`, the carried temperature is at most `N`, its derivative
at most `N L`, its second derivative `Dθ̃₀(Y) D²Y + D²θ̃₀(Y)[DY, DY]` at most `N σ + N L²` and
`α`-Hölder. The chain rule gives the two derivatives. In the difference of the second derivatives at
two points every term has one factor that is a difference: of the derivatives of the datum at the
two labels, of the first variations or of the second variations. The second variation is `α`-Hölder
with constant `η`; the other differences are Lipschitz, and a Lipschitz bound together with the
bound of the size gives a Hölder bound.

## Main results

* `contDiff_carriedTemperature`: the carried temperature is `C²` in space at every time.
* `hasFDerivAt_carriedTemperature`, `fderiv_fderiv_carriedTemperature_apply`: the first and the
  second spatial derivative by the chain rule.
* `carriedTemperature_bounds`: `|θ| ≤ N`, `‖Dθ‖ ≤ N L`, `‖D²θ‖ ≤ N σ + N L²`.
* `norm_fderiv_fderiv_carriedTemperature_sub_le`: `D²θ` is `α`-Hölder with constant
  `N η + N L^α L² + max (3 N L σ) (2 (N σ + N L²))`, for `α ∈ [0, 1]`;
  `norm_fderiv_fderiv_carriedTemperature_sub_le_add` is the bound by a Hölder term plus a Lipschitz
  term.

`Iteration.lean` uses these bounds in the proof that the iteration map keeps the class of `C^{1,α}`
histories and that the carried temperature has `C^{2,α}` slices; `CarriedHigherForcing.lean` has the
bounds of the derivatives of higher order.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

variable {v : ℝ → ℝ^2 → ℝ^2} {Dv : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {a b α V K₁ L δ σ η : ℝ} {K K₂ : ℝ≥0}
  {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ}

/-- The carried temperature is `C²` in space at every time of `[a, b]`. -/
theorem contDiff_carriedTemperature (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 2 (fun z ↦ carriedTemperature θ₀ v a b z t) :=
  contDiff_comp_flowOn hv h0 hd.contDiff_dataTemperature ht

/-- The spatial derivative of the carried temperature. -/
theorem hasFDerivAt_carriedTemperature (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ^2) :
    HasFDerivAt (fun z ↦ carriedTemperature θ₀ v a b z t)
      ((fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t x)).comp
        (variationOn v Dv a b 0 t x)) x :=
  hasFDerivAt_comp_flowOn hv h0 (hd.contDiff_dataTemperature.differentiable two_ne_zero) ht x

/-- The second spatial derivative of the carried temperature applied to `h` and `k`:
`Dθ₀(Y) (D²Y h k) + D²θ₀(Y) (DY h) (DY k)` at the label `Y`. -/
theorem fderiv_fderiv_carriedTemperature_apply (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    (x h k : ℝ^2) :
    fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x h k =
      fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t x)
          (secondVariationOn v Dv D2v a b 0
            t x h k) +
        fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn v a b 0 t x)
          (variationOn v Dv a b 0 t x h)
          (variationOn v Dv a b 0 t x k) := by
  have hv1 := hv.toIsC1FieldOn
  have hθ := hd.contDiff_dataTemperature
  have hD : Differentiable ℝ (fderiv ℝ (dataTemperature θ₀)) :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hfun : fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t) = fun z ↦
      (fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t z)).comp
        (variationOn v Dv a b 0 t z) :=
    funext fun z ↦ (hasFDerivAt_carriedTemperature hv1 h0 hd ht z).fderiv
  have hc : HasFDerivAt (fun z ↦ fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t z))
      ((fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn v a b 0 t x)).comp
        (variationOn v Dv a b 0 t x)) x :=
    (hD _).hasFDerivAt.comp x (hv1.hasFDerivAt_flowOn h0 ht x)
  have hJ := hv.hasFDerivAt_variationOn h0 ht x
  rw [hfun, (hc.clm_comp hJ).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

/-- **Bounds of the carried temperature** on the closed half-plane: the value is at most `N`, the
derivative at most `N L` and the second derivative at most `N σ + N L ^ 2`. Proof: the chain
rule for `θ̃₀(Y)`, with the bounds `N` of the datum and its derivatives, `L` of the first
variation of the label map and `σ` of its second variation. -/
theorem carriedTemperature_bounds
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) {t : ℝ} (ht : t ∈ Icc a b)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedTemperature θ₀ v a b x t| ≤ N ∧
      ‖fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t) x‖ ≤ N * L ∧
      ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x‖ ≤
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
    set J := variationOn v Dv a b 0 t x
    set S := secondVariationOn v Dv D2v a b
      0 t x
    set B := fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t x)
    set A := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn v a b 0 t x)
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
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) {t : ℝ}
    (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x -
        fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x'‖ ≤
      (N * η + N * L ^ α * L ^ 2) * ‖x - x'‖ ^ α + 3 * N * L * σ * ‖x - x'‖ := by
  have hY := hb.flowOn_mem h0 ht hx
  have hY' := hb.flowOn_mem h0 ht hx'
  have hL0 := hb.zero_le_L h0
  have hσ0 := hb.zero_le_σ h0
  have hη0 := hb.zero_le_η h0
  set J := variationOn v Dv a b 0 t x
  set J' := variationOn v Dv a b 0 t x'
  set S := secondVariationOn v Dv D2v a b
    0 t x
  set S' := secondVariationOn v Dv D2v a b
    0 t x'
  set B := fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t x)
  set B' := fderiv ℝ (dataTemperature θ₀) (flowOn v a b 0 t x')
  set A := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn v a b 0 t x)
  set A' := fderiv ℝ (fderiv ℝ (dataTemperature θ₀)) (flowOn v a b 0 t x')
  set d := ‖x - x'‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hp0 : 0 ≤ d ^ α := Real.rpow_nonneg hd0 α
  have hYY : ‖flowOn v a b 0 t x - flowOn v a b 0 t x'‖ ≤ L * d :=
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
  -- Split the difference into five terms, each with one factor that is a difference: of the
  -- derivatives of the datum at the two labels, of the second variations, or of the first
  -- variations.
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
with constant `N η + N L ^ α L ^ 2 + max (3 N L σ) (2 (N σ + N L ^ 2))`. It gives the `C^{2,α}`
regularity of the temperature of the iteration. Proof: the difference is at most a Hölder term
plus a Lipschitz term, and it is at most twice the bound of the size; the two bounds of the
second part combine to a Hölder bound. -/
theorem norm_fderiv_fderiv_carriedTemperature_sub_le
    (hb : IsBoundedFlowOn v Dv D2v a b α V K₁ L δ σ η)
    (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {t : ℝ} (ht : t ∈ Icc a b) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x -
        fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x'‖ ≤
      (N * η + N * L ^ α * L ^ 2 + max (3 * N * L * σ) (2 * (N * σ + N * L ^ 2))) *
        ‖x - x'‖ ^ α := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans
    (hd.norm_fderiv_dataTemperature_le (hb.flowOn_mem h0 ht hx))
  have hL0 := hb.zero_le_L h0
  have hη0 := hb.zero_le_η h0
  have hσ0 := hb.zero_le_σ h0
  have hb₁ := (carriedTemperature_bounds hb hv h0 hd ht hx).2.2
  have hb₂ := (carriedTemperature_bounds hb hv h0 hd ht hx').2.2
  refine le_add_max_mul_rpow (by positivity) hα0 hα1 (norm_nonneg _)
    (norm_fderiv_fderiv_carriedTemperature_sub_le_add hb hv h0 hd hα0 ht hx hx') ?_
    (by positivity)
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x‖ +
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x'‖ :=
        norm_sub_le (fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x)
          (fderiv ℝ (fderiv ℝ (fun z ↦ carriedTemperature θ₀ v a b z t)) x')
    _ ≤ 2 * (N * σ + N * L ^ 2) := by linarith

end HalfPlaneSystem
