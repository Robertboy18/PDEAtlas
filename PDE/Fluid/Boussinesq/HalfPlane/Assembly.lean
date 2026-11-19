/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Construction
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.ODE.Flow.Estimates
import PDE.FDeriv.Laplacian.Congruence

/-!
# A fixed point of the iteration map is a solution

Let `ω` be a `C^{1,α}` vorticity history on `[a, b]`, `a < 0 < b`, that is a fixed point of the
iteration map on the closed half-plane: `ω t x = carriedVorticity ω₀ θ₀ ω a b x t` there. The fields
`assembled ω₀ θ₀ ω a b` are the carried vorticity and temperature of the flow of the velocity field
of `ω`, with the stream function the weighted reflection of order two of the Green potential of
`ω t`. They form a solution in the class `IsSolutionOn` on `(a, b)` with the data `ω₀, θ₀` at time
zero (`isSolutionOn_of_fixedPoint`).

## Main definitions

* `assembled ω₀ θ₀ ω a b`: the carried vorticity, the carried temperature and the reflected Green
  stream function.

## Main results

* `isSolutionOn_of_fixedPoint`: a fixed-point history gives a solution on `(a, b)` with the data
  at time zero.
* `assembled_vorticity_of_nonneg`, `assembled_eq_zero`, `hasBoundedSupportOn_assembled`: the
  vorticity is the history on the closed half-plane, and the support bound.

## How it works

The carried fields are jointly `C¹` on `ℝ² × (a, b)` and solve the transport equations on the whole
plane with the velocity field of `ω`: `PDE.Hyperbolic.Transport.hasDerivAt_comp_flowOn_time` for the
temperature and `PDE.Hyperbolic.Transport.hasDerivAt_forcedAmplitude_labelForcing` for the
vorticity, whose forcing is the derivative of the carried temperature in the direction `e₀`. On the
closed half-plane this field is the half-plane velocity of `ω t`, which by the fixed point property
is the velocity of the vorticity slice. It is also the velocity of the stream function, because the
reflected Green potential agrees with the Green potential there
(`vorticityStreamVelocity_assembled`). The Green potential solves the Poisson equation in the open
half-plane by the div-curl identities of the velocity
(`laplacian_halfSpaceGreenPotential_of_history`) and vanishes on the boundary. The labels move at
most `V |t|`, `V` the bound of the velocity on the closed half-plane, so the fields vanish on the
closed half-plane outside the disc of radius `R + V max(-a, b)` (`assembled_eq_zero`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology
open SobolevSpace GreenFunction IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport
open PDE.Analysis (evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The fields assembled from a vorticity history `ω` on the times `[a, b]`: the carried
vorticity, the carried temperature, and as stream function the weighted reflection of order two
of the Green potential of `ω t`. -/
def assembled (ω₀ θ₀ : ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (a b : ℝ) : VorticityStreamFields where
  vorticity := carriedVorticity ω₀ θ₀ ω a b
  temperature := carriedTemperature θ₀ ω a b
  streamFunction x t := weightedReflectionFun 1 2 (halfSpaceGreenPotential (ω t)) x

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R N : ℝ} {a b : ℝ} {ω : ℝ → ℝ^2 → ℝ} {R₁ B M : ℝ}

/-- The Green potential of a time of a history is `C²` within the closed half-plane. -/
theorem contDiffOn_halfSpaceGreenPotential_of_history
    (hω : IsVorticityHistory ω a b α R₁ B M) (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Icc a b) : ContDiffOn ℝ 2 (halfSpaceGreenPotential (ω t)) H̄ := by
  have h := contDiffOn_succ_halfSpaceGreenPotential (m := 1) (hω.continuousOn t ht)
    (hω.eq_zero t ht) (hω.contDiffOn_halfPlaneVelocity hα ht)
  exact_mod_cast h

/-- The stream function of the assembled fields is globally `C²`. -/
theorem contDiff_assembled_streamFunction
    (hω : IsVorticityHistory ω a b α R₁ B M) (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ContDiff ℝ 2 (fun x ↦ (assembled ω₀ θ₀ ω a b).streamFunction x t) :=
  PDE.Analysis.contDiff_weightedReflectionFun (k := 2) 1 (by norm_num)
    (by exact_mod_cast contDiffOn_halfSpaceGreenPotential_of_history hω hα ht)

/-- The Green potential of a time of a history is globally `C¹`. -/
theorem contDiff_halfSpaceGreenPotential_of_history
    (hω : IsVorticityHistory ω a b α R₁ B M) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 1 (halfSpaceGreenPotential (ω t)) := by
  have hφ : halfSpaceGreenPotential (ω t) =
      halfSpaceGreenPotential (PDE.Analysis.evenReflection (ω t)) :=
    halfSpaceGreenPotential_congr fun y hy ↦
      (evenReflection_of_nonneg (le_of_lt hy)).symm
  rw [hφ]
  exact contDiff_one_halfSpaceGreenPotential
    (continuous_evenReflection (hω.continuousOn t ht))
    (hasCompactSupport_evenReflection_of_eq_zero (hω.eq_zero t ht))

/-- On the closed half-plane the velocity of the assembled stream function is the velocity
field of the history. -/
theorem vorticityStreamVelocity_assembled
    (hω : IsVorticityHistory ω a b α R₁ B M) (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    vorticityStreamVelocity (assembled ω₀ θ₀ ω a b) x t = historyField ω t x := by
  rw [historyField_of_nonneg ω t hx]
  set φ := halfSpaceGreenPotential (ω t)
  have hψ := contDiff_assembled_streamFunction (ω₀ := ω₀) (θ₀ := θ₀) hω hα ht
  have hφ := contDiff_halfSpaceGreenPotential_of_history hω ht
  have heq : EqOn (fun y ↦ (assembled ω₀ θ₀ ω a b).streamFunction y t) φ H̄ := fun y hy ↦
    weightedReflectionFun_eq_of_nonneg 1 2 φ y hy
  have hderiv : fderiv ℝ (fun y ↦ (assembled ω₀ θ₀ ω a b).streamFunction y t) x =
      fderiv ℝ φ x := by
    have h1 := (hψ.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt (s := H̄)
    have h2 := (hφ.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt (s := H̄)
    exact (uniqueDiffOn_closedUpper x hx).eq h1 (h2.congr (fun y hy ↦ heq hy) (heq hx))
  have hpartial (i : Fin 2) :
      (∂[i] (fun y ↦ (assembled ω₀ θ₀ ω a b).streamFunction y t)) x = (∂[i] φ) x := by
    simp only [PDE.partialDeriv, hderiv]
  ext k
  fin_cases k
  · simp [vorticityStreamVelocity, halfPlaneVelocity, planarStreamVelocity, hpartial, φ]
  · simp [vorticityStreamVelocity, halfPlaneVelocity, planarStreamVelocity, hpartial, φ]

/-- The Green potential of a Hölder vorticity solves `-Δφ = ω` in the open half-plane. -/
theorem laplacian_halfSpaceGreenPotential_of_history
    (hω : IsVorticityHistory ω a b α R₁ B M) (hα : 0 < α) (hα1 : α < 1) {t : ℝ}
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    -PDE.laplacian (halfSpaceGreenPotential (ω t)) x = ω t x := by
  set f := PDE.Analysis.evenReflection (ω t)
  have hf : Continuous f :=
    continuous_evenReflection (hω.continuousOn t ht)
  have hfc : HasCompactSupport f := hasCompactSupport_evenReflection_of_eq_zero
    (hω.eq_zero t ht)
  have hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α := by
    intro y z hy hz
    simp only [f, evenReflection_of_nonneg hy, evenReflection_of_nonneg hz]
    exact hω.holder t ht y z hy hz
  have hφ : halfSpaceGreenPotential (ω t) = halfSpaceGreenPotential f :=
    halfSpaceGreenPotential_congr fun y hy ↦
      (evenReflection_of_nonneg (le_of_lt hy)).symm
  obtain ⟨-, hcurl⟩ := partialDeriv_halfPlaneVelocity_div_curl hf hfc hα hα1.le hM hx
  have hfx : f x = ω t x := evenReflection_of_nonneg (le_of_lt hx)
  have h0 := halfPlaneVelocity_zero f
  have h1 := halfPlaneVelocity_one f
  rw [h0, h1, hfx, PDE.partialDeriv_neg] at hcurl
  rw [hφ]
  simp only [PDE.laplacian, Fin.sum_univ_two]
  change -((∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x +
      (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))) x) = ω t x
  linarith

variable {B₁ M₁ : ℝ}

/-- **Supports.** The assembled vorticity and temperature vanish on the closed half-plane outside
the disc of radius `R + V max(-a, b)`, where `R` is the support radius of the data and
`V = (1 + max R₁ 0 ^ 2) max B 0` bounds the velocity on the closed half-plane. -/
theorem assembled_eq_zero (hα : 0 < α) (hα1 : α < 1) (hdata : IsHolderData ω₀ θ₀ α R N)
    (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁) (h0 : (0 : ℝ) ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R + (1 + max R₁ 0 ^ 2) * max B 0 * max (-a) b < ‖x‖) :
    (assembled ω₀ θ₀ ω a b).vorticity x t = 0 ∧ (assembled ω₀ θ₀ ω a b).temperature x t = 0 := by
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hω hα hα1
  have hL := hv.toIsC1FieldOn.isLipschitzFieldOn
  have hS : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b, MapsTo (flowOn (historyField ω) a b s r) H̄ H̄ :=
    fun s hs r hr ↦ hL.mapsTo_flowOn_nonneg (j := 1)
      (fun q hq y hy ↦ historyField_normal_eq_zero hω.toIsVorticityHistory hq hy) hs hr
  set V := (1 + max R₁ 0 ^ 2) * max B 0 with hVdef
  have hV0 : 0 ≤ V := by positivity
  set Y := flowOn (historyField ω) a b 0 t x with hYdef
  have hY : 0 ≤ Y 1 := hS 0 h0 t ht hx
  have hdisp : ‖Y - x‖ ≤ V * |0 - t| :=
    IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS
      (fun r hr y hy ↦ (norm_historyField_le hω.toIsVorticityHistory hr hy).trans
        (mul_le_mul_of_nonneg_left (le_max_left B 0) (by positivity))) h0 ht hx
  have htabs : |0 - t| ≤ max (-a) b := by
    rw [zero_sub, abs_neg, abs_le]
    constructor
    · linarith [le_max_left (-a) b, ht.1]
    · linarith [le_max_right (-a) b, ht.2]
  have hYR : R < ‖Y‖ := by
    have h1 : ‖x‖ - ‖Y‖ ≤ ‖Y - x‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le x Y
    have h2 : V * |0 - t| ≤ V * max (-a) b := mul_le_mul_of_nonneg_left htabs hV0
    linarith
  have hθY : θ₀ Y = 0 := (hdata.eq_zero Y hY hYR).2
  have hωY : ω₀ Y = 0 := (hdata.eq_zero Y hY hYR).1
  have hθd : Differentiable ℝ (dataTemperature θ₀) :=
    (contDiff_dataTemperature hdata.temperature_contDiffOn).differentiable two_ne_zero
  have hDθ : fderiv ℝ (dataTemperature θ₀) Y = 0 :=
    PDE.Analysis.fderiv_slice_eq_zero (f := fun y (_ : ℝ) ↦ dataTemperature θ₀ y) (t := 0) hθd
      (fun z hz hzR ↦ by
        simp only [dataTemperature_of_nonneg θ₀ hz]
        exact (hdata.eq_zero z hz hzR).2) hY hYR
  constructor
  · change forcedAmplitude (dataVorticity ω₀) _ Y t = 0
    simp [forcedAmplitude, labelForcing, dataVorticity_of_nonneg ω₀ hY, hωY, hDθ]
  · change dataTemperature θ₀ Y = 0
    rw [dataTemperature_of_nonneg θ₀ hY, hθY]

/-- On the closed half-plane the assembled vorticity is the fixed-point history. -/
theorem assembled_vorticity_of_nonneg
    (hfix : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → ω t x = carriedVorticity ω₀ θ₀ ω a b x t)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    (assembled ω₀ θ₀ ω a b).vorticity x t = ω t x :=
  (hfix t ht x hx).symm

/-- The assembled fields have supports bounded uniformly on `(a, b)`. -/
theorem hasBoundedSupportOn_assembled (hα : 0 < α) (hα1 : α < 1)
    (hdata : IsHolderData ω₀ θ₀ α R N) (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁)
    (h0 : (0 : ℝ) ∈ Icc a b) : HasBoundedSupportOn (assembled ω₀ θ₀ ω a b) (Ioo a b) :=
  fun _ _ hsub ↦ ⟨R + (1 + max R₁ 0 ^ 2) * max B 0 * max (-a) b, fun _ ht _ hx hxR ↦
    assembled_eq_zero hα hα1 hdata hω h0 (Ioo_subset_Icc_self (hsub ht)) hx hxR⟩

/-- **A fixed point of the iteration map is a solution.** If the `C^{1,α}` vorticity history `ω`
on `[a, b]`, `a < 0 < b`, equals on the closed half-plane the vorticity carried by the flow of its
own velocity field, then the assembled fields are a solution on `(a, b)` in the class
`IsSolutionOn` with the data `ω₀, θ₀` at time zero. -/
theorem isSolutionOn_of_fixedPoint (hα : 0 < α) (hα1 : α < 1)
    (hdata : IsHolderData ω₀ θ₀ α R N) (ha : a < 0) (hb : 0 < b)
    (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁)
    (hfix : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → ω t x = carriedVorticity ω₀ θ₀ ω a b x t) :
    IsSolutionOn (assembled ω₀ θ₀ ω a b) (Ioo a b) ∧ HasDataAt (assembled ω₀ θ₀ ω a b) 0 ω₀ θ₀ := by
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨ha.le, hb.le⟩
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hω hα hα1
  have hv1 := hv.toIsC1FieldOn
  have hL := hv1.isLipschitzFieldOn
  have hω' := hω.toIsVorticityHistory
  have hθ2 : ContDiff ℝ 2 (dataTemperature θ₀) :=
    contDiff_dataTemperature hdata.temperature_contDiffOn
  have hω1 : ContDiff ℝ 1 (dataVorticity ω₀) := contDiff_dataVorticity hdata.vorticity_contDiffOn
  have hθd : Differentiable ℝ (dataTemperature θ₀) := hθ2.differentiable two_ne_zero
  set sol := assembled ω₀ θ₀ ω a b with hsol
  have hvort {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ^2) :
      HasDerivAt (fun s ↦ sol.vorticity x s)
        (fderiv ℝ (fun y ↦ sol.temperature y t) x (EuclideanSpace.single 0 1) -
          fderiv ℝ (fun y ↦ sol.vorticity y t) x (historyField ω t x)) t :=
    hasDerivAt_forcedAmplitude_labelForcing (e := EuclideanSpace.single 0 1) hv h0 hθ2 hω1 ht x
  have htemp {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ^2) :
      HasDerivAt (fun s ↦ sol.temperature x s)
        (-(fderiv ℝ (fun y ↦ sol.temperature y t) x (historyField ω t x))) t :=
    hasDerivAt_comp_flowOn_time hv1 h0 hθd ht x
  have hvel {t : ℝ} (ht : t ∈ Ioo a b) {x : ℝ^2} (hx : x ∈ upperHalfPlane) :
      vorticityStreamVelocity sol x t = historyField ω t x :=
    vorticityStreamVelocity_assembled hω' hα (Ioo_subset_Icc_self ht)
      (le_of_lt (show 0 < x 1 from hx))
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact contDiffOn_forcedAmplitude_labelForcing (e := EuclideanSpace.single 0 1) hv h0 hθ2 hω1
  · exact contDiffOn_comp_flowOn hv1 h0 (hθ2.of_le (by norm_num))
  · intro x t ht
    exact (hvort ht x).differentiableAt
  · intro x t ht
    exact (htemp ht x).differentiableAt
  · intro t ht
    exact contDiff_assembled_streamFunction hω' hα (Ioo_subset_Icc_self ht)
  · intro x t hx ht
    rw [(hvort ht x).deriv, PDE.advectiveDerivative, hvel ht hx]
    simp only [PDE.partialDeriv]
    abel
  · intro x t hx ht
    rw [(htemp ht x).deriv, PDE.advectiveDerivative, hvel ht hx]
    abel
  · intro x t hx ht
    have hx' : x ∈ HalfSpace.upper 2 := by rwa [← upperHalfPlane_eq_halfSpaceUpper]
    have hopen : IsOpen {y : ℝ^2 | 0 < y 1} :=
      isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous
    have hgerm : (fun y ↦ sol.streamFunction y t) =ᶠ[𝓝 x]
        halfSpaceGreenPotential (ω t) := by
      filter_upwards [hopen.mem_nhds (show 0 < x 1 from hx)] with y hy
      exact weightedReflectionFun_eq_of_nonneg 1 2 _ y (le_of_lt hy)
    rw [EuclideanLaplacian.laplacian_congr_nhds hgerm,
      laplacian_halfSpaceGreenPotential_of_history hω' hα hα1 (Ioo_subset_Icc_self ht) hx']
    exact hfix t (Ioo_subset_Icc_self ht) x (le_of_lt (show 0 < x 1 from hx))
  · intro x₁ t ht
    change weightedReflectionFun 1 2 (halfSpaceGreenPotential (ω t))
      (horizontalBoundaryPoint x₁) = 0
    rw [weightedReflectionFun_eq_of_nonneg 1 2 _ _ (by simp)]
    exact halfSpaceGreenPotential_boundary _ (horizontalBoundaryPoint_mem_halfSpace_boundary x₁)
  · intro t ht x hx
    change weightedReflectionFun 1 2 (halfSpaceGreenPotential (ω t)) x = _
    rw [weightedReflectionFun_eq_of_nonneg 1 2 _ x hx]
    exact congrFun (halfSpaceGreenPotential_congr fun y hy ↦
      hfix t (Ioo_subset_Icc_self ht) y (le_of_lt hy)) x
  · exact hasBoundedSupportOn_assembled hα hα1 hdata hω h0
  · intro x hx
    constructor
    · change carriedVorticity ω₀ θ₀ ω a b x 0 = ω₀ x
      rw [carriedVorticity_zero ω₀ θ₀ hL h0, dataVorticity_of_nonneg ω₀ hx]
    · change carriedTemperature θ₀ ω a b x 0 = θ₀ x
      rw [carriedTemperature_zero θ₀, dataTemperature_of_nonneg θ₀ hx]

end Boussinesq.HalfPlane
