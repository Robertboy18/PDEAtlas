/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Uniqueness
public import PDE.Fluid.Boussinesq.VorticityStream.Symmetry
import PDE.FDeriv.Reflection.Coordinate
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.Linearity

/-!
# Propagation of the reflection symmetry for half-plane Boussinesq solutions

Let `R (x₀, x₁) = (-x₀, x₁)` be the reflection in the vertical axis (`tangentialReflection`). The
reflection `(ω, θ, ψ) ↦ (-ω ∘ R, θ ∘ R, -ψ ∘ R)` of a solution of the half-plane Boussinesq system
is again a solution. Hence a solution whose data are odd in `x₀` (vorticity) and even in `x₀`
(temperature) keeps this parity at every later time, and if the temperature datum also vanishes on
the vertical axis, so does the temperature at every later time. Together these give the propagation
of the symmetry class (Sym) of Chen and Hou.

## Main definitions

* `reflected`: the reflected fields `(-ω ∘ R, θ ∘ R, -ψ ∘ R)`.
* `IsReflectionSymmetric`: the symmetry class (Sym) on the closed half-plane.

## Main results

* `halfSpaceGreenPotential_comp_tangentialReflection`: the half-space Green potential commutes with
  `R`.
* `halfPlaneVelocity_zero_eq_zero_of_odd`: odd vorticity gives zero horizontal velocity on the
  vertical axis.
* `IsSolutionOn.reflected`: the reflection of a solution is a solution.
* `IsSolutionOn.parity`, `IsSolutionOn.temperature_axis`, `IsSolutionOn.isReflectionSymmetric`:
  propagation of the parity, of the zero trace of the temperature on the axis and of the symmetry
  class, forward in time.

## How it works

Under the reflection the velocity becomes `R u ∘ R` (`vorticityStreamVelocity_reflected`), the
transport terms and the forcing, the derivative of `θ` in `x₀`, change sign together with `ω`, and
the half-space Green potential commutes with `R` because `R` preserves the half-plane and its Green
function; this gives `IsSolutionOn.reflected`. When the data have the parity, the reflected solution
has the same data as the solution, so the two agree at later times by uniqueness
(`IsSolutionOn.eq_of_hasDataAt`), which is `IsSolutionOn.parity`. For odd vorticity the Green
potential of its even extension is odd in `x₀`, so its derivative in `x₁`, the horizontal velocity
up to sign, vanishes on the vertical axis, and so does the horizontal component of the extended
velocity field. The axis is then invariant under the flow
(`IsLipschitzFieldOn.mapsTo_flowOn_eq_zero`), so the label of a point of the axis lies on the axis,
and the temperature, which is the datum at the label (`IsSolutionOn.temperature_eq_label`), vanishes
there.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, the symmetry class
  (Sym).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open GreenFunction PDE.Common IncompressibleFlow PDE.Analysis.ODE SobolevSpace
open PDE.Analysis (evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The Green potential and the reflection -/

/-- The tangential coordinate is not the normal one. -/
private theorem zero_ne_lastIndex : (0 : Fin 2) ≠ PDE.Common.lastIndex (n := 2) := by
  rw [show (PDE.Common.lastIndex : Fin 2) = 1 from rfl]
  decide

/-- The half-space Green potential commutes with the reflection in the vertical axis. -/
theorem halfSpaceGreenPotential_comp_tangentialReflection (f : ℝ^2 → ℝ) (x : ℝ^2) :
    halfSpaceGreenPotential (fun y ↦ f (tangentialReflection y)) x =
      halfSpaceGreenPotential f (tangentialReflection x) := by
  have hmp : MeasurePreserving (coordinateReflection (0 : Fin 2) : ℝ^2 → ℝ^2)
      (volume.restrict (HalfSpace.upper 2)) (volume.restrict (HalfSpace.upper 2)) :=
    HalfSpace.measurePreserving_coordinateReflection_restrict_upper 2 zero_ne_lastIndex
  have hemb : MeasurableEmbedding (coordinateReflection (0 : Fin 2) : ℝ^2 → ℝ^2) :=
    (coordinateReflectionLinearIsometryEquiv (0 : Fin 2)).toMeasurableEquiv.measurableEmbedding
  let g : ℝ^2 → ℝ := fun z ↦
    halfSpaceGreenFunction (n := 2) z (coordinateReflection 0 x) * f z
  have hg : (fun y ↦ g (coordinateReflection 0 y)) =
      fun y ↦ halfSpaceGreenFunction (n := 2) y x * f (coordinateReflection 0 y) := by
    funext y
    simp only [g]
    rw [halfSpaceGreenFunction_coordinateReflection (n := 2) zero_ne_lastIndex]
  unfold halfSpaceGreenPotential
  change ∫ y in HalfSpace.upper 2,
      halfSpaceGreenFunction (n := 2) y x * f (coordinateReflection 0 y) = ∫ z in _, g z
  rw [← hg, hmp.integral_comp hemb g]

/-- **Odd vorticity gives zero horizontal velocity on the vertical axis.** If `f` is continuous on
the closed half-plane, vanishes there outside a disc and is odd in `x₀` there, then the
horizontal component of its half-plane velocity vanishes at every point of the vertical axis. -/
theorem halfPlaneVelocity_zero_eq_zero_of_odd {f : ℝ^2 → ℝ} (hf : ContinuousOn f H̄)
    {R : ℝ} (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hodd : ∀ y : ℝ^2, 0 ≤ y 1 → f (tangentialReflection y) = -f y) {z : ℝ^2}
    (hz : z 0 = 0) : halfPlaneVelocity f z 0 = 0 := by
  set g := PDE.Analysis.evenReflection f
  have hgc : Continuous g := continuous_evenReflection hf
  have hgs : HasCompactSupport g := hasCompactSupport_evenReflection_of_eq_zero hR
  have hφ : ContDiff ℝ 1 (halfSpaceGreenPotential g) := contDiff_one_halfSpaceGreenPotential hgc hgs
  have hodd' : IsOddUnderCoordinateReflection (0 : Fin 2) (halfSpaceGreenPotential g) := by
    intro x
    have h1 := halfSpaceGreenPotential_comp_tangentialReflection g x
    have h2 : halfSpaceGreenPotential (fun y ↦ g (tangentialReflection y)) =
        halfSpaceGreenPotential (fun y ↦ -g y) := by
      apply halfSpaceGreenPotential_congr
      intro y hy
      have hy' : 0 ≤ y 1 := le_of_lt hy
      have hRy : 0 ≤ tangentialReflection y 1 := by
        simpa [tangentialReflection] using hy'
      simp only [g, evenReflection_of_nonneg hRy, evenReflection_of_nonneg hy']
      exact hodd y hy'
    rw [h2, halfSpaceGreenPotential_neg] at h1
    exact h1.symm
  have hd := (hodd'.partialDeriv_of_ne (j := 1) (by decide) hφ).vanishesOnCoordinateHyperplane
    (show z ∈ coordinateHyperplane (0 : Fin 2) from hz)
  rw [← halfPlaneVelocity_evenReflection f]
  have hu := congrFun (halfPlaneVelocity_zero g) z
  simp only [Pi.neg_apply] at hu
  rw [hu, hd, neg_zero]

/-! ### The reflected solution -/

/-- The reflection `(ω, θ, ψ) ↦ (-ω ∘ R, θ ∘ R, -ψ ∘ R)` of the fields in the vertical axis. -/
def reflected (sol : VorticityStreamFields) : VorticityStreamFields where
  vorticity x t := -sol.vorticity (tangentialReflection x) t
  temperature x t := sol.temperature (tangentialReflection x) t
  streamFunction x t := -sol.streamFunction (tangentialReflection x) t

/-- The first coordinate changes sign under the reflection. -/
@[simp]
theorem tangentialReflection_apply_zero (x : ℝ^2) : tangentialReflection x 0 = -x 0 := by
  simp [tangentialReflection]

/-- The second coordinate is fixed by the reflection. -/
@[simp]
theorem tangentialReflection_apply_one (x : ℝ^2) : tangentialReflection x 1 = x 1 := by
  simp [tangentialReflection]

/-- The reflection is an involution. -/
@[simp]
theorem tangentialReflection_tangentialReflection (x : ℝ^2) :
    tangentialReflection (tangentialReflection x) = x :=
  coordinateReflection_involutive 0 x

/-- The reflection preserves the norm. -/
@[simp]
theorem norm_tangentialReflection (x : ℝ^2) : ‖tangentialReflection x‖ = ‖x‖ :=
  norm_coordinateReflection 0 x

/-- The tangential derivative of a reflected function. -/
private theorem partialDeriv_zero_comp {g : ℝ^2 → ℝ} {x : ℝ^2}
    (hg : DifferentiableAt ℝ g (tangentialReflection x)) :
    (∂[(0 : Fin 2)] (fun y ↦ g (tangentialReflection y))) x =
      -(∂[(0 : Fin 2)] g) (tangentialReflection x) :=
  partialDeriv_comp_coordinateReflection_same 0 g x hg

/-- The normal derivative of a reflected function. -/
private theorem partialDeriv_one_comp {g : ℝ^2 → ℝ} {x : ℝ^2}
    (hg : DifferentiableAt ℝ g (tangentialReflection x)) :
    (∂[(1 : Fin 2)] (fun y ↦ g (tangentialReflection y))) x =
      (∂[(1 : Fin 2)] g) (tangentialReflection x) :=
  partialDeriv_comp_coordinateReflection_of_ne 0 1 (by decide) g x hg

/-- The velocity of the reflected fields is `R u ∘ R`, componentwise. -/
theorem vorticityStreamVelocity_reflected {sol : VorticityStreamFields} {t : ℝ} {x : ℝ^2}
    (hψ : Differentiable ℝ (fun y ↦ sol.streamFunction y t)) :
    vorticityStreamVelocity (reflected sol) x t 0 =
        -vorticityStreamVelocity sol (tangentialReflection x) t 0 ∧
      vorticityStreamVelocity (reflected sol) x t 1 =
        vorticityStreamVelocity sol (tangentialReflection x) t 1 := by
  have hd := hψ (tangentialReflection x)
  simp only [vorticityStreamVelocity, planarStreamVelocity_apply_zero,
    planarStreamVelocity_apply_one, reflected]
  rw [PDE.partialDeriv_fun_neg, PDE.partialDeriv_fun_neg, partialDeriv_one_comp hd,
    partialDeriv_zero_comp hd]
  constructor <;> ring

variable {sol : VorticityStreamFields} {I : Set ℝ}

/-- The linear map `(x, t) ↦ (R x, t)`. -/
private theorem contDiff_reflectSpace :
    ContDiff ℝ 1 (fun p : ℝ^2 × ℝ ↦ (tangentialReflection p.1, p.2)) :=
  ((coordinateReflectionLinearIsometryEquiv (0 : Fin 2)).contDiff.comp contDiff_fst).prodMk
    contDiff_snd

/-- **The reflection of a solution is a solution** on the same times. -/
theorem IsSolutionOn.reflected (h : IsSolutionOn sol I) :
    IsSolutionOn (HalfPlane.reflected sol) I := by
  have hreg := h.classical.regularity
  have hmaps : MapsTo (fun p : ℝ^2 × ℝ ↦ (tangentialReflection p.1, p.2)) (univ ×ˢ I)
      (univ ×ˢ I) := fun p hp ↦ ⟨mem_univ _, hp.2⟩
  have hψd (t : ℝ) (ht : t ∈ I) : Differentiable ℝ (fun y ↦ sol.streamFunction y t) :=
    (hreg.streamFunction_spatial_contDiff ht).differentiable (by norm_num)
  have hωd (t : ℝ) (ht : t ∈ I) : Differentiable ℝ (fun y ↦ sol.vorticity y t) :=
    (h.contDiff_vorticity ht).differentiable one_ne_zero
  have hθd (t : ℝ) (ht : t ∈ I) : Differentiable ℝ (fun y ↦ sol.temperature y t) :=
    (h.contDiff_temperature ht).differentiable one_ne_zero
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hreg.vorticity_contDiffOn.comp contDiff_reflectSpace.contDiffOn hmaps).neg
  · exact hreg.temperature_contDiffOn.comp contDiff_reflectSpace.contDiffOn hmaps
  · intro x t ht
    exact (hreg.vorticity_differentiableAt_time (x := tangentialReflection x) ht).neg
  · intro x t ht
    exact hreg.temperature_differentiableAt_time (x := tangentialReflection x) ht
  · intro t ht
    exact ((hreg.streamFunction_spatial_contDiff ht).comp
      (coordinateReflectionLinearIsometryEquiv (0 : Fin 2)).contDiff).neg
  · intro x t hx ht
    have hRx : tangentialReflection x ∈ upperHalfPlane :=
      tangentialReflection_mem_upperHalfPlane_iff.mpr hx
    have heq := h.classical.vorticity_equation hRx ht
    obtain ⟨hu0, hu1⟩ := vorticityStreamVelocity_reflected (x := x) (hψd t ht)
    simp only [PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Fin.sum_univ_two] at heq ⊢
    change deriv (fun s ↦ -sol.vorticity (tangentialReflection x) s) t +
        (vorticityStreamVelocity (HalfPlane.reflected sol) x t 0 *
            (∂[(0 : Fin 2)] (fun y ↦ -sol.vorticity (tangentialReflection y) t)) x +
          vorticityStreamVelocity (HalfPlane.reflected sol) x t 1 *
            (∂[(1 : Fin 2)] (fun y ↦ -sol.vorticity (tangentialReflection y) t)) x) =
      (∂[(0 : Fin 2)] (fun y ↦ sol.temperature (tangentialReflection y) t)) x
    rw [deriv.fun_neg, PDE.partialDeriv_fun_neg, PDE.partialDeriv_fun_neg,
      partialDeriv_zero_comp (hωd t ht _), partialDeriv_one_comp (hωd t ht _),
      partialDeriv_zero_comp (hθd t ht _), hu0, hu1]
    linear_combination (-1 : ℝ) * heq
  · intro x t hx ht
    have hRx : tangentialReflection x ∈ upperHalfPlane :=
      tangentialReflection_mem_upperHalfPlane_iff.mpr hx
    have heq := h.classical.temperature_equation hRx ht
    obtain ⟨hu0, hu1⟩ := vorticityStreamVelocity_reflected (x := x) (hψd t ht)
    simp only [PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Fin.sum_univ_two] at heq ⊢
    change deriv (fun s ↦ sol.temperature (tangentialReflection x) s) t +
        (vorticityStreamVelocity (HalfPlane.reflected sol) x t 0 *
            (∂[(0 : Fin 2)] (fun y ↦ sol.temperature (tangentialReflection y) t)) x +
          vorticityStreamVelocity (HalfPlane.reflected sol) x t 1 *
            (∂[(1 : Fin 2)] (fun y ↦ sol.temperature (tangentialReflection y) t)) x) = 0
    rw [partialDeriv_zero_comp (hθd t ht _), partialDeriv_one_comp (hθd t ht _), hu0, hu1]
    linear_combination heq
  · intro x t hx ht
    have hRx : tangentialReflection x ∈ upperHalfPlane :=
      tangentialReflection_mem_upperHalfPlane_iff.mpr hx
    have heq := h.classical.streamFunction_equation hRx ht
    change -PDE.laplacian (-(fun y ↦ sol.streamFunction (coordinateReflection 0 y) t)) x =
      -sol.vorticity (tangentialReflection x) t
    rw [PDE.laplacian_neg, PDE.Common.laplacian_comp_coordinateReflection 0 _ x
      (hreg.streamFunction_spatial_contDiff ht)]
    change -PDE.laplacian (fun y ↦ sol.streamFunction y t) (coordinateReflection 0 x) =
      sol.vorticity (coordinateReflection 0 x) t at heq
    change - -PDE.laplacian (fun y ↦ sol.streamFunction y t) (coordinateReflection 0 x) =
      -sol.vorticity (coordinateReflection 0 x) t
    linarith
  · intro x₁ t ht
    change -sol.streamFunction (tangentialReflection (horizontalBoundaryPoint x₁)) t = 0
    rw [tangentialReflection_horizontalBoundaryPoint,
      h.classical.zero_streamFunction_boundary (-x₁) ht, neg_zero]
  · intro t ht x hx
    have hRx : 0 ≤ tangentialReflection x 1 := by simpa using hx
    change -sol.streamFunction (tangentialReflection x) t =
      halfSpaceGreenPotential (fun y ↦ -sol.vorticity (tangentialReflection y) t) x
    rw [h.stream t ht _ hRx,
      halfSpaceGreenPotential_comp_tangentialReflection (fun z ↦ -sol.vorticity z t),
      halfSpaceGreenPotential_neg]
  · intro a b hab
    obtain ⟨R, hR⟩ := h.support a b hab
    refine ⟨R, fun t ht x hx hxR ↦ ?_⟩
    have hRx : 0 ≤ tangentialReflection x 1 := by simpa using hx
    have hRxR : R < ‖tangentialReflection x‖ := by simpa using hxR
    obtain ⟨h1, h2⟩ := hR t ht _ hRx hRxR
    exact ⟨by simp [_root_.Boussinesq.HalfPlane.reflected, h1], by
      simpa [_root_.Boussinesq.HalfPlane.reflected] using h2⟩

/-! ### Propagation of the symmetry class -/

/-- **The symmetry class (Sym)** of Chen and Hou on the closed half-plane: the vorticity is odd
and the temperature even in `x₀`, and the temperature vanishes on the vertical axis. -/
structure IsReflectionSymmetric (ω θ : ℝ^2 → ℝ) : Prop where
  /-- The vorticity is odd in `x₀` on the closed half-plane. -/
  vorticity_odd : ∀ x : ℝ^2, 0 ≤ x 1 → ω (tangentialReflection x) = -ω x
  /-- The temperature is even in `x₀` on the closed half-plane. -/
  temperature_even : ∀ x : ℝ^2, 0 ≤ x 1 → θ (tangentialReflection x) = θ x
  /-- The temperature vanishes on the vertical axis in the closed half-plane. -/
  temperature_axis : ∀ x : ℝ^2, x 0 = 0 → 0 ≤ x 1 → θ x = 0

/-- **Propagation of parity.** If the data of a solution at time `0` are odd (vorticity) and
even (temperature) in `x₀` on the closed half-plane, so are the fields at every later time of an
order-connected set of times containing `0`. -/
theorem IsSolutionOn.parity (h : IsSolutionOn sol I) (hI : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    (hω : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity (tangentialReflection x) 0 = -sol.vorticity x 0)
    (hθ : ∀ x : ℝ^2, 0 ≤ x 1 → sol.temperature (tangentialReflection x) 0 = sol.temperature x 0)
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity (tangentialReflection x) t = -sol.vorticity x t ∧
      sol.temperature (tangentialReflection x) t = sol.temperature x t := by
  have hdata : ∀ y : ℝ^2, 0 ≤ y 1 →
      (HalfPlane.reflected sol).vorticity y 0 = sol.vorticity y 0 ∧
        (HalfPlane.reflected sol).temperature y 0 = sol.temperature y 0 := fun y hy ↦ by
    refine ⟨?_, hθ y hy⟩
    change -sol.vorticity (tangentialReflection y) 0 = _
    rw [hω y hy, neg_neg]
  obtain ⟨h1, h2⟩ := h.reflected.eq_of_hasDataAt h hI h0 hdata ht ht0 hx
  change -sol.vorticity (tangentialReflection x) t = sol.vorticity x t at h1
  exact ⟨by linarith, h2⟩

/-- A weighted reflection across `x₁ = 0` of a function vanishing on the vertical axis vanishes
on the vertical axis. -/
private theorem weightedReflectionFun_eq_zero_of_axis {K : ℕ} {g : ℝ^2 → ℝ}
    (hg : ∀ z : ℝ^2, z 0 = 0 → g z = 0) {y : ℝ^2} (hy : y 0 = 0) :
    weightedReflectionFun 1 K g y = 0 := by
  by_cases hy1 : y 1 < 0
  · rw [PDE.Analysis.weightedReflectionFun_of_neg 1 K g hy1]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hg _ (by simp [normalDilation_apply, hy]), mul_zero]
  · rw [weightedReflectionFun_eq_of_nonneg 1 K g y (le_of_not_gt hy1)]
    exact hg y hy

/-- **Propagation of the zero temperature trace on the vertical axis.** If the data of a solution
have the parity of `IsSolutionOn.parity` and the temperature datum vanishes on the vertical axis,
the temperature vanishes on the vertical axis at every later time: the horizontal velocity
vanishes on the axis, so the axis is invariant under the flow, and the temperature is carried. -/
theorem IsSolutionOn.temperature_axis (h : IsSolutionOn sol I) (hI : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I)
    (hω : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity (tangentialReflection x) 0 = -sol.vorticity x 0)
    (hθ : ∀ x : ℝ^2, 0 ≤ x 1 → sol.temperature (tangentialReflection x) 0 = sol.temperature x 0)
    (haxis : ∀ x : ℝ^2, x 0 = 0 → 0 ≤ x 1 → sol.temperature x 0 = 0)
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) {x : ℝ^2} (hx0 : x 0 = 0) (hx : 0 ≤ x 1) :
    sol.temperature x t = 0 := by
  rcases ht0.eq_or_lt with rfl | hb
  · exact haxis x hx0 hx
  have hIt : Icc 0 t ⊆ I := hI.out h0 ht
  obtain ⟨K, hv⟩ := h.exists_isC1FieldOn hb hIt
  have hL := hv.isLipschitzFieldOn
  have htan : ∀ r ∈ Icc 0 t, ∀ y : ℝ^2, y 0 = 0 → velocityField sol r y 0 = 0 := by
    intro r hr y hy
    have hrI : r ∈ I := hIt hr
    obtain ⟨R, hR⟩ := h.exists_vorticity_eq_zero hrI
    have hu : ∀ z : ℝ^2, z 0 = 0 →
        halfPlaneVelocity (fun w ↦ sol.vorticity w r) z 0 = 0 := fun z hz ↦
      halfPlaneVelocity_zero_eq_zero_of_odd
        (h.contDiff_vorticity hrI).continuous.continuousOn hR
        (fun w hw ↦ (h.parity hI h0 hω hθ hrI hr.1 hw).1) hz
    simp only [velocityField, extendedVelocity_apply]
    exact weightedReflectionFun_eq_zero_of_axis hu hy
  have hlab : label sol t x t 0 = 0 :=
    hL.mapsTo_flowOn_eq_zero (j := 0) htan ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩ hx0
  have hlab1 := h.label_mem hIt hL ⟨hb.le, le_rfl⟩ hx
  rw [h.temperature_eq_label hIt hv ⟨hb.le, le_rfl⟩ hx]
  exact haxis _ hlab hlab1

/-- **Propagation of the symmetry class.** A solution whose data at time `0` are in the class
`IsReflectionSymmetric` stays in it at every later time of an order-connected set of times
containing `0`. -/
theorem IsSolutionOn.isReflectionSymmetric (h : IsSolutionOn sol I) (hI : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I)
    (hsym : IsReflectionSymmetric (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0))
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) :
    IsReflectionSymmetric (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) where
  vorticity_odd _ hx :=
    (h.parity hI h0 hsym.vorticity_odd hsym.temperature_even ht ht0 hx).1
  temperature_even _ hx :=
    (h.parity hI h0 hsym.vorticity_odd hsym.temperature_even ht ht0 hx).2
  temperature_axis _ hx0 hx :=
    h.temperature_axis hI h0 hsym.vorticity_odd hsym.temperature_even hsym.temperature_axis ht
      ht0 hx0 hx

end Boussinesq.HalfPlane
