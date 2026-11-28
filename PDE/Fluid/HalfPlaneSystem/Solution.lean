/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Iteration
import PDE.Analysis.Calculus.SliceDerivative

/-!
# Classical solutions of a half-plane system and their construction from a fixed point

A half-plane system with the velocity law `U` and the forcing coefficient `κ` is `θ_t + u · ∇θ = 0`,
`ω_t + u · ∇ω = κ ∂₀θ` on the open upper half-plane, with the velocity `u(t) = U (ω t)`. For the
half-plane Biot-Savart law and `κ = 1` this is the Boussinesq system; for the velocity of the
cylinder near its wall and `κ = r⁻⁴` it is axisymmetric Euler with swirl. This module defines the
classical solutions and shows that a vorticity history that reproduces itself under the Lagrangian
iteration map is one.

The class `IsSolutionOn U κ R₀ sol I` asks for joint `C¹` regularity on `ℝ² × I`, the two transport
equations, and supports on the closed half-plane in a disc of radius less than `R₀` uniformly on
compact time intervals. Every disc of this folder is a disc about the origin. Only the values on the
closed half-plane are determined; the fields below the boundary are classical extensions. The class
has no boundary condition of its own: the tangency of the velocity is a property of the law.

A `C^{1,α}` history `ω` on `[a, b]`, `a < 0 < b`, that equals on the closed half-plane the vorticity
carried by the flow of its own field gives a solution on `(a, b)` with the data at time zero
(`isSolutionOn_of_fixedPoint`): the carried fields solve the transport equations on the whole plane
with the field of `ω`, which on the closed half-plane is `U (ω t)`, and `U (ω t)` depends only on
the values of `ω t` there, which are those of the carried vorticity. No stream function and no
incompressibility enter: the supports move by at most the velocity bound times the time.

## Main results

* `Fields`, `HasBoundedSupportOn`, `IsSolutionOn`, `HasDataAt`: the pair of fields, the support
  condition, the class of classical solutions and the data at a time.
* `assembled`: the fields carried by the flow of the field of a history.
* `IsSolutionOn.mono`, `IsSolutionOn.contDiff_vorticity`, `IsSolutionOn.contDiff_temperature`:
  solutions restrict to fewer times, and their slices are globally `C¹`.
* `IsSolutionOn.exists_isVorticityHistory`: on a compact interval of times the vorticity of a
  solution vanishes outside a disc of radius `R < R₀`, is bounded with its gradient, and is a
  vorticity history for every exponent `α ∈ [0, 1]`.
* `assembled_eq_zero`: the assembled fields vanish on the closed half-plane outside the disc of
  radius `R + C 0 0 B max(-a, b)`.
* `isSolutionOn_of_fixedPoint`: for `0 < α < 1` and data of the class `IsHolderData`, a fixed point
  of the iteration map, a `C^{1,α}` history with support radius at most `R₀` whose carried supports
  stay in a disc of radius less than `R₀`, is a solution on `(a, b)` with the data at time zero.

`LocalExistence.lean` produces the fixed point and applies `isSolutionOn_of_fixedPoint`.
`Lagrangian.lean` gives the characteristic formulas for `IsSolutionOn`, `Uniqueness.lean`
proves forward uniqueness in that class on the closed half-plane, and the modules of the a priori
estimate study solutions of the class.
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

/-- The vorticity and the temperature of a half-plane system. -/
structure Fields where
  /-- The vorticity. -/
  vorticity : ℝ^2 → ℝ → ℝ
  /-- The temperature. -/
  temperature : ℝ^2 → ℝ → ℝ

/-- The vorticity and the temperature vanish on the closed half-plane outside a disc about the
origin of radius less than `R₀` that is common to all times of every compact interval
`[a, b] ⊆ I`. -/
def HasBoundedSupportOn (R₀ : ℝ) (sol : Fields) (I : Set ℝ) : Prop :=
  ∀ a b : ℝ, Icc a b ⊆ I → ∃ R < R₀, ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ →
    sol.vorticity x t = 0 ∧ sol.temperature x t = 0

/-- A classical solution on the times `I` of the half-plane system with the velocity law `U` and
the forcing coefficient `κ`: jointly `C¹` fields solving `ω_t + u · ∇ω = κ ∂₀θ` and
`θ_t + u · ∇θ = 0` on the open upper half-plane with `u(t) = U (ω t)`, whose supports on the
closed half-plane lie in a disc about the origin of radius less than `R₀` uniformly on compact
time intervals. -/
structure IsSolutionOn (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (κ : ℝ^2 → ℝ) (R₀ : ℝ) (sol : Fields)
    (I : Set ℝ) : Prop where
  /-- Joint first-order regularity of the vorticity. -/
  vorticity_contDiffOn : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) (univ ×ˢ I)
  /-- Joint first-order regularity of the temperature. -/
  temperature_contDiffOn :
    ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) (univ ×ˢ I)
  /-- The vorticity is differentiable in time at the times of `I`. -/
  vorticity_differentiableAt_time {x : ℝ^2} {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (fun s ↦ sol.vorticity x s) t
  /-- The temperature is differentiable in time at the times of `I`. -/
  temperature_differentiableAt_time {x : ℝ^2} {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (fun s ↦ sol.temperature x s) t
  /-- The vorticity equation on the open upper half-plane. -/
  vorticity_equation {x : ℝ^2} {t : ℝ} (hx : 0 < x 1) (ht : t ∈ I) :
    deriv (fun s ↦ sol.vorticity x s) t +
        PDE.advectiveDerivative (U (fun y ↦ sol.vorticity y t)) (fun y ↦ sol.vorticity y t) x =
      κ x * PDE.partialDeriv 0 (fun y ↦ sol.temperature y t) x
  /-- The temperature equation on the open upper half-plane. -/
  temperature_equation {x : ℝ^2} {t : ℝ} (hx : 0 < x 1) (ht : t ∈ I) :
    deriv (fun s ↦ sol.temperature x s) t +
        PDE.advectiveDerivative (U (fun y ↦ sol.vorticity y t)) (fun y ↦ sol.temperature y t)
          x = 0
  /-- Supports on the closed half-plane in a disc about the origin of radius less than `R₀`,
  uniformly on compact time intervals. -/
  support : HasBoundedSupportOn R₀ sol I

/-- The fields take the values `ω₀` and `θ₀` at time `t₀` on the closed half-plane. -/
def HasDataAt (sol : Fields) (t₀ : ℝ) (ω₀ θ₀ : ℝ^2 → ℝ) : Prop :=
  ∀ x : ℝ^2, 0 ≤ x 1 → sol.vorticity x t₀ = ω₀ x ∧ sol.temperature x t₀ = θ₀ x

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

/-- Bounded supports restrict to smaller sets of times. -/
theorem HasBoundedSupportOn.mono {sol : Fields} {I J : Set ℝ} (h : HasBoundedSupportOn R₀ sol I)
    (hJ : J ⊆ I) : HasBoundedSupportOn R₀ sol J :=
  fun a b hab ↦ h a b (hab.trans hJ)

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ}

/-- Solutions restrict to smaller sets of times. -/
theorem mono (h : IsSolutionOn U κ R₀ sol I) {J : Set ℝ} (hJ : J ⊆ I) :
    IsSolutionOn U κ R₀ sol J where
  vorticity_contDiffOn := h.vorticity_contDiffOn.mono (prod_mono subset_rfl hJ)
  temperature_contDiffOn := h.temperature_contDiffOn.mono (prod_mono subset_rfl hJ)
  vorticity_differentiableAt_time ht := h.vorticity_differentiableAt_time (hJ ht)
  temperature_differentiableAt_time ht := h.temperature_differentiableAt_time (hJ ht)
  vorticity_equation hx ht := h.vorticity_equation hx (hJ ht)
  temperature_equation hx ht := h.temperature_equation hx (hJ ht)
  support := h.support.mono hJ

/-- Every time slice of the vorticity is globally `C¹`. -/
theorem contDiff_vorticity (h : IsSolutionOn U κ R₀ sol I) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ 1 (fun x ↦ sol.vorticity x t) := by
  simpa only [Function.comp_def] using
    h.vorticity_contDiffOn.comp_contDiff (contDiff_prodMk_left t) (fun x ↦ ⟨mem_univ x, ht⟩)

/-- Every time slice of the temperature is globally `C¹`. -/
theorem contDiff_temperature (h : IsSolutionOn U κ R₀ sol I) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ 1 (fun x ↦ sol.temperature x t) := by
  simpa only [Function.comp_def] using
    h.temperature_contDiffOn.comp_contDiff (contDiff_prodMk_left t) (fun x ↦ ⟨mem_univ x, ht⟩)

/-- **Uniform bounds on compact time intervals.** On `[a, b] ⊆ I` with `a < b` the vorticity of a
solution vanishes on the closed half-plane outside a common disc of radius `R < R₀`, is bounded
together with the spatial derivatives of its slices on the closed half-plane uniformly in time,
and is continuous in time uniformly on the closed half-plane; for every exponent `α ∈ [0, 1]` it
is therefore a vorticity history whose Hölder constant comes from the gradient bound. -/
theorem exists_isVorticityHistory (h : IsSolutionOn U κ R₀ sol I) {a b α : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ I) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ R < R₀, ∃ B B₁ : ℝ, 0 ≤ B ∧ 0 ≤ B₁ ∧
      IsVorticityHistory (fun t x ↦ sol.vorticity x t) a b α R B (max B₁ (2 * B)) ∧
      ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderiv ℝ (fun y ↦ sol.vorticity y t) x‖ ≤ B₁ := by
  obtain ⟨R, hRR₀, hR⟩ := h.support a b hI
  obtain ⟨B, B₁, hB0, hB₁0, hB, hB₁, hu, -⟩ :=
    PDE.Analysis.exists_bounds_of_contDiffOn (f := sol.vorticity) hab hI
      h.vorticity_contDiffOn fun t ht x hx hxR ↦ (hR t ht x hx hxR).1
  have hc (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (fun x ↦ sol.vorticity x t) :=
    h.contDiff_vorticity (hI ht)
  have hfd (t : ℝ) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderivWithin ℝ (fun y ↦ sol.vorticity y t) H̄ x =
        fderiv ℝ (fun y ↦ sol.vorticity y t) x :=
    ((hc t ht).differentiable (by norm_num) x).fderivWithin (uniqueDiffOn_closedUpper x hx)
  refine ⟨R, hRR₀, B, B₁, hB0, hB₁0, ?_, hB₁⟩
  refine IsVorticityHistory.of_fderivWithin_le (fun t ht ↦ (hc t ht).contDiffOn)
    (fun t ht x hx hxR ↦ (hR t ht x hx hxR).1) hB (fun t ht x hx ↦ ?_) hu hα0 hα1
  rw [hfd t ht hx]
  exact hB₁ t ht x hx

end IsSolutionOn

/-! ### The fields assembled from a history -/

/-- The fields assembled from a vorticity history `ω` on the times `[a, b]`: the vorticity and
the temperature carried by the flow of the field of `ω` under the law `U`. -/
def assembled (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (κ ω₀ θ₀ : ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (a b : ℝ) :
    Fields where
  vorticity := carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) a b
  temperature := carriedTemperature θ₀ (lawField U ω) a b

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R N : ℝ} {a b : ℝ} {ω : ℝ → ℝ^2 → ℝ} {R₁ B M B₁ M₁ : ℝ}

/-- **Supports.** The assembled vorticity and temperature vanish on the closed half-plane outside
the disc of radius `R + C 0 0 B max(-a, b)`, `R` the support radius of the data. -/
theorem assembled_eq_zero (hU : IsVelocityLaw U R₀ C) (hα : 0 < α) (hα1 : α < 1)
    (hdata : IsHolderData ω₀ θ₀ α R N) (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁)
    (hR₁ : R₁ ≤ R₀) (h0 : (0 : ℝ) ∈ Icc a b) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2}
    (hx : 0 ≤ x 1) (hxR : R + C 0 0 * B * max (-a) b < ‖x‖) :
    (assembled U κ ω₀ θ₀ ω a b).vorticity x t = 0 ∧
      (assembled U κ ω₀ θ₀ ω a b).temperature x t = 0 := by
  have hb := isBoundedFlowOn_lawField hU hω hR₁ hα hα1 (h0.1.trans h0.2)
  have hv := (hω.isC2FieldOn_lawField hU hR₁ hα hα1).isLipschitzFieldOn
  have htτ : |t| ≤ max (-a) b := by
    rw [abs_le]
    constructor
    · linarith [le_max_left (-a) b, ht.1]
    · linarith [le_max_right (-a) b, ht.2]
  exact carried_eq_zero hb h0 hdata ht htτ hx (by linarith)

/-- On the closed half-plane the field of a fixed point is the field of the law at the assembled
vorticity. -/
theorem lawField_eq_assembled (hU : IsVelocityLaw U R₀ C)
    (hfix : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ω t x = carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) a b x t)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    lawField U ω t x = U (fun y ↦ (assembled U κ ω₀ θ₀ ω a b).vorticity y t) x := by
  rw [lawField_of_nonneg U ω t hx]
  exact hU.congr (fun y hy ↦ hfix t ht y hy) x hx

/-- **A fixed point of the iteration map is a solution.** If the `C^{1,α}` vorticity history `ω`
on `[a, b]`, `a < 0 < b`, with support radius `R₁ ≤ R₀`, equals on the closed half-plane the
vorticity carried by the flow of its own field, and the supports of the carried fields stay in a
disc of radius `R + C 0 0 B max(-a, b) < R₀`, then the assembled fields are a solution on `(a, b)`
in the class `IsSolutionOn U κ R₀` with the data `ω₀, θ₀` at time zero. It reduces existence of
a solution to existence of a fixed point. Proof: the carried fields solve the two transport
equations with the field of the history on the whole plane; on the closed half-plane this
field is the velocity of the law at the assembled vorticity, because the history is a fixed
point and the law sees only the values there. -/
theorem isSolutionOn_of_fixedPoint (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (hα : 0 < α) (hα1 : α < 1) (hdata : IsHolderData ω₀ θ₀ α R N) (ha : a < 0) (hb : 0 < b)
    (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁) (hR₁ : R₁ ≤ R₀)
    (hsupp : R + C 0 0 * B * max (-a) b < R₀)
    (hfix : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ω t x = carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) a b x t) :
    IsSolutionOn U κ R₀ (assembled U κ ω₀ θ₀ ω a b) (Ioo a b) ∧
      HasDataAt (assembled U κ ω₀ θ₀ ω a b) 0 ω₀ θ₀ := by
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨ha.le, hb.le⟩
  have hv := hω.isC2FieldOn_lawField hU hR₁ hα hα1
  have hv1 := hv.toIsC1FieldOn
  have hL := hv1.isLipschitzFieldOn
  have hθ2 : ContDiff ℝ 2 (dataTemperature θ₀) :=
    contDiff_dataTemperature hdata.temperature_contDiffOn
  have hω1 : ContDiff ℝ 1 (dataVorticity ω₀) := contDiff_dataVorticity hdata.vorticity_contDiffOn
  have hθd : Differentiable ℝ (dataTemperature θ₀) := hθ2.differentiable two_ne_zero
  have hκ1 := hκ.contDiff_one
  set sol := assembled U κ ω₀ θ₀ ω a b with hsol
  -- The carried vorticity solves the forced transport equation with the field of the history,
  -- at every point of the plane, and the carried temperature is transported by the same field.
  have hvort {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ^2) :
      HasDerivAt (fun s ↦ sol.vorticity x s)
        (κ x * fderiv ℝ (fun y ↦ sol.temperature y t) x (EuclideanSpace.single 0 1) -
          fderiv ℝ (fun y ↦ sol.vorticity y t) x (lawField U ω t x)) t :=
    hasDerivAt_forcedAmplitude_weightedForcing (e := EuclideanSpace.single 0 1) hv h0 hκ1 hθ2
      hω1 ht x
  have htemp {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ^2) :
      HasDerivAt (fun s ↦ sol.temperature x s)
        (-(fderiv ℝ (fun y ↦ sol.temperature y t) x (lawField U ω t x))) t :=
    hasDerivAt_comp_flowOn_time hv1 h0 hθd ht x
  -- In the open half-plane the field of the history is the velocity of the law at the
  -- assembled vorticity, because the history is a fixed point.
  have hvel {t : ℝ} (ht : t ∈ Ioo a b) {x : ℝ^2} (hx : 0 < x 1) :
      U (fun y ↦ sol.vorticity y t) x = lawField U ω t x :=
    (lawField_eq_assembled hU hfix (Ioo_subset_Icc_self ht) hx.le).symm
  -- The regularity, the two equations, the supports, and the data at time zero.
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact contDiffOn_forcedAmplitude_weightedForcing (e := EuclideanSpace.single 0 1) hv h0 hκ1
      hθ2 hω1
  · exact contDiffOn_comp_flowOn hv1 h0 (hθ2.of_le (by norm_num))
  · intro x t ht
    exact (hvort ht x).differentiableAt
  · intro x t ht
    exact (htemp ht x).differentiableAt
  · intro x t hx ht
    rw [(hvort ht x).deriv, PDE.advectiveDerivative, hvel ht hx, PDE.partialDeriv]
    abel
  · intro x t hx ht
    rw [(htemp ht x).deriv, PDE.advectiveDerivative, hvel ht hx]
    abel
  · intro a' b' hsub
    refine ⟨R + C 0 0 * B * max (-a) b, hsupp, fun t ht x hx hxR ↦ ?_⟩
    exact assembled_eq_zero hU hα hα1 hdata hω hR₁ h0 (Ioo_subset_Icc_self (hsub ht)) hx hxR
  · intro x hx
    constructor
    · change carriedVorticity κ ω₀ θ₀ (lawField U ω) (lawFieldDeriv U ω) a b x 0 = ω₀ x
      rw [carriedVorticity_zero κ ω₀ θ₀ hL h0, dataVorticity_of_nonneg ω₀ hx]
    · change carriedTemperature θ₀ (lawField U ω) a b x 0 = θ₀ x
      rw [carriedTemperature_zero θ₀ hL h0, dataTemperature_of_nonneg θ₀ hx]

end HalfPlaneSystem
