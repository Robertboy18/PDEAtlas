/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.APrioriTop
import PDE.Analysis.Calculus.IntegralMajorant

/-!
# Grönwall bounds of the top-order derivatives along trajectories

The gradient of the vorticity and the Hessian of the temperature solve linear equations along the
particle trajectories, with the velocity gradient as coefficient (`APrioriTop.lean`). This module
bounds them at a later time, and their differences at two particles, when only the time integral of
the velocity gradient is bounded.

Consider a solution on `[0, b]` whose vorticity is a `C^{1,α}` history and whose slices are of the
class `IsHolderData`, with `‖Dv‖ ≤ A` on the closed half-plane and `∫₀ᵇ A ≤ Λ`. Grönwall's
inequality applied to the equations of the Hessian of the temperature `H(r, a) = D²θ_r(X(r, a))` and
of the vorticity gradient `Z(r, a) = Dω_r(X(r, a))` along the trajectories of the field of the law
bounds `H`, `Z` and their differences at two labels by integrals of the forcings. The equation of
`H` has the coefficient `Du` twice, which gives the factor `exp (2Λ)`; the equation of `Z` has it
once, which gives `exp Λ`. The forcing of `Z` contains the forcing coefficient and its derivative
along the trajectory. Each bound is stated for an integrable majorant `m` of the forcing, a
hypothesis here, so that the module which uses it can choose the majorant.

## Main results

Here `a`, `a'` are labels in the closed half-plane and `r ∈ [0, b]`.

* `IsSolutionOn.norm_hessian_flowOn_le`: `‖H(r, a)‖ ≤ (‖D²θ₀(a)‖ + ∫₀ʳ m) exp (2Λ)` for a majorant
  `m` of `‖Dθ_ρ(X)‖ ‖D²v(ρ, X)‖`.
* `IsSolutionOn.norm_vorticityGradient_flowOn_le`: `‖Z(r, a)‖ ≤ (‖Dω₀(a)‖ + ∫₀ʳ m) exp Λ` for a
  majorant `m` of `|κ(X)| ‖H(ρ, a)‖ + ‖Dθ_ρ(X)‖ ‖Dκ(X)‖`.
* `IsSolutionOn.norm_hessian_flowOn_sub_le`: `‖H(r, a) - H(r, a')‖` is at most `exp (2Λ)` times
  `‖D²θ₀(a) - D²θ₀(a')‖` plus the integral of a majorant of
  `2 ‖H(ρ, a')‖ ‖δDv‖ + ‖δDθ‖ ‖D²v(ρ, X(ρ, a))‖ + ‖Dθ_ρ(X(ρ, a'))‖ ‖δD²v‖`, where `δ` is the
  difference of the values at the two particles.
* `IsSolutionOn.norm_vorticityGradient_flowOn_sub_le`: `‖Z(r, a) - Z(r, a')‖` is at most `exp Λ`
  times `‖Dω₀(a) - Dω₀(a')‖` plus the integral of a majorant of
  `|κ| ‖δH‖ + |δκ| ‖H(ρ, a')‖ + ‖δDθ‖ ‖Dκ‖ + ‖Dθ_ρ(X(ρ, a'))‖ ‖δDκ‖ + ‖Z(ρ, a')‖ ‖δDv‖`.

`APriori.lean` chooses the majorants in terms of a monotone bound of the top-order quantities and
obtains the four integral inequalities of the a priori estimate.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
  Boussinesq.HalfPlane
open scoped Topology NNReal

open PDE.Analysis (le_of_le_integral_majorant)
namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ} {b : ℝ}

set_option quotPrecheck false in
/-- The field of the law at the vorticity history. -/
local notation "𝐯" => lawField U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its spatial derivative. -/
local notation "𝐃𝐯" => lawFieldDeriv U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its second spatial derivative. -/
local notation "𝐃²𝐯" => lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- The position at time `ρ` of the particle of label `a` for the flow of the history. -/
local notation "𝐗 " ρ:max a:max => flowOn 𝐯 0 b ρ 0 a

set_option quotPrecheck false in
/-- The temperature gradient along the particle of label `a`. -/
local notation "𝐆 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The Hessian of the temperature along the particle of label `a`. -/
local notation "𝐇 " ρ:max a:max =>
  fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The vorticity gradient along the particle of label `a`. -/
local notation "𝐙 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (𝐗 ρ a)

section Bounds

variable {α R B M B₁ M₁ Rq Nq : ℝ} {K K₁ K₂ : ℝ≥0}
  (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
  (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R B M B₁ M₁) (hR : R ≤ R₀)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (lawField U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hreg : ∀ t ∈ Icc 0 b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)
  {A : ℝ → ℝ} {Λ : ℝ} (hA : ContinuousOn A (Icc 0 b))
  (hDv : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖lawFieldDeriv U (fun t x ↦ sol.vorticity x t) ρ x‖ ≤ A ρ)
  (hΛ : ∫ ρ in (0)..b, A ρ ≤ Λ)

include hb hv₂ in
/-- The particle position is continuous in time. -/
theorem continuousOn_flowOn_time_lawField (a : ℝ^2) : ContinuousOn (fun ρ ↦ 𝐗 ρ a) (Icc 0 b) :=
  hv₂.toIsC1FieldOn.isLipschitzFieldOn.continuousOn_flowOn_time ⟨le_rfl, hb.le⟩ a

include hU h hb hI hv hω hR hv₂ hreg hA hDv hΛ in
/-- **The Hessian along a trajectory.** For a majorant `m` of `‖Dθ_ρ(X)‖ ‖D²v(ρ, X)‖` on
`[0, r]`, `‖H(r, a)‖ ≤ (‖D²θ₀(a)‖ + ∫₀ʳ m) exp (2Λ)`. Proof: Grönwall's inequality for the
equation `∂ᵣ H = -H[Du ·, ·] - H[·, Du ·] - Dθ ∘ D²u`, in which `Du` enters twice. -/
theorem norm_hessian_flowOn_le {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ} (hr : r ∈ Icc 0 b)
    {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r, ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ m ρ) :
    ‖𝐇 r a‖ ≤ (‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a‖ +
      ∫ ρ in (0)..r, m ρ) * Real.exp (2 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_lawField hU hω hR hL ρ hρ 0 h0 ha
  have hX0 : 𝐗 0 a = a := hL.flowOn_self h0 a
  have hgc : ContinuousOn (fun ρ ↦ ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖) (Icc 0 b) :=
    (h.continuousOn_gradient_flowOn hU hb hI hv hω hR hv₂ hreg ha).norm.mul
      (continuousOn_norm_bilinear (continuousOn_deriv₂_flowOn hb hv₂ a))
  refine le_of_le_integral_majorant hr hgc hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐇 ρ a)
    (g := fun ρ ↦ ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖) (by norm_num)
    (fun ρ hρ ↦ h.hasDerivWithinAt_hessian hU hb hI hv hω hR hv₂ hreg ha hρ) hA
    (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ hgc (fun _ _ ↦ by positivity)
    (by rw [hX0]) (fun ρ hρ ↦ ?_) hr
  refine (norm_hessianTransport_le _ _ _ _).trans ?_
  gcongr
  exact hDv ρ hρ _ (hX ρ hρ)

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg hA hDv hΛ in
/-- **The vorticity gradient along a trajectory.** For a majorant `m` of
`|κ(X)| ‖H(ρ, a)‖ + ‖Dθ_ρ(X)‖ ‖Dκ(X)‖` on `[0, r]`,
`‖Z(r, a)‖ ≤ (‖Dω₀(a)‖ + ∫₀ʳ m) exp Λ`. Proof: Grönwall's inequality for the equation
`∂ᵣ Z = κ H[·, e₀] + (∂₀θ) Dκ - Z ∘ Du`, in which `Du` enters once. -/
theorem norm_vorticityGradient_flowOn_le {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ} (hr : r ∈ Icc 0 b)
    {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r, |κ (𝐗 ρ a)| * ‖𝐇 ρ a‖ + ‖𝐆 ρ a‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ ≤ m ρ) :
    ‖𝐙 r a‖ ≤ (‖fderivWithin ℝ (fun x ↦ sol.vorticity x 0) H̄ a‖ +
      ∫ ρ in (0)..r, m ρ) * Real.exp (1 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_lawField hU hω hR hL ρ hρ 0 h0 ha
  have hX0 : 𝐗 0 a = a := hL.flowOn_self h0 a
  have hXc := continuousOn_flowOn_time_lawField hb hv₂ a
  have hgc : ContinuousOn (fun ρ ↦ |κ (𝐗 ρ a)| * ‖𝐇 ρ a‖ + ‖𝐆 ρ a‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖)
      (Icc 0 b) :=
    ((hκ.contDiff_one.continuous.comp_continuousOn hXc).abs.mul
      (continuousOn_norm_bilinear (h.continuousOn_hessian_flowOn hU hb hI hv hω hR hv₂ hreg
        ha))).add
      ((h.continuousOn_gradient_flowOn hU hb hI hv hω hR hv₂ hreg ha).norm.mul
        ((hκ.contDiff_one.continuous_fderiv one_ne_zero).comp_continuousOn hXc).norm)
  refine le_of_le_integral_majorant hr hgc hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐙 ρ a)
    (g := fun ρ ↦ |κ (𝐗 ρ a)| * ‖𝐇 ρ a‖ + ‖𝐆 ρ a‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖) zero_le_one
    (fun ρ hρ ↦ h.hasDerivWithinAt_vorticityGradient hU hκ hb hI hv hω hR hα hα1 hv₂ hreg ha
      hρ) hA (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ hgc
    (fun _ _ ↦ by positivity) (by rw [hX0]) (fun ρ hρ ↦ ?_) hr
  refine (norm_vorticityGradientTransport_le _ _ _ _ _ _).trans ?_
  have hA' := hDv ρ hρ _ (hX ρ hρ)
  have : ‖𝐃𝐯 ρ (𝐗 ρ a)‖ * ‖𝐙 ρ a‖ ≤ 1 * A ρ * ‖𝐙 ρ a‖ := by
    rw [one_mul]; gcongr
  linarith

include hU h hb hI hv hω hR hv₂ hreg hA hDv hΛ in
/-- **The Hessian at two labels.** `‖H(r, a) - H(r, a')‖` is at most `exp (2Λ)` times
`‖D²θ₀(a) - D²θ₀(a')‖` plus the integral over `[0, r]` of a majorant of
`2 ‖H(ρ, a')‖ ‖δDv‖ + ‖δDθ‖ ‖D²v(ρ, X(ρ, a))‖ + ‖Dθ_ρ(X(ρ, a'))‖ ‖δD²v‖`, where `δ` is the
difference of the values at `X(ρ, a)` and `X(ρ, a')`. It gives the Hölder constant of the
Hessian. Proof: the difference of the two Hessians solves the same linear equation with this
forcing, and Grönwall's inequality applies. -/
theorem norm_hessian_flowOn_sub_le {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1) {r : ℝ}
    (hr : r ∈ Icc 0 b) {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r, 2 * ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ +
      ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ + ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖ ≤
        m ρ) :
    ‖𝐇 r a - 𝐇 r a'‖ ≤
      (‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a -
          fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a'‖ +
        ∫ ρ in (0)..r, m ρ) * Real.exp (2 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv₁.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_lawField hU hω hR hL ρ hρ 0 h0 ha
  have hX0 (c : ℝ^2) : 𝐗 0 c = c := hL.flowOn_self h0 c
  have hG := h.continuousOn_gradient_flowOn hU hb hI hv hω hR hv₂ hreg ha
  have hG' := h.continuousOn_gradient_flowOn hU hb hI hv hω hR hv₂ hreg ha'
  have hH' := h.continuousOn_hessian_flowOn hU hb hI hv hω hR hv₂ hreg ha'
  have hD := hv₁.continuousOn_deriv_flowOn h0 a
  have hD' := hv₁.continuousOn_deriv_flowOn h0 a'
  have hT := continuousOn_deriv₂_flowOn hb hv₂ a
  have hT' := continuousOn_deriv₂_flowOn hb hv₂ a'
  have hTT : ContinuousOn (fun ρ ↦ 𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')) (Icc 0 b) :=
    continuousOn_sub_bilinear hT hT'
  have hg : ContinuousOn (fun ρ ↦ 2 * ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ +
      ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ +
      ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖) (Icc 0 b) :=
    (((continuousOn_const.mul (continuousOn_norm_bilinear hH')).mul
      (hD.sub hD').norm).add ((hG.sub hG').norm.mul
        (continuousOn_norm_bilinear hT))).add
      (hG'.norm.mul (continuousOn_norm_bilinear hTT))
  refine le_of_le_integral_majorant hr hg hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐇 ρ a - 𝐇 ρ a') (by norm_num)
    (fun ρ hρ ↦ HasDerivWithinAt.sub (F := ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ)
      (h.hasDerivWithinAt_hessian hU hb hI hv hω hR hv₂ hreg ha hρ)
      (h.hasDerivWithinAt_hessian hU hb hI hv hω hR hv₂ hreg ha' hρ)) hA
    (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ
    hg (fun _ _ ↦ by positivity) (by simp only [hX0, le_refl]) (fun ρ hρ ↦ ?_) hr
  refine (norm_hessianTransport_sub_le _ _ _ _ _ _ _ _).trans ?_
  have hA' := hDv ρ hρ _ (hX ρ hρ)
  have : 2 * ‖𝐃𝐯 ρ (𝐗 ρ a)‖ * ‖𝐇 ρ a - 𝐇 ρ a'‖ ≤ 2 * A ρ * ‖𝐇 ρ a - 𝐇 ρ a'‖ := by gcongr
  linarith

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg hA hDv hΛ in
/-- **The vorticity gradient at two labels.** `‖Z(r, a) - Z(r, a')‖` is at most `exp Λ` times
`‖Dω₀(a) - Dω₀(a')‖` plus the integral over `[0, r]` of a majorant of
`|κ| ‖δH‖ + |δκ| ‖H(ρ, a')‖ + ‖δDθ‖ ‖Dκ‖ + ‖Dθ_ρ(X(ρ, a'))‖ ‖δDκ‖ + ‖Z(ρ, a')‖ ‖δDv‖`, where `δ`
is the difference of the values at `X(ρ, a)` and `X(ρ, a')` and `κ`, `Dκ` are taken at
`X(ρ, a)`. It gives the Hölder constant of the gradient of the vorticity. Proof: the difference
of the two gradients solves the same linear equation with this forcing, and Grönwall's
inequality applies. -/
theorem norm_vorticityGradient_flowOn_sub_le {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1)
    {r : ℝ} (hr : r ∈ Icc 0 b) {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r,
      |κ (𝐗 ρ a)| * ‖𝐇 ρ a - 𝐇 ρ a'‖ + |κ (𝐗 ρ a) - κ (𝐗 ρ a')| * ‖𝐇 ρ a'‖ +
        ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ +
        ‖𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a) - fderiv ℝ κ (𝐗 ρ a')‖ +
        ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ m ρ) :
    ‖𝐙 r a - 𝐙 r a'‖ ≤
      (‖fderivWithin ℝ (fun x ↦ sol.vorticity x 0) H̄ a -
          fderivWithin ℝ (fun x ↦ sol.vorticity x 0) H̄ a'‖ +
        ∫ ρ in (0)..r, m ρ) * Real.exp (1 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv₁.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_lawField hU hω hR hL ρ hρ 0 h0 ha
  have hX0 (c : ℝ^2) : 𝐗 0 c = c := hL.flowOn_self h0 c
  have hXc := continuousOn_flowOn_time_lawField hb hv₂ a
  have hXc' := continuousOn_flowOn_time_lawField hb hv₂ a'
  have hκc := hκ.contDiff_one.continuous
  have hDκc := hκ.contDiff_one.continuous_fderiv one_ne_zero
  have hH := h.continuousOn_hessian_flowOn hU hb hI hv hω hR hv₂ hreg ha
  have hH' := h.continuousOn_hessian_flowOn hU hb hI hv hω hR hv₂ hreg ha'
  have hG := h.continuousOn_gradient_flowOn hU hb hI hv hω hR hv₂ hreg ha
  have hG' := h.continuousOn_gradient_flowOn hU hb hI hv hω hR hv₂ hreg ha'
  have hZ' := h.continuousOn_vorticityGradient_flowOn hU hκ hb hI hv hω hR hα hα1 hv₂ hreg ha'
  have hD := hv₁.continuousOn_deriv_flowOn h0 a
  have hD' := hv₁.continuousOn_deriv_flowOn h0 a'
  have hHH : ContinuousOn (fun ρ ↦ 𝐇 ρ a - 𝐇 ρ a') (Icc 0 b) :=
    continuousOn_sub_bilinear hH hH'
  have hg : ContinuousOn (fun ρ ↦
      |κ (𝐗 ρ a)| * ‖𝐇 ρ a - 𝐇 ρ a'‖ + |κ (𝐗 ρ a) - κ (𝐗 ρ a')| * ‖𝐇 ρ a'‖ +
        ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ +
        ‖𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a) - fderiv ℝ κ (𝐗 ρ a')‖ +
        ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖) (Icc 0 b) :=
    (((((hκc.comp_continuousOn hXc).abs.mul (continuousOn_norm_bilinear hHH)).add
      (((hκc.comp_continuousOn hXc).sub (hκc.comp_continuousOn hXc')).abs.mul
        (continuousOn_norm_bilinear hH'))).add
      ((hG.sub hG').norm.mul (hDκc.comp_continuousOn hXc).norm)).add
      (hG'.norm.mul ((hDκc.comp_continuousOn hXc).sub (hDκc.comp_continuousOn hXc')).norm)).add
      (hZ'.norm.mul (hD.sub hD').norm)
  refine le_of_le_integral_majorant hr hg hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐙 ρ a - 𝐙 ρ a') zero_le_one
    (fun ρ hρ ↦ (h.hasDerivWithinAt_vorticityGradient hU hκ hb hI hv hω hR hα hα1 hv₂ hreg ha
      hρ).sub (h.hasDerivWithinAt_vorticityGradient hU hκ hb hI hv hω hR hα hα1 hv₂ hreg ha' hρ))
    hA (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ hg (fun _ _ ↦ by positivity)
    (by simp only [hX0, le_refl]) (fun ρ hρ ↦ ?_) hr
  refine (norm_vorticityGradientTransport_sub_le _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  have hA' := hDv ρ hρ _ (hX ρ hρ)
  have : ‖𝐃𝐯 ρ (𝐗 ρ a)‖ * ‖𝐙 ρ a - 𝐙 ρ a'‖ ≤ 1 * A ρ * ‖𝐙 ρ a - 𝐙 ρ a'‖ := by
    rw [one_mul]; gcongr
  linarith

end Bounds

end IsSolutionOn

end HalfPlaneSystem
