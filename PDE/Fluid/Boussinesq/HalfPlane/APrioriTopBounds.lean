/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.APrioriTop
import PDE.Analysis.Calculus.IntegralMajorant

/-!
# Grönwall bounds of the top-order derivatives along trajectories

With `‖Du‖ ≤ A` on the closed half-plane and `∫₀ᵇ A ≤ Λ`, we bound the Hessian of the temperature
`H(r, a) = D²θ_r(X(r, a))` and the vorticity gradient `Z(r, a) = Dω_r(X(r, a))` along the
trajectories of the velocity field of the vorticity history, and their differences at two labels, by
integrals of the forcings.

## Main results

* `IsSolutionOn.norm_hessian_flowOn_le`: `‖H(r, a)‖ ≤ (‖D²θ₀(a)‖ + ∫₀ʳ m) exp (2Λ)` for a
  majorant `m` of `‖Dθ_ρ(X)‖ ‖D²v(ρ, X)‖`.
* `IsSolutionOn.norm_vorticityGradient_flowOn_le`: `‖Z(r, a)‖ ≤ (‖Dω₀(a)‖ + ∫₀ʳ m) exp Λ` for a
  majorant `m` of `‖H(ρ, a)‖`.
* `IsSolutionOn.norm_hessian_flowOn_sub_le`: the bound of `‖H(r, a) - H(r, a')‖` by
  `exp (2Λ)` times the initial difference plus the integral of a majorant of the forcing.
* `IsSolutionOn.norm_vorticityGradient_flowOn_sub_le`: `‖Z(r, a) - Z(r, a')‖` is at most `exp Λ`
  times `‖Dω₀(a) - Dω₀(a')‖` plus the integral of a majorant of
  `‖H(ρ, a) - H(ρ, a')‖ + ‖Z(ρ, a')‖ ‖δDv‖`.

## How it works

Each bound applies Grönwall's inequality with a coefficient of bounded integral
(`norm_le_mul_exp_of_integral_le`) to a transport equation along the trajectory:
`IsSolutionOn.hasDerivWithinAt_hessian` for `H`, `IsSolutionOn.hasDerivWithinAt_vorticityGradient`
for `Z`, and their differences at two labels. The velocity gradient enters the equation of `H`
twice, through `H[Du ·, ·]` and `H[·, Du ·]`, which gives the factor `exp (2Λ)`; it enters the
equation of `Z` once, through `Z ∘ Du`, which gives `exp Λ`. The other terms form the forcing, and
`le_of_le_integral_majorant` replaces its integral by that of any integrable majorant `m`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
open scoped Topology NNReal
open SobolevSpace

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

namespace IsSolutionOn

variable {sol : VorticityStreamFields} {I : Set ℝ} {b : ℝ}

set_option quotPrecheck false in
/-- The velocity field of the vorticity history. -/
local notation "𝐯" => historyField fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its spatial derivative. -/
local notation "𝐃𝐯" => historyFieldDeriv fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its second spatial derivative. -/
local notation "𝐃²𝐯" => historyFieldDeriv₂ fun t x ↦ sol.vorticity x t

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

section Hessian

variable {α R₀ B M B₁ M₁ Rq Nq : ℝ} {K K₁ K₂ : ℝ≥0}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R₀ B M B₁ M₁)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (historyField fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv₂ fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hreg : ∀ t ∈ Icc 0 b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)

variable {A : ℝ → ℝ} {Λ : ℝ} (hA : ContinuousOn A (Icc 0 b))
  (hDv : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖historyFieldDeriv (fun t x ↦ sol.vorticity x t) ρ x‖ ≤ A ρ)
  (hΛ : ∫ ρ in (0)..b, A ρ ≤ Λ)

omit hα hα1 in
include h hb hI hv hω hv₂ hreg hA hDv hΛ in
/-- **The Hessian along a trajectory.** For a majorant `m` of `‖Dθ_ρ(X)‖ ‖D²v(ρ, X)‖` on
`[0, r]`, `‖H(r, a)‖ ≤ (‖D²θ₀(a)‖ + ∫₀ʳ m) exp (2Λ)`. -/
theorem norm_hessian_flowOn_le {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ} (hr : r ∈ Icc 0 b)
    {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r, ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ m ρ) :
    ‖𝐇 r a‖ ≤ (‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a‖ +
      ∫ ρ in (0)..r, m ρ) * Real.exp (2 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_historyField hω hL ρ hρ 0 h0 ha
  have hX0 : 𝐗 0 a = a := hL.flowOn_self h0 a
  have hgc : ContinuousOn (fun ρ ↦ ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖) (Icc 0 b) :=
    (h.continuousOn_gradient_flowOn hb hI hv hω hv₂ ha).norm.mul
      (continuousOn_norm_bilinear (continuousOn_deriv₂_flowOn hb hv₂ a))
  refine PDE.Analysis.le_of_le_integral_majorant hr hgc hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐇 ρ a)
    (g := fun ρ ↦ ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖) (by norm_num)
    (fun ρ hρ ↦ h.hasDerivWithinAt_hessian hI hv hω hv₂ hreg ha hρ) hA
    (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ hgc (fun _ _ ↦ by positivity)
    (by rw [hX0]) (fun ρ hρ ↦ ?_) hr
  refine (norm_hessianTransport_le _ _ _ _).trans ?_
  gcongr
  exact hDv ρ hρ _ (hX ρ hρ)

include h hb hI hv hω hα hα1 hv₂ hreg hA hDv hΛ in
/-- **The vorticity gradient along a trajectory.** For a majorant `m` of `‖H(ρ, a)‖` on
`[0, r]`, `‖Z(r, a)‖ ≤ (‖Dω₀(a)‖ + ∫₀ʳ m) exp Λ`. -/
theorem norm_vorticityGradient_flowOn_le {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ} (hr : r ∈ Icc 0 b)
    {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r) (hgm : ∀ ρ ∈ Icc 0 r, ‖𝐇 ρ a‖ ≤ m ρ) :
    ‖𝐙 r a‖ ≤ (‖fderivWithin ℝ (fun x ↦ sol.vorticity x 0) H̄ a‖ +
      ∫ ρ in (0)..r, m ρ) * Real.exp (1 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_historyField hω hL ρ hρ 0 h0 ha
  have hX0 : 𝐗 0 a = a := hL.flowOn_self h0 a
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  have hgc : ContinuousOn (fun ρ ↦ ‖𝐇 ρ a‖) (Icc 0 b) :=
    continuousOn_norm_bilinear (h.continuousOn_hessian_flowOn hI hv hω hv₂ hreg ha)
  refine PDE.Analysis.le_of_le_integral_majorant hr hgc hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐙 ρ a) (g := fun ρ ↦ ‖𝐇 ρ a‖)
    zero_le_one
    (fun ρ hρ ↦ h.hasDerivWithinAt_vorticityGradient hb hI hv hω hα hα1 hv₂ hreg ha hρ) hA
    (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ hgc (fun _ _ ↦ by positivity)
    (by rw [hX0]) (fun ρ hρ ↦ ?_) hr
  refine (norm_apply_comp_sub_comp_le _ _ _ _).trans ?_
  rw [he, one_mul, one_mul, add_comm]
  gcongr
  exact hDv ρ hρ _ (hX ρ hρ)

omit hα hα1 in
include h hb hI hv hω hv₂ hreg hA hDv hΛ in
/-- **The Hessian at two labels.** `‖H(r, a) - H(r, a')‖` is at most `exp (2Λ)` times
`‖D²θ₀(a) - D²θ₀(a')‖` plus the integral over `[0, r]` of a majorant of
`2 ‖H(ρ, a')‖ ‖δDv‖ + ‖δDθ‖ ‖D²v(ρ, X(ρ, a))‖ + ‖Dθ_ρ(X(ρ, a'))‖ ‖δD²v‖`, where `δ` is the
difference of the values at `X(ρ, a)` and `X(ρ, a')`. -/
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
    mapsTo_flowOn_historyField hω hL ρ hρ 0 h0 ha
  have hX0 (c : ℝ^2) : 𝐗 0 c = c := hL.flowOn_self h0 c
  have hG := h.continuousOn_gradient_flowOn hb hI hv hω hv₂ ha
  have hG' := h.continuousOn_gradient_flowOn hb hI hv hω hv₂ ha'
  have hH' := h.continuousOn_hessian_flowOn hI hv hω hv₂ hreg ha'
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
  refine PDE.Analysis.le_of_le_integral_majorant hr hg hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐇 ρ a - 𝐇 ρ a') (by norm_num)
    (fun ρ hρ ↦ HasDerivWithinAt.sub (F := ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ)
      (h.hasDerivWithinAt_hessian hI hv hω hv₂ hreg ha hρ)
      (h.hasDerivWithinAt_hessian hI hv hω hv₂ hreg ha' hρ)) hA
    (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ
    hg (fun _ _ ↦ by positivity) (by simp only [hX0, le_refl]) (fun ρ hρ ↦ ?_) hr
  refine (norm_hessianTransport_sub_le _ _ _ _ _ _ _ _).trans ?_
  have hA' := hDv ρ hρ _ (hX ρ hρ)
  have : 2 * ‖𝐃𝐯 ρ (𝐗 ρ a)‖ * ‖𝐇 ρ a - 𝐇 ρ a'‖ ≤ 2 * A ρ * ‖𝐇 ρ a - 𝐇 ρ a'‖ := by gcongr
  linarith

include h hb hI hv hω hα hα1 hv₂ hreg hA hDv hΛ in
/-- **The vorticity gradient at two labels.** `‖Z(r, a) - Z(r, a')‖` is at most `exp Λ` times
`‖Dω₀(a) - Dω₀(a')‖` plus the integral over `[0, r]` of a majorant of
`‖H(ρ, a) - H(ρ, a')‖ + ‖Z(ρ, a')‖ ‖δDv‖`. -/
theorem norm_vorticityGradient_flowOn_sub_le {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1)
    {r : ℝ} (hr : r ∈ Icc 0 b) {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r,
      ‖𝐇 ρ a - 𝐇 ρ a'‖ + ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ m ρ) :
    ‖𝐙 r a - 𝐙 r a'‖ ≤
      (‖fderivWithin ℝ (fun x ↦ sol.vorticity x 0) H̄ a -
          fderivWithin ℝ (fun x ↦ sol.vorticity x 0) H̄ a'‖ +
        ∫ ρ in (0)..r, m ρ) * Real.exp (1 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv₁.isLipschitzFieldOn
  have hX (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) : 0 ≤ (𝐗 ρ a) 1 :=
    mapsTo_flowOn_historyField hω hL ρ hρ 0 h0 ha
  have hX0 (c : ℝ^2) : 𝐗 0 c = c := hL.flowOn_self h0 c
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  have hH := h.continuousOn_hessian_flowOn hI hv hω hv₂ hreg ha
  have hH' := h.continuousOn_hessian_flowOn hI hv hω hv₂ hreg ha'
  have hZ' := h.continuousOn_vorticityGradient_flowOn hb hI hv hω hα hα1 hv₂ hreg ha'
  have hD := hv₁.continuousOn_deriv_flowOn h0 a
  have hD' := hv₁.continuousOn_deriv_flowOn h0 a'
  have hHH : ContinuousOn (fun ρ ↦ 𝐇 ρ a - 𝐇 ρ a') (Icc 0 b) :=
    continuousOn_sub_bilinear hH hH'
  have hg : ContinuousOn (fun ρ ↦ ‖𝐇 ρ a - 𝐇 ρ a'‖ +
      ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖) (Icc 0 b) :=
    (continuousOn_norm_bilinear hHH).add (hZ'.norm.mul (hD.sub hD').norm)
  refine PDE.Analysis.le_of_le_integral_majorant hr hg hm hgm (Real.exp_pos _).le ?_
  refine norm_le_mul_exp_of_integral_le (f := fun ρ ↦ 𝐙 ρ a - 𝐙 ρ a') zero_le_one
    (fun ρ hρ ↦ (h.hasDerivWithinAt_vorticityGradient hb hI hv hω hα hα1 hv₂ hreg ha hρ).sub
      (h.hasDerivWithinAt_vorticityGradient hb hI hv hω hα hα1 hv₂ hreg ha' hρ)) hA
    (fun ρ hρ ↦ (norm_nonneg _).trans (hDv ρ hρ a ha)) hΛ
    hg (fun _ _ ↦ by positivity)
    (by simp only [hX0, le_refl]) (fun ρ hρ ↦ ?_) hr
  refine (norm_apply_comp_sub_comp_sub_le _ _ _ _ _ _ _).trans ?_
  rw [he, one_mul]
  have hA' := hDv ρ hρ _ (hX ρ hρ)
  have : ‖𝐃𝐯 ρ (𝐗 ρ a)‖ * ‖𝐙 ρ a - 𝐙 ρ a'‖ ≤ 1 * A ρ * ‖𝐙 ρ a - 𝐙 ρ a'‖ := by
    rw [one_mul]; gcongr
  linarith

end Hessian

end IsSolutionOn

end Boussinesq.HalfPlane
