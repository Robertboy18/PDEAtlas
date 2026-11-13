/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The first integral of a viscous system profile

A traveling profile for identity viscosity satisfies a second-order vector ODE.
Its first integral and Rankine–Hugoniot condition follow from the end
limits, including the vanishing velocity at both ends.

The profile equation is (4) of Evans, §11.4.1, with the end conditions (5); the first integral
is (10), and the jump condition is (9), which we write with right-minus-left jumps. Existence
of profiles is in `ViscousProfile.Local.Existence`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (3)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- A classical traveling profile, including the four end conditions for the
second-order viscous equation. Constant profiles are allowed in this definition. -/
structure IsViscousProfile (flux : ℝ^m → ℝ^m) (uL uR : ℝ^m) (speed : ℝ)
    (v : ℝ → ℝ^m) : Prop where
  /-- The profile is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 v
  /-- The second-order equation for identity viscosity. -/
  equation : ∀ s, deriv (deriv v) s =
    fderiv ℝ flux (v s) (deriv v s) - speed • deriv v s
  /-- The state at the left end. -/
  tendsto_atBot : Tendsto v atBot (𝓝 uL)
  /-- The state at the right end. -/
  tendsto_atTop : Tendsto v atTop (𝓝 uR)
  /-- The velocity vanishes at the left end. -/
  tendsto_deriv_atBot : Tendsto (deriv v) atBot (𝓝 0)
  /-- The velocity vanishes at the right end. -/
  tendsto_deriv_atTop : Tendsto (deriv v) atTop (𝓝 0)

/-- Integrating the second-order equation and using its left end conditions
fixes the integration constant. -/
theorem IsViscousProfile.first_integral {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ} {v : ℝ → ℝ^m}
    (hv : IsViscousProfile flux uL uR speed v) (hflux : Differentiable ℝ flux) (s : ℝ) :
    deriv v s = flux (v s) - flux uL - speed • (v s - uL) := by
  let Q : ℝ → ℝ^m := fun t ↦ deriv v t - flux (v t) + speed • v t
  have hd : ∀ t, HasDerivAt Q 0 t := by
    intro t
    have hv' := (hv.contDiff.differentiable (by norm_num) t).hasDerivAt
    have hf' := (hflux (v t)).hasFDerivAt.comp_hasDerivAt t hv'
    have h := ((hv.contDiff.differentiable_deriv_two t).hasDerivAt.sub hf').add
      (hv'.const_smul speed)
    simpa [Q, hv.equation, Function.comp_def] using! h
  have hconst : ∀ t r, Q t = Q r :=
    is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv)
  have hlim : Tendsto Q atBot (𝓝 (-flux uL + speed • uL)) := by
    simpa [Q] using (hv.tendsto_deriv_atBot.sub
        (hflux.continuous.continuousAt.tendsto.comp hv.tendsto_atBot)).add
        (hv.tendsto_atBot.const_smul speed)
  have hQ : Q s = -flux uL + speed • uL := by
    have heq : Q = fun _ ↦ Q s := funext fun t ↦ hconst t s
    rw [heq] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  calc
    deriv v s = Q s + flux (v s) - speed • v s := by dsimp [Q]; abel
    _ = -flux uL + speed • uL + flux (v s) - speed • v s := by rw [hQ]
    _ = flux (v s) - flux uL - speed • (v s - uL) := by rw [smul_sub]; abel

/-- Taking the right limit in the first integral gives the vector
Rankine–Hugoniot condition, with the right-minus-left convention. -/
theorem IsViscousProfile.rankineHugoniot {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ} {v : ℝ → ℝ^m}
    (hv : IsViscousProfile flux uL uR speed v) (hflux : Differentiable ℝ flux) :
    RankineHugoniot flux uL uR speed := by
  have heq : deriv v = fun s ↦ flux (v s) - flux uL - speed • (v s - uL) :=
    funext (hv.first_integral hflux)
  have hlim : Tendsto (deriv v) atTop
      (𝓝 (flux uR - flux uL - speed • (uR - uL))) := by
    rw [heq]
    exact ((hflux.continuous.continuousAt.tendsto.comp hv.tendsto_atTop).sub_const _).sub
      ((hv.tendsto_atTop.sub_const _).const_smul speed)
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim hv.tendsto_deriv_atTop)

/-- A twice continuously differentiable orbit of the integrated equation has
all four profile end conditions once its state limits satisfy Rankine–Hugoniot.
The velocity limits are derived from the first-order equation. -/
theorem isViscousProfile_of_first_order {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ} {v : ℝ → ℝ^m}
    (hflux : Differentiable ℝ flux) (hv : ContDiff ℝ 2 v)
    (hode : ∀ s, HasDerivAt v (flux (v s) - flux uL - speed • (v s - uL)) s)
    (hleft : Tendsto v atBot (𝓝 uL)) (hright : Tendsto v atTop (𝓝 uR))
    (hjump : RankineHugoniot flux uL uR speed) :
    IsViscousProfile flux uL uR speed v := by
  have heq : deriv v = fun s ↦ flux (v s) - flux uL - speed • (v s - uL) :=
    funext fun s ↦ (hode s).deriv
  refine ⟨hv, ?_, hleft, hright, ?_, ?_⟩
  · intro s
    have hv' := (hv.differentiable (by norm_num) s).hasDerivAt
    have h := ((hflux (v s)).hasFDerivAt.comp_hasDerivAt s hv').sub_const (flux uL)
    have hd := h.sub ((hv'.sub_const uL).const_smul speed)
    change HasDerivAt (fun t ↦ flux (v t) - flux uL - speed • (v t - uL)) _ s at hd
    rw [← heq] at hd
    exact hd.deriv
  · rw [heq]
    simpa using ((hflux.continuous.continuousAt.tendsto.comp hleft).sub_const (flux uL)).sub
      ((hleft.sub_const uL).const_smul speed)
  · rw [heq]
    change flux uR - flux uL = speed • (uR - uL) at hjump
    simpa [hjump] using
      ((hflux.continuous.continuousAt.tendsto.comp hright).sub_const (flux uL)).sub
        ((hright.sub_const uL).const_smul speed)

end PDE.Hyperbolic.ConservationLaw.System
