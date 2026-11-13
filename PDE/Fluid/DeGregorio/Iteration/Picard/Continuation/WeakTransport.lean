/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakJet
public import PDE.Fluid.DeGregorio.DynamicRescaling.PrincipalValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The rescaled transport equation tested at H² regularity

On a compact H² slice, the coupled Hilbert relation recovers the weak velocity
jet. The equal-rate rescaled PDE then gives the conservative second-derivative
identity against compact C² spatial tests.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio

/-- The weak second-derivative equation of an equal-rate rescaled solution.
The H² state constructs both highest derivatives. Compact tests permit the
linear rescaling drift without a global bound on the velocity. -/
theorem IsClassicalRescaledSolutionOn.exists_weak_secondDerivative_transport
    {fields : Fields} {ρ : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ times)
    {t : ℝ} (ht : t ∈ times) (W : W^{2,2}(ℝ^1))
    (hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] fun x ↦ fields.vorticity x t)
    (hsupp : HasCompactSupport (fun x ↦ fields.vorticity x t))
    (hzero : fields.velocity 0 t = 0) :
    ∃ (r : Lp ℝ 2 (volume : Measure ℝ)) (s : ℝ → ℝ),
      HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) r ∧
      IsHilbertPair r s ∧
      ContDiff ℝ 2 (fun x ↦ fields.velocity x t) ∧
      HasWeakTimeDerivativeOn univ (deriv (deriv (fun x ↦ fields.velocity x t))) s ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        (∫ x, deriv (fields.vorticity x) t * deriv (deriv ψ) x) =
          (∫ x, (ρ t * x + fields.velocity x t) * r x * deriv ψ x) +
            ∫ x, (s x * fields.vorticity x t +
              deriv (deriv (fun y ↦ fields.velocity y t)) x *
                deriv (fun y ↦ fields.vorticity y t) x) * ψ x := by
  let w := fun x ↦ fields.vorticity x t
  let u := fun x ↦ fields.velocity x t
  have hw : Continuous w := continuous_iff_continuousAt.mpr fun _ ↦
    (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  obtain ⟨r, hw₁, hq, hwq, hqr⟩ :=
    Iteration.exists_weak_secondDerivative_of_h2 W hw hrep
  have hu₁ : ContDiff ℝ 1 u := by
    change ContDiff ℝ 1 (fun x ↦ fields.velocity x t)
    rw [hsol.velocity_eq_hilbertPVVelocity ht hw₁ hsupp hzero]
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hw₁ one_ne_zero
    exact contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hK hsupp
  obtain ⟨hu₂, _, s, hrs, hds⟩ := Iteration.IsHilbertPair.exists_weak_velocity_jet
    (hsol.biotSavart ht) hu₁ hq (Lp.memLp r) hwq hqr
  refine ⟨r, s, hqr, hrs, hu₂, hds, fun ψ hψ hc ↦ ?_⟩
  let V := fun x ↦ ρ t * x + u x
  have hV : ContDiff ℝ 2 V := (contDiff_const.mul contDiff_id).add hu₂
  have hV' : deriv V = fun x ↦ ρ t + deriv u x := by
    funext x
    simpa only [V, id_eq, mul_one, Pi.add_def] using
      (((hasDerivAt_id x).const_mul (ρ t)).add
        ((hu₁.differentiable one_ne_zero) x).hasDerivAt).deriv
  have hV'' : deriv (deriv V) = deriv (deriv u) := by
    rw [hV']
    funext x
    simpa only [zero_add] using
      ((((hu₂.deriv' (n := 1)).differentiable one_ne_zero) x).hasDerivAt.const_add
        (ρ t)).deriv
  have htime (x : ℝ) : deriv (fields.vorticity x) t =
      deriv V x * w x - V x * deriv w x := by
    rw [hV']
    have h := hsol.transport (x := x) ht
    simpa only [one_mul, w, u, V] using eq_sub_of_add_eq h
  simp_rw [htime]
  have hidentity := Iteration.integral_transport_secondDerivative_test
    hw₁ hV hqr (hV''.symm ▸ hds) hψ hc
  simpa only [hV'', w, u, V] using hidentity

end DeGregorio
