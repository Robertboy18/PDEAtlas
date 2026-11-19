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
# Contact identities along local characteristic curves

On a connected open parameter set, the chain rule first makes the characteristic
speed constant. The same argument for `F(R) - λ(R(t₀)) R` then gives the
Rankine–Hugoniot identity between any two points. Only derivatives at states
reached by the curve are required.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Set

/-- A local integral curve with zero speed derivative connects its
states by contacts. This single-curve statement also underlies the uniform
version for a family of nearby initial states. -/
theorem constant_speed_rankineHugoniot_of_integralCurve {m : ℕ} {flux : ℝ^m → ℝ^m} {eig : ℝ^m → ℝ}
    {r : ℝ^m → ℝ^m} {R : ℝ → ℝ^m} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hflux : ∀ s ∈ I, DifferentiableAt ℝ flux (R s)) (hflow : ∀ s ∈ I, HasDerivAt R (r (R s)) s)
    (hfield : ∀ s ∈ I, DifferentiableAt ℝ eig (R s) ∧ fderiv ℝ eig (R s) (r (R s)) = 0 ∧
      fderiv ℝ flux (R s) (r (R s)) = eig (R s) • r (R s))
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    eig (R s) = eig (R t) ∧ RankineHugoniot flux (R t) (R s) (eig (R t)) := by
  have hspeed (a : ℝ) (ha : a ∈ I) :
      HasDerivAt (fun b ↦ eig (R b)) 0 a := by
    simpa only [Function.comp_def, (hfield a ha).2.1] using
      (hfield a ha).1.hasFDerivAt.comp_hasDerivAt a (hflow a ha)
  have hconstant (a : ℝ) (ha : a ∈ I) : eig (R a) = eig (R t) := hI.is_const_of_deriv_eq_zero hconn
      (fun b hb ↦ (hspeed b hb).differentiableAt.differentiableWithinAt)
      (fun b hb ↦ (hspeed b hb).deriv) ha ht
  have hconserved (a : ℝ) (ha : a ∈ I) :
      HasDerivAt (fun b ↦ flux (R b) - eig (R t) • R b) 0 a := by
    have hdF := (hflux a ha).hasFDerivAt.comp_hasDerivAt a (hflow a ha)
    convert hdF.sub ((hflow a ha).const_smul (eig (R t))) using 1
    · rfl
    · rw [(hfield a ha).2.2, hconstant a ha, sub_self]
  refine ⟨hconstant s hs, ?_⟩
  have heq := hI.is_const_of_deriv_eq_zero hconn
    (fun a ha ↦ (hconserved a ha).differentiableAt.differentiableWithinAt)
    (fun a ha ↦ (hconserved a ha).deriv) hs ht
  change flux (R s) - flux (R t) = eig (R t) • (R s - R t)
  rw [smul_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp heq

end PDE.Hyperbolic.ConservationLaw.System
