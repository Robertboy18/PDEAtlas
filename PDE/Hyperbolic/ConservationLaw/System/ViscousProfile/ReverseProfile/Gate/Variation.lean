/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.State

/-!
# Projected speed variation on the upward gate

The full-flux Jacobian, cutoff plateaus and reflected support identity
reduce the middle and fast coordinates at zero delta. Both feedback transitions
are accounted for: the fast state is beyond the inner transition and strictly
before the outer transition. The full-flow variational theorem then gives the
projected equations for the same physical speed derivative.
-/

@[expose] public noncomputable section

open Filter Set
open PDE.Analysis PDE.Analysis.NormalizedPulse
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The orbit and speed variation satisfy the upward-gate scalar
ODEs with zero delta and the same fixed coefficient vector. `hinner` is the
inner-transition completion margin supplied by the upward branch
geometry; positivity alone would not give a unit feedback plateau.

The set `I` need only lie in the closed ODE slab. Ordinary derivatives at its
endpoints are retained from the full-flow and variational theorems. -/
theorem prescribed_clock_upward_gate_variation {A B H : ℝ} {c : Fin 3 → ℝ} {b : (Fin 3 → ℝ) × ℝ → ℝ}
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))}
    {I : Set ℝ} (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b) (hΨ : ContDiff ℝ ∞ Ψ) (hN : IsOpen N)
    (hbase : ((0, c), (0, 0)) ∈ N)
    (hode : ∀ θ ∈ N, ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt (fun s ↦ Ψ (s, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (t, θ)) - θ.2.1 •
      Ψ (t, θ)) t)
    (hsupport : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (hI : I ⊆ Icc (0 : ℝ) H)
    (hgate : ∀ t ∈ I, Ψ (t, ((0, c), (0, 0))) 1 ∈ Ioo (205 : ℝ) (2051 / 10))
    (hinner : ∀ t ∈ I, 2 < Ψ (t, ((0, c), (0, 0))) 2)
    (houter : ∀ t ∈ I, (Ψ (t, ((0, c), (0, 0))) 2) ^ 2 < A ^ 2) :
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, ((0, c), (0, 0)))
    let W : ℝ → ℝ^3 := prescribedClockFullVariation Ψ (0, c) (1, 0)
    ∀ t ∈ I,
      HasDerivAt (fun s ↦ γ s 1) (MiddleClock.g (γ t 1) + 1) t ∧
      HasDerivAt (fun s ↦ γ s 2) (2 * γ t 2) t ∧
      HasDerivAt (fun s ↦ W s 1) (deriv MiddleClock.g (γ t 1) * W t 1 - γ t 1) t ∧
      HasDerivAt (fun s ↦ W s 2) (2 * W t 2 - γ t 2) t := by
  dsimp only
  intro t ht
  let γ : ℝ → ℝ^3 := fun s ↦ Ψ (s, ((0, c), (0, 0)))
  let W : ℝ → ℝ^3 := prescribedClockFullVariation Ψ (0, c) (1, 0)
  let f : ℝ^3 → ℝ^3 := concreteGatedFlux 0 (clockFeedback A B) (fun y ↦ b (c, y))
  have hbc : ContDiff ℝ ∞ (fun y : ℝ ↦ b (c, y)) := hb.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hflux, _, _, _, hJac⟩ := concreteGatedFlux_upward_gate_state
    (q := γ t) hAB (hbc.differentiable (by simp) (γ t 1))
    hsupport (hgate t ht).1 (hinner t ht) (houter t ht)
  have hf1 : f (γ t) 1 = MiddleClock.g (γ t 1) + 1 := congrArg (fun r : ℝ^3 ↦ r 1) hflux
  have hf2 : f (γ t) 2 = 2 * γ t 2 := congrArg (fun r : ℝ^3 ↦ r 2) hflux
  have hDf1 : (fderiv ℝ f (γ t) (W t)) 1 = deriv MiddleClock.g (γ t 1) * W t 1 :=
    congrArg (fun r : ℝ^3 ↦ r 1) (hJac (W t))
  have hDf2 : (fderiv ℝ f (γ t) (W t)) 2 = 2 * W t 2 := congrArg (fun r : ℝ^3 ↦ r 2) (hJac (W t))
  have hγode : HasDerivAt γ (f (γ t)) t := by
    simpa only [γ, f, zero_smul, sub_zero] using hode ((0, c), (0, 0)) hbase t (hI ht)
  have hWode : HasDerivAt W (fderiv ℝ f (γ t) (W t) - γ t) t := by
    simpa only [γ, W, f, one_smul] using
      hasDerivAt_prescribedClockFullVariation hb hΨ hN hbase hode (hI ht) (1, 0)
  have hγcoord (i : Fin 3) : HasDerivAt (fun s ↦ γ s i) (f (γ t) i) t :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ t) i).comp_hasDerivAt t hγode
  have hWcoord (i : Fin 3) : HasDerivAt (fun s ↦ W s i) ((fderiv ℝ f (γ t) (W t)) i - γ t i) t :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (W t) i).comp_hasDerivAt t hWode
  refine ⟨(hγcoord 1).congr_deriv hf1, (hγcoord 2).congr_deriv hf2, ?_, ?_⟩
  · exact (hWcoord 1).congr_deriv (congrArg (fun r : ℝ ↦ r - γ t 1) hDf1)
  · exact (hWcoord 2).congr_deriv (congrArg (fun r : ℝ ↦ r - γ t 2) hDf2)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
