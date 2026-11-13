/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm

/-!
# Changing representatives in the weak initial identity

Both the state and its initial datum may be replaced almost everywhere.
The spacetime comparison is needed only for positive time. In particular,
extending a solution by zero to negative time does not change its initial
boundary term.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The full weak initial identity is invariant under almost-everywhere
changes of both the positive-time state and the prescribed initial datum. -/
theorem IsWeakInitialValueSolution.congr_ae_restrict {F : E → E} {g h : ℝ → E} {u v : ℝ^2 → E}
    (hu : IsWeakInitialValueSolution F g u) (huv : u =ᵐ[volume.restrict forwardHalfSpace] v)
    (hgh : g =ᵐ[volume] h) :
    IsWeakInitialValueSolution F h v := by
  have hflux := huv.fun_comp F
  have htest (φ : InitialValueTestFunction) : InteriorWeakForm.integrand u (fun p ↦ F (u p)) φ =ᵐ[
        volume.restrict forwardHalfSpace]
      InteriorWeakForm.integrand v (fun p ↦ F (v p)) φ := by
    filter_upwards [huv] with p hp
    simp only [InteriorWeakForm.integrand, hp]
  refine ⟨hu.u_locallyIntegrable.congr huv, hu.flux_locallyIntegrable.congr hflux,
    hu.initial_locallyIntegrable.congr hgh, fun φ ↦ (hu.spacetime_integrable φ).congr (htest φ), ?_⟩
  intro φ
  rw [← integral_congr_ae (htest φ)]
  have hb : (fun x : ℝ ↦ φ !₂[0, x] • g x) =ᵐ[volume]
        fun x ↦ φ !₂[0, x] • h x := by
    filter_upwards [hgh] with x hx
    rw [hx]
  rw [← integral_congr_ae hb]
  exact hu.weak_initial_eq φ

end PDE.Hyperbolic.ConservationLaw
