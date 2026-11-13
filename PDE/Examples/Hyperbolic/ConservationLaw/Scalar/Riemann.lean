/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.InitialValue
import CAS.ExactTactic

/-!
# A nonquadratic scalar Riemann problem

The flux `r⁴/4 + r²/2 + 2r + 7` has characteristic speed `r³ + r + 2` and second
derivative `3r² + 1 ≥ 1`, unbounded above. The Riemann theorem
`exists_riemann_initial_value_solution` gives, for every pair of states, an entropy
solution with strong initial trace and Oleinik bound `1`, unique among bounded weak
solutions with an Oleinik bound (`quartic_riemann_initial_value`). For the states
`-1, 2` it is a fan between the speeds `0` and `12`, for `2, -1` a shock with speed
`15/4`, and for equal states a constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.Scalar
open PDE.Hyperbolic.ConservationLaw.Scalar.Riemann

namespace PDE.Examples.ConservationLaw

/-- A uniformly convex flux with nonlinear characteristic speed, drift,
and a nonzero value at the origin. -/
def quarticFlux (r : ℝ) : ℝ := r ^ 4 / 4 + r ^ 2 / 2 + 2 * r + 7

/-- The characteristic speed is `r³ + r + 2`. -/
theorem deriv_quarticFlux (r : ℝ) :
    deriv quarticFlux r = r ^ 3 + r + 2 := by
  cas

/-- The second derivative of the flux is `3r² + 1`. -/
theorem deriv_deriv_quarticFlux (r : ℝ) :
    deriv (deriv quarticFlux) r = 3 * r ^ 2 + 1 := by
  cas

/-- The shock from `2` to `-1` has Rankine–Hugoniot speed `15/4`, between the
characteristic speeds `0` and `12`. -/
theorem quartic_shock_speed :
    rankineHugoniotSpeed quarticFlux 2 (-1) = 15 / 4 := by
  unfold rankineHugoniotSpeed
  cas

/-- For every pair of states the Riemann solution is an entropy solution with strong
initial trace and Oleinik bound `1`, unique among bounded weak solutions with an Oleinik
bound. The last clauses give it for the states `(-1, 2)`, `(2, -1)` and `(3, 3)`. -/
theorem quartic_riemann_initial_value :
    ∃ e : ℝ ≃o ℝ,
      (∀ r, e r = r ^ 3 + r + 2) ∧
      (∀ uL uR : ℝ,
        IsWeakInitialValueSolution quarticFlux (riemannData uL uR)
          (riemannSolution quarticFlux e uL uR) ∧
        IsEntropyWeakSolution quarticFlux forwardHalfSpace
          (riemannSolution quarticFlux e uL uR) ∧
        HasInitialTraceLocallyL1 (riemannSolution quarticFlux e uL uR)
          (riemannData uL uR) ∧
        HasOleinikBound (riemannSolution quarticFlux e uL uR) 1 ∧
        (∀ v : ℝ^2 → ℝ,
          IsWeakInitialValueSolution quarticFlux (riemannData uL uR) v →
          MemLp v ∞ (volume.restrict forwardHalfSpace) →
          (∃ Cv, HasOleinikBound v Cv) →
          v =ᵐ[volume.restrict forwardHalfSpace] riemannSolution quarticFlux e uL uR)) ∧
      e (-1) = 0 ∧ e 2 = 12 ∧
      (∀ p : ℝ^2, 0 < p 0 → p 1 ≤ 0 →
        riemannSolution quarticFlux e (-1) 2 p = -1) ∧
      (∀ p : ℝ^2, 0 < p 0 → 12 * p 0 ≤ p 1 →
        riemannSolution quarticFlux e (-1) 2 p = 2) ∧
      (∀ p : ℝ^2, 0 < p 0 →
        riemannSolution quarticFlux e 2 (-1) p = planarShock 2 (-1) (15 / 4) p) ∧
      (∀ p : ℝ^2, riemannSolution quarticFlux e 3 3 p = 3) := by
  have hF : ContDiff ℝ 2 quarticFlux := by
    unfold quarticFlux
    fun_prop
  have hcurv (r : ℝ) : 1 ≤ deriv (deriv quarticFlux) r := by
    rw [deriv_deriv_quarticFlux]
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg r))
  obtain ⟨e, C, he, hC, _, hstates⟩ :=
    exists_riemann_initial_value_solution hF (by norm_num : (0 : ℝ) < 1) hcurv
  have hCone : C = 1 := by simpa using hC
  have hspeed (r : ℝ) : e r = r ^ 3 + r + 2 := (he r).trans (deriv_quarticFlux r)
  have hleft : e (-1) = 0 := by rw [hspeed]; cas
  have hright : e 2 = 12 := by rw [hspeed]; cas
  refine ⟨e, hspeed, ?_, hleft, hright, ?_, ?_, ?_, ?_⟩
  · intro uL uR
    obtain ⟨hi, hentropy, htrace, _, _, _, _, _, _, hslope, _, _, _, huniq⟩ :=
      hstates uL uR
    exact ⟨hi, hentropy, htrace, hCone ▸ hslope, huniq⟩
  · intro p ht hx
    rw [riemannSolution_of_left_le_right quarticFlux e (by norm_num : (-1 : ℝ) ≤ 2) ht]
    apply rarefactionProfile_eq_left e ht
    simpa only [hleft, zero_mul] using hx
  · intro p ht hx
    rw [riemannSolution_of_left_le_right quarticFlux e (by norm_num : (-1 : ℝ) ≤ 2) ht]
    apply rarefactionProfile_eq_right e (by norm_num) ht
    simpa only [hright] using hx
  · intro p ht
    rw [riemannSolution_of_right_lt_left quarticFlux e (by norm_num : (-1 : ℝ) < 2) ht,
      quartic_shock_speed]
  · exact riemannSolution_same quarticFlux e 3

end PDE.Examples.ConservationLaw
