/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Jump
public import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Trace

/-!
# Rankine–Hugoniot across a curved shock

Join two C¹ fields along a C¹ graph `x = s(t)`, and impose the classical
conservation law on each open side. The weak integral is precisely the
Rankine–Hugoniot defect tested on the graph. Hence the joined field is a weak
solution if and only if the traces satisfy Rankine–Hugoniot at every
time, with speed `s'(t)`.

The fields are global C¹ extensions; neither the fields nor the shock speed
need be constant. Their equations are required only on their respective sides.
All local integrability and trace testing statements are derived. With `s'(t)` as the speed
`σ`, the jump condition is the Rankine–Hugoniot condition (12) of Evans, §3.4.1(a).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1(a), equations (8)-(12).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common TopologicalSpace
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Shock

/-- The coefficient of a test trace in the weak conservation law:
`s'(t) [u] - [F(u)]`, with right-minus-left jumps. -/
def fluxJump (F s : ℝ → ℝ) (uL uR : ℝ^2 → ℝ) (t : ℝ) : ℝ :=
  deriv s t * (uR (interface s t) - uL (interface s t)) -
    (F (uR (interface s t)) - F (uL (interface s t)))

/-- Classical fields and a C¹ shock have a continuous Rankine–Hugoniot defect. -/
theorem continuous_fluxJump {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hF : Continuous F)
    (hs : ContDiff ℝ 1 s) (hL : Continuous uL) (hR : Continuous uR) :
    Continuous (fluxJump F s uL uR) := by
  have hc := continuous_interface hs.continuous
  exact (hs.continuous_deriv_one.mul ((hR.comp hc).sub (hL.comp hc))).sub
    ((hF.comp (hR.comp hc)).sub (hF.comp (hL.comp hc)))

/-- Rankine–Hugoniot is the vanishing of the coefficient in the weak jump formula. -/
theorem fluxJump_eq_zero_iff {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} {t : ℝ} :
    fluxJump F s uL uR t = 0 ↔
      RankineHugoniot F (uL (interface s t)) (uR (interface s t)) (deriv s t) :=
  sub_eq_zero.trans eq_comm

/-- The joined field is locally integrable, as is its continuous flux. -/
theorem locallyIntegrable_flux_profile {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hF : Continuous F)
    (hs : Continuous s) (hL : Continuous uL) (hR : Continuous uR) :
    LocallyIntegrable (fun p ↦ F (profile s uL uR p)) := by
  rw [comp_profile]
  exact locallyIntegrable_profile hs (hF.comp hL).locallyIntegrable (hF.comp hR).locallyIntegrable

/-- The weak jump formula for a moving shock with varying classical states.
The bulk conservation equations are imposed only strictly to each side. -/
theorem integral_weakIntegrand_profile {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hF : ContDiff ℝ 1 F)
    (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual F uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual F uR p = 0) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p, weakIntegrand F (profile s uL uR) φ p) =
      ∫ t, fluxJump F s uL uR t * φ (interface s t) := by
  have hcomp (p : ℝ^2) := congrFun (comp_profile F s uL uR) p
  simp_rw [weakIntegrand, hcomp]
  exact integral_profile_divergence_of_bulk_eq_zero hs hL hR (hF.comp hL) (hF.comp hR) hPL hPR φ

/-- Rankine–Hugoniot at the traces suffices for the joined field to solve
the conservation law distributionally. -/
theorem isWeakSolution_profile_of_rankineHugoniot {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ}
    (hF : ContDiff ℝ 1 F) (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual F uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual F uR p = 0)
    (hRH : ∀ t, RankineHugoniot F (uL (interface s t)) (uR (interface s t)) (deriv s t)) :
    IsWeakSolution F (⊤ : Opens ℝ^2) (profile s uL uR) := by
  refine
    { u_locallyIntegrable :=
        (locallyIntegrable_profile hs.continuous hL.continuous.locallyIntegrable
          hR.continuous.locallyIntegrable).locallyIntegrableOn univ
      flux_locallyIntegrable := (locallyIntegrable_flux_profile hF.continuous hs.continuous
          hL.continuous hR.continuous).locallyIntegrableOn univ
      weak_eq := ?_ }
  intro φ
  rw [integral_weakIntegrand_profile hF hs hL hR hPL hPR]
  have hz (t : ℝ) : fluxJump F s uL uR t = 0 := fluxJump_eq_zero_iff.mpr (hRH t)
  simp only [hz, zero_mul, integral_zero]

/-- A curved shock with classical bulk fields is a weak solution exactly when
Rankine–Hugoniot holds at every point of its moving interface. -/
theorem isWeakSolution_profile_iff_rankineHugoniot {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ}
    (hF : ContDiff ℝ 1 F) (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual F uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual F uR p = 0) :
    IsWeakSolution F (⊤ : Opens ℝ^2) (profile s uL uR) ↔ ∀ t,
      RankineHugoniot F (uL (interface s t)) (uR (interface s t)) (deriv s t) := by
  constructor
  · intro hw
    have hz := eq_zero_of_integral_mul_trace_eq_zero hs
      (continuous_fluxJump hF.continuous hs hL.continuous hR.continuous)
      (fun φ ↦ by
        rw [← integral_weakIntegrand_profile hF hs hL hR hPL hPR]
        exact hw.weak_eq φ)
    exact fun t ↦ fluxJump_eq_zero_iff.mp (hz t)
  · exact isWeakSolution_profile_of_rankineHugoniot hF hs hL hR hPL hPR

end PDE.Hyperbolic.ConservationLaw.Scalar.Shock
