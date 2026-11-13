/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.LowerReturn
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.Basic

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic

/-!
# Assembling the prescribed clock into the gated field

The supplied slow and fast clock coordinates, together with the scalar
solution of `r' = b(X) - 4*r` through zero, form the candidate `(Z*r, X, Z)`.
The product rule gives its first coordinate equation. The other coordinates use
explicit reflected-cutoff, reflected-gate and feedback-cancellation conditions.

The cancellation is required at the candidate's first coordinate `Z*r`.
-/

@[expose] public noncomputable section

open PDE.Analysis.Evolution

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- The candidate formed from the supplied clock and the zero-initial
scalar solution satisfies the linear-fast gated field at the given time,
provided the reflected identities and feedback cancellation hold there.

Only continuity of the forcing is required globally. The clock equations and
three algebraic conditions concern this time alone, so ordinary derivatives at
closed-interval endpoints are covered as well. The forcing may be signed. -/
theorem hasDerivAt_prescribed_coupled_candidate {X Z b : ℝ → ℝ} {A B μ t : ℝ}
    (hforcing : Continuous (fun s ↦ b (X s)))
    (hX : HasDerivAt X (prescribedClockField A B (Z t) (X t) - μ * X t) t)
    (hZ : HasDerivAt Z ((2 - μ) * Z t) t) (hcutoffReflection : cutoff (-X t) = 1)
    (hgateReflection : b (-X t) = 0)
    (hfeedbackCancellation : let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0;
      cutoff (X t) * (clockFeedback A B (Z t * r t) + 4 * outerTransition A B (Z t)) = 0) :
    let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0;
      let q : ℝ → ℝ^3 := fun s ↦ !₂[Z s * r s, X s, Z s]; HasDerivAt q
      (GatedFlux.flux (fun s ↦ 2 * s) g cutoff (clockFeedback A B) b (q t) - μ • q t) t := by
  let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0
  let q : ℝ → ℝ^3 := fun s ↦ !₂[Z s * r s, X s, Z s]
  change HasDerivAt q
    (GatedFlux.flux (fun s ↦ 2 * s) g cutoff (clockFeedback A B) b (q t) - μ • q t) t
  change cutoff (X t) * (clockFeedback A B (Z t * r t) +
    4 * outerTransition A B (Z t)) = 0 at hfeedbackCancellation
  have hr : HasDerivAt r (b (X t) - 4 * r t) t :=
    hasDerivAt_scalarLinearSolution (a := fun _ : ℝ ↦ 4) continuous_const hforcing 0 0 t
  have hcoordinates : HasDerivAt (fun s : ℝ ↦ ![Z s * r s, X s, Z s])
      ![(2 - μ) * Z t * r t + Z t * (b (X t) - 4 * r t),
        prescribedClockField A B (Z t) (X t) - μ * X t, (2 - μ) * Z t] t := by
    refine hasDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact hZ.fun_mul hr
    · exact hX
    · exact hZ
  have hq : HasDerivAt q !₂[(2 - μ) * Z t * r t + Z t * (b (X t) - 4 * r t),
        prescribedClockField A B (Z t) (X t) - μ * X t, (2 - μ) * Z t] t :=
    (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hcoordinates
  apply hq.congr_deriv
  ext i
  fin_cases i
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    change (2 - μ) * Z t * r t + Z t * (b (X t) - 4 * r t) =
      -(2 * (Z t * r t)) + b (X t) * Z t - μ * (Z t * r t)
    ring
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    change prescribedClockField A B (Z t) (X t) - μ * X t =
      g (X t) + cutoff (-X t) * clockFeedback A B (Z t) +
        cutoff (X t) * clockFeedback A B (Z t * r t) - μ * X t
    rw [hcutoffReflection, one_mul]
    unfold prescribedClockField
    linear_combination -hfeedbackCancellation
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    change (2 - μ) * Z t = 2 * Z t - b (-X t) * (Z t * r t) - μ * Z t
    rw [hgateReflection, zero_mul, sub_zero]
    ring

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
