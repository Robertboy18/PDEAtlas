/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.SecondVariation.CompactDomain
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import PDE.Analysis.Calculus.LocalExtrema

/-!
# Necessary positivity of the nonlinear second variation

At a local minimum along a classical variation, the integral of the density's
Hessian on that variation is nonnegative. The derivative identity is proved from
the continuous second jet; neither stationarity nor positivity is an assumption.

This is the second-variation inequality (11) of Evans, §8.1.3, for vector-valued
maps; the density may couple all components. The pointwise Legendre–Hadamard
condition, the systems analogue of Evans's (14), follows by localization in
`PDE.CalculusOfVariations.SecondVariation.Legendre`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.3, (11) and (14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

open Analysis

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u v : ℝ^n → ℝ^m}

/-- A local minimum along `u + t • v` has nonnegative integral second variation.
Local minimality is only required in a neighborhood of `t = 0`, exactly as for
the first-order necessary condition. No boundary regularity or boundary condition
is needed once this minimum hypothesis is given. -/
theorem integral_lagrangian_secondVariation_nonneg_of_isLocalMin
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hmin : IsLocalMin
      (fun t : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + t • v x)) 0) :
    0 ≤ ∫ x in Ω, fderiv ℝ (fderiv ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2))
      (jacobianMatrix u x, (u x, x))
      (jacobianMatrix v x, (v x, 0)) (jacobianMatrix v x, (v x, 0)) := by
  have hfirst := hasDerivAt_lagrangianAction hopen hbounded hL hu hv 0
  have hsecond := hasDerivAt_deriv_lagrangianAction hopen hbounded hL hu hv 0
  have hnonpos := hmin.neg.deriv_deriv_nonpos hfirst.continuousAt.neg
  let A (t : ℝ) := lagrangianAction Ω L (fun x ↦ u x + t • v x)
  change deriv (deriv (-A)) 0 ≤ 0 at hnonpos
  rw [deriv.neg'] at hnonpos
  change deriv (-(deriv A)) 0 ≤ 0 at hnonpos
  rw [deriv.neg, neg_nonpos] at hnonpos
  rw [show deriv (deriv A) 0 = _ from hsecond.deriv] at hnonpos
  simpa only [zero_smul, add_zero] using hnonpos

end PDE.CalculusOfVariations
