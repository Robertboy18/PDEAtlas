/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianNoncompactHessian
import CAS.ExactTactic

/-!
# The Poisson equation for a noncompact C¹ Newtonian source

The two integrable parts of the centered Hessian formula have zero trace.
The five diagonal local corrections supply the entire source. Absolute
convergence of the potential at one anchor is the only decay hypothesis.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter

namespace PotentialTheory

/-- The Newtonian integral solves the signed Poisson equation.
The centered near term and the exterior term are integrable before their
traces are summed; the five local corrections total exactly `-f X`. -/
theorem fundamentalSolution_five_integral_solves_poisson_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    -(∑ i : Fin 5, iteratedPartialDeriv [i, i]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X) = f X := by
  let N (i : Fin 5) (H : ℝ^5) :=
    iteratedPartialDeriv [i, i] (fundamentalSolution 5) H * (f (X - H) - f X)
  let T (i : Fin 5) (H : ℝ^5) :=
    iteratedPartialDeriv [i, i] (fundamentalSolution 5) H * f (X - H)
  have hformula (i : Fin 5) :=
    fundamentalSolution_five_integral_hessian_eq_centered_of_integrable_at_anchor
      f hf A X hInt i i 1 zero_lt_one
  have hN : (∑ i : Fin 5, ∫ H in Metric.ball (0 : ℝ^5) 1, N i H) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ (hformula i).1)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ^5))] with H hH
    rw [← Finset.sum_mul, fundamentalSolution_five_classicalHessian_trace_zero H hH,
      zero_mul]
    rfl
  have hT : (∑ i : Fin 5, ∫ H in (Metric.ball (0 : ℝ^5) 1)ᶜ, T i H) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ (hformula i).2.1)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ^5))] with H hH
    rw [← Finset.sum_mul, fundamentalSolution_five_classicalHessian_trace_zero H hH,
      zero_mul]
    rfl
  have htrace : (∑ i : Fin 5, iteratedPartialDeriv [i, i]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X) =
      (∑ i : Fin 5, ∫ H in Metric.ball (0 : ℝ^5) 1, N i H) +
        (∑ i : Fin 5, ∫ H in (Metric.ball (0 : ℝ^5) 1)ᶜ, T i H) -
        ∑ _i : Fin 5, f X / 5 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := (hformula i).2.2
    rw [ite_eq_left rfl] at hi
    exact hi
  rw [htrace, hN, hT]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  cas

end PotentialTheory
