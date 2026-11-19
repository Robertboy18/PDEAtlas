/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Linear algebra of the wave equation

We prove linearity of the coordinate wave operator and the resulting
superposition principles for homogeneous and nonhomogeneous wave equations.

Conclusions stated with `SatisfiesPDEProblem` are pointwise residual identities.
Regularity hypotheses justify the operator algebra and are not part of those conclusions.
-/

@[expose] public section

open PDE (partialDeriv SatisfiesPDEProblem)

namespace WaveEquation

variable {n : ℕ}

/-- The wave operator preserves addition under the sharp local `C²` hypotheses. -/
theorem waveOperator_add {u v : ℝ^(n + 1) → ℝ} {xt : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u xt)
    (hv : ContDiffAt ℝ 2 v xt) :
    waveOperator (n := n) (fun x ↦ u x + v x) xt =
      waveOperator (n := n) u xt + waveOperator (n := n) v xt := by
  classical
  have hsecond (i : Fin (n + 1)) : (∂[i] (fun p ↦ (∂[i] (fun x ↦ u x + v x)) p)) xt = (∂[i]
            (fun p ↦ (∂[i] u) p)) xt + (∂[i]
            (fun p ↦ (∂[i] v) p)) xt := by
    simpa [Function.iterate_succ_apply] using (PDE.iterate_partialDeriv_add_of_contDiffAt
        (n := n + 1) i 2 hu hv)
  simp only [waveOperator, hsecond, Finset.sum_add_distrib]
  ring

/--
The wave operator commutes with multiplication by a scalar constant.

This holds for every function because Mathlib's total `fderiv` commutes with scalar multiplication
over a field.
-/
theorem waveOperator_const_mul (c : ℝ) (u : ℝ^(n + 1) → ℝ) (xt : ℝ^(n + 1)) :
    waveOperator (n := n) (fun x ↦ c * u x) xt = c * waveOperator (n := n) u xt := by
  have hpartial (i : Fin (n + 1)) (f : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) : (∂[i] (fun y ↦ c * f y)) x =
        c * (∂[i] f) x := by
    unfold partialDeriv
    change fderiv ℝ (c • f) x _ = _
    rw [fderiv_const_smul_field]
    rfl
  simp only [waveOperator, hpartial]
  rw [← Finset.mul_sum]
  ring

/-- The wave operator preserves subtraction under the sharp local `C²` hypotheses. -/
theorem waveOperator_sub {u v : ℝ^(n + 1) → ℝ} {xt : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u xt)
    (hv : ContDiffAt ℝ 2 v xt) :
    waveOperator (n := n) (fun x ↦ u x - v x) xt =
      waveOperator (n := n) u xt - waveOperator (n := n) v xt := by
  have hadd := waveOperator_add (n := n) hu hv.neg
  have hneg := waveOperator_const_mul (n := n) (-1 : ℝ) v xt
  calc
    waveOperator (n := n) (fun x ↦ u x - v x) xt = waveOperator (n := n) u xt +
          waveOperator (n := n) (fun x ↦ -v x) xt := by
      simpa [sub_eq_add_neg] using hadd
    _ = waveOperator (n := n) u xt - waveOperator (n := n) v xt := by
      rw [show waveOperator (n := n) (fun x ↦ -v x) xt =
        -waveOperator (n := n) v xt by simpa using hneg]
      ring

/--
Superposition for the nonhomogeneous wave equation.

If `u_tt - Δu = f` and `v_tt - Δv = g`, then `(u+v)_tt - Δ(u+v) = f+g`,
under the classical `C²` regularity needed for the wave operator algebra.
-/
theorem nonhomogeneousWaveEquation_add {U : Set (ℝ^(n + 1))} {f g u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U g) v) (hcu : ContDiff ℝ 2 u)
    (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun x ↦ f x + g x))
      (fun x ↦ u x + v x) := by
  refine nonhomogeneousWaveEquation.of_residual (n := n) ?_
  intro x hx
  rw [waveOperator_add (n := n) hcu.contDiffAt hcv.contDiffAt]
  have hu_res := nonhomogeneousWaveEquation.residual_eq (n := n) hu hx
  have hv_res := nonhomogeneousWaveEquation.residual_eq (n := n) hv hx
  linarith

/--
Scalar multiplication for the nonhomogeneous wave equation.

If `u_tt - Δu = f`, then `(c u)_tt - Δ(c u) = c f`.
-/
theorem nonhomogeneousWaveEquation_const_mul (c : ℝ) {U : Set (ℝ^(n + 1))} {f u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun x ↦ c * f x))
      (fun x ↦ c * u x) := by
  refine nonhomogeneousWaveEquation.of_residual (n := n) ?_
  intro x hx
  rw [waveOperator_const_mul (n := n) c u x]
  have hu_res := nonhomogeneousWaveEquation.residual_eq (n := n) hu hx
  rw [hu_res]

/--
Linear combinations for the nonhomogeneous wave equation.

If `u_tt - Δu = f` and `v_tt - Δv = g`, then
`(c₁u+c₂v)_tt - Δ(c₁u+c₂v) = c₁f+c₂g`.
-/
theorem nonhomogeneousWaveEquation_linear_combination (c₁ c₂ : ℝ) {U : Set (ℝ^(n + 1))}
    {f g u v : ℝ^(n + 1) → ℝ} (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U g) v) (hcu : ContDiff ℝ 2 u)
    (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun x ↦ c₁ * f x + c₂ * g x))
      (fun x ↦ c₁ * u x + c₂ * v x) := by
  have hcu_sol := nonhomogeneousWaveEquation_const_mul (n := n) c₁ hu
  have hcv_sol := nonhomogeneousWaveEquation_const_mul (n := n) c₂ hv
  exact nonhomogeneousWaveEquation_add (n := n) hcu_sol hcv_sol
    (hcu.const_smul c₁) (hcv.const_smul c₂)

/-- Negation for the nonhomogeneous wave equation. -/
theorem nonhomogeneousWaveEquation_neg {U : Set (ℝ^(n + 1))} {f u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun x ↦ -f x)) (fun x ↦ -u x) := by
  have hsource : (fun x : ℝ^(n + 1) ↦ -f x) =
        fun x ↦ (-1 : ℝ) * f x := by
    funext x
    ring
  have hsol : (fun x : ℝ^(n + 1) ↦ -u x) =
        fun x ↦ (-1 : ℝ) * u x := by
    funext x
    ring
  rw [hsource, hsol]
  exact nonhomogeneousWaveEquation_const_mul (n := n) (-1 : ℝ) hu

/-- Difference of two residual witnesses for forced wave equations. -/
theorem nonhomogeneousWaveEquation_sub {U : Set (ℝ^(n + 1))} {f g u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U g) v) (hcu : ContDiff ℝ 2 u)
    (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun x ↦ f x - g x))
      (fun x ↦ u x - v x) := by
  simpa [sub_eq_add_neg] using
    nonhomogeneousWaveEquation_linear_combination (n := n) (1 : ℝ) (-1 : ℝ) hu hv hcu hcv

/-- Equal-source forced-wave witnesses have a zero-source residual difference. -/
theorem nonhomogeneousWaveEquation_difference_same_source_zero {U : Set (ℝ^(n + 1))}
    {f u v : ℝ^(n + 1) → ℝ} (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u)
    (hv : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) v) (hcu : ContDiff ℝ 2 u)
    (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun _ : ℝ^(n + 1) ↦ 0))
      (fun x ↦ u x - v x) := by
  simpa using nonhomogeneousWaveEquation_sub (n := n) hu hv hcu hcv

/-- The zero field satisfies the forced-wave residual with zero source. -/
theorem nonhomogeneousWaveEquation_zero {U : Set (ℝ^(n + 1))} :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U (fun _ : ℝ^(n + 1) ↦ 0))
      (fun _ : ℝ^(n + 1) ↦ 0) := by
  refine nonhomogeneousWaveEquation.of_residual (n := n) ?_
  intro x hx
  simp [waveOperator]

end WaveEquation
