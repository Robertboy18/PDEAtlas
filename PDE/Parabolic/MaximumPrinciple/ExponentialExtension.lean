/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.ExponentialExtension
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator

/-!
# Exponential extension of a parabolic operator

The elliptic exponential extension acts on each time slice. Its additional
coordinate is spatial, so the time derivative gains the same exponential
factor. Separate spatial C² and time differentiability
suffice for the exact identity.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open PDE (time)
open PDE.Analysis PDE.Common EllipticHarnack

variable {n : ℕ}

/-- Exponential extension absorbs an arbitrary signed potential into the
drift of the parabolic operator in one more spatial dimension. -/
theorem matrixParabolicOperator_exponentialExtension
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u : ℝ^n → ℝ → ℝ} {x : ℝ^(n + 1)} {t : ℝ}
    (hspace : ContDiffAt ℝ 2 (fun y ↦ u y t) (spatialPart x))
    (htime : DifferentiableAt ℝ (u (spatialPart x)) t) :
    matrixParabolicOperator
        (fun p s ↦ liftedPrincipal (fun y ↦ a y s) p)
        (fun p s ↦ liftedDrift (fun y ↦ b y s) (fun y ↦ c y s) p)
        (fun _ _ ↦ 0) (fun p s ↦ exponentialExtension (fun y ↦ u y s) p) x t =
      Real.exp (time x) * matrixParabolicOperator a b c u (spatialPart x) t := by
  rw [matrixParabolicOperator,
    matrixOperator_exponentialExtension (fun y ↦ a y t) (fun y ↦ b y t)
      (fun y ↦ c y t) hspace]
  simp only [exponentialExtension, deriv_const_mul _ htime, matrixParabolicOperator, mul_add]

end ParabolicMaximum
