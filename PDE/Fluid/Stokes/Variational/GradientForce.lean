/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.Energy

/-!
# Gradient forces in the incompressible energy

A square integrable weak gradient does no work on a native divergence-free
zero-trace field. Consequently the zero velocity minimizes the energy for
such a force. The result uses weak derivatives and zero-trace density, with no
geometric condition on the domain.
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace IncompressibleFlow.Stokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- An L² weak gradient is orthogonal to every native divergence-free
zero-trace field. -/
theorem inner_gradient_force_eq_zero
    (p : DerivLp n 2 Ω) (d : Fin n → DerivLp n 2 Ω)
    (hd : ∀ i, HasWeakDerivativeOn Ω [i] (p : ℝ^n → ℝ) (d i : ℝ^n → ℝ))
    (v : H¹₀(Ω; ℝ^n)) (hv : ∇· v = 0) :
    ⟪Lp.euclideanTuple d, toLp v⟫ = 0 := by
  change ⟪Lp.euclideanTuple d, Lp.euclideanTuple (fun i ↦ baseCoordCLM (v i))⟫ = 0
  rw [Lp.inner_euclideanTuple]
  have hi (i : Fin n) :
      ⟪d i, baseCoordCLM (v i)⟫ = -⟪p, derivCoordCLM i (v i)⟫ := by
    linarith only [weakDerivative_integrationByParts_H10 i p (d i) (hd i) (v i)]
  simp only [hi, Finset.sum_neg_distrib, ← inner_sum,
    ← divergence_apply, hv, inner_zero_right, neg_zero]

/-- Zero velocity is a raw constrained minimizer for every L² weak-gradient
force. The Dirichlet term retains the full matrix gradient. -/
theorem energy_zero_le_of_gradient_force
    (p : DerivLp n 2 Ω) (d : Fin n → DerivLp n 2 Ω)
    (hd : ∀ i, HasWeakDerivativeOn Ω [i] (p : ℝ^n → ℝ) (d i : ℝ^n → ℝ))
    (v : H¹₀(Ω; ℝ^n)) (hv : ∇· v = 0) :
    energy (Lp.euclideanTuple d) 0 ≤ energy (Lp.euclideanTuple d) v := by
  simp only [energy, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    inner_zero_right, sub_self, inner_gradient_force_eq_zero p d hd v hv, sub_zero]
  positivity

end IncompressibleFlow.Stokes
