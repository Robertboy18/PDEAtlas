/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Basic

/-!
# The Hamilton–Jacobi operator on first derivatives

Restrict a real linear derivative on `E × ℝ` to the spatial directions and
apply the Riesz map. Together with the derivative in the time direction,
this gives `u_t + H(Dₓu, x)`. Continuity of `H` in momentum and position is
therefore continuity of this operator in the contact point and derivative.
No finite-dimensional assumption is needed for this identification.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Evaluate the spatial Hamilton–Jacobi operator on a spacetime point and
its real linear first derivative. The spatial covector is identified with
a vector by the Hilbert-space Riesz map. -/
def spatialJetOperator (H : E → E → ℝ)
    (q : (E × ℝ) × ((E × ℝ) →L[ℝ] ℝ)) : ℝ :=
  q.2 (0, 1) + H
    ((InnerProductSpace.toDual ℝ E).symm
      (q.2.comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)))) q.1.1

/-- Joint continuity in momentum and position gives continuity on spacetime jets. -/
theorem continuous_spatialJetOperator {H : E → E → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) :
    Continuous (spatialJetOperator H) := by
  have htime : Continuous (fun q : (E × ℝ) × ((E × ℝ) →L[ℝ] ℝ) ↦ q.2 (0, 1)) :=
    ((ContinuousLinearMap.apply ℝ ℝ (0, 1)).continuous).comp continuous_snd
  have hspace : Continuous (fun q : (E × ℝ) × ((E × ℝ) →L[ℝ] ℝ) ↦
      (InnerProductSpace.toDual ℝ E).symm
        (q.2.comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)))) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (continuous_snd.clm_comp_const _)
  exact htime.add (hH.comp (hspace.prodMk (continuous_fst.comp continuous_fst)))

/-- The jet operator evaluated on a differentiable test agrees with its time
derivative plus the Hamiltonian of its spatial gradient. -/
theorem spatialJetOperator_fderiv {H : E → E → ℝ} {φ : E × ℝ → ℝ}
    {z : E × ℝ} (hφ : DifferentiableAt ℝ φ z) :
    spatialJetOperator H (z, fderiv ℝ φ z) =
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 := by
  simp only [spatialJetOperator, gradient_spaceSlice_eq hφ]

end HamiltonJacobi

end
