/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.Commutation
public import PDE.Analysis.Operator.ConstantCoefficient.Polynomial

/-!
# Polynomial operators on ordinary distributions

Polynomial evaluation uses the distributional directional derivatives.
Their commutation is proved on test functions, so the determinant reduction
below imposes no smoothness or temperateness on the distributions.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {Ω : Opens E}

/-- Directional derivatives commute as algebraic endomorphisms as well as
continuous linear maps. -/
theorem lineDerivEnd_commute (v w : E) :
    Commute (lineDerivCLM v : 𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, F)).toLinearMap
      (lineDerivCLM w).toLinearMap := by
  apply LinearMap.ext
  intro T
  exact congrArg (fun A : 𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, F) ↦ A T)
    (lineDerivCLM_commute v w).eq

/-- The constant-coefficient polynomial derivative operator on ordinary
distributions. -/
def polynomialLineDeriv (v : ι → E) :
    MvPolynomial ι ℝ →ₐ[ℝ] Module.End ℝ 𝓓'(Ω, F) :=
  PDE.Analysis.commutingPolynomialEval
    (fun i ↦ (lineDerivCLM (v i)).toLinearMap)
    (fun i j ↦ lineDerivEnd_commute (v i) (v j))

/-- A coordinate monomial differentiates in its specified direction. -/
@[simp]
theorem polynomialLineDeriv_X (v : ι → E) (i : ι) (T : 𝓓'(Ω, F)) :
    polynomialLineDeriv v (MvPolynomial.X i) T = lineDerivCLM (v i) T := by
  simp [polynomialLineDeriv]

/-- A distributional solution of a polynomial matrix system satisfies
the scalar determinant equation in every component. -/
theorem polynomialLineDeriv_determinant_annihilates
    [Fintype κ] [DecidableEq κ] (v : ι → E)
    (P : Matrix κ κ (MvPolynomial ι ℝ)) (T : κ → 𝓓'(Ω, F))
    (hT : ∀ i, ∑ j, polynomialLineDeriv v (P i j) (T j) = 0) :
    ∀ i, polynomialLineDeriv v P.det (T i) = 0 :=
  PDE.Analysis.polynomialDeterminant_annihilates
    (fun i ↦ (lineDerivCLM (v i)).toLinearMap)
    (fun i j ↦ lineDerivEnd_commute (v i) (v j)) P T hT

end Distribution
