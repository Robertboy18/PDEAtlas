/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.Notation

/-!
# Distributional Laplacians

Mathlib's canonical Laplacian on scalar distributions is the transpose of the
test-function Laplacian, and we compute it on Dirac masses. We also define `-Δ`,
the sign convention used by LeanPDE's fundamental solutions.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace Distribution

/-- The canonical distributional Laplacian is the transpose of the canonical
test-function Laplacian. The two signs from distributional differentiation cancel. -/
theorem laplacianCLM_apply_apply
    {n : ℕ} {Ω : Opens (ℝ^n)} (T : 𝓓'(Ω, ℝ))
    (φ : 𝓓(Ω, ℝ)) :
    LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'(Ω, ℝ) T φ =
      T (LineDeriv.laplacianCLM ℝ (ℝ^n)
        𝓓(Ω, ℝ) φ) := by
  rw [LineDeriv.laplacianCLM_eq_sum
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  simp_rw [lineDerivOp_eq_lineDerivCLM]
  simp only [_root_.sum_apply, lineDerivCLM_apply, neg_neg]
  rw [← map_sum]
  congr 1
  rw [LineDeriv.laplacianCLM_eq_sum
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ,
    TestFunction.lineDerivOp_eq_lineDerivCLM ℝ]

/-- The canonical distributional Laplacian of a Dirac mass acts by evaluating the
canonical test-function Laplacian at the pole. -/
theorem laplacianCLM_delta_apply
    {n : ℕ} (x : ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'((⊤ : Opens (ℝ^n)), ℝ) (delta x) φ =
      LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓((⊤ : Opens (ℝ^n)), ℝ) φ x := by
  rw [laplacianCLM_apply_apply, delta_apply]

/-- The negative of Mathlib's canonical distributional Laplacian on `ℝ^n`. -/
def negativeLaplacianCLM (n : ℕ) :
    𝓓'((⊤ : Opens (ℝ^n)), ℝ) →L[ℝ] 𝓓'((⊤ : Opens (ℝ^n)), ℝ) :=
  -LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'((⊤ : Opens (ℝ^n)), ℝ)

/-- The distributional negative Laplacian pairs a distribution with the
negative test-function Laplacian. -/
theorem negativeLaplacianCLM_apply
    {n : ℕ} (T : 𝓓'((⊤ : Opens (ℝ^n)), ℝ))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    negativeLaplacianCLM n T φ =
      -T (LineDeriv.laplacianCLM ℝ (ℝ^n)
        𝓓((⊤ : Opens (ℝ^n)), ℝ) φ) := by
  rw [negativeLaplacianCLM]
  simp only [neg_apply]
  rw [laplacianCLM_apply_apply]

end Distribution
