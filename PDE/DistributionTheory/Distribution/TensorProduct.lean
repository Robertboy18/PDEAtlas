/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.SliceFamily

/-!
# Tensor products of distributions

For scalar distributions `S` on `E` and `T` on `F`, their tensor product is the
distribution on `E × F` obtained by applying `T` to the moving right slices of a
test function and then applying `S`. The slice-family construction is continuous
linear in the canonical LF test-function topologies, so compact-convergence
precomposition gives a continuous distribution and continuous dependence on the
first factor.

We compute the action on arbitrary tests and on elementary test-function
tensor products, identify tensor products of Dirac masses, and prove the two
coordinate derivative laws.
-/

@[expose] public section

open TopologicalSpace
open scoped CompactConvergenceCLM Distributions

noncomputable section

namespace Distribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Tensor with a fixed distribution in the second variable, continuously in the first
distribution for the compact-convergence topology. -/
def tensorProductRightCLM
    (T : 𝓓'((⊤ : Opens F), ℝ)) :
    𝓓'((⊤ : Opens E), ℝ) →L[ℝ]
      𝓓'((⊤ : Opens (E × F)), ℝ) :=
  (TestFunction.applyDistributionToSliceRightCLM T).precompCompactConvergenceCLM ℝ

/-- The tensor product of two scalar distributions. -/
def tensorProduct
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens F), ℝ)) :
    𝓓'((⊤ : Opens (E × F)), ℝ) :=
  tensorProductRightCLM T S

/-- Fubini-type evaluation formula: `⟨S ⊗ T, Φ⟩ = ⟨S, x ↦ ⟨T, Φ(x, ·)⟩⟩`, the inner function
being the slice family `applyDistributionToSliceRight T Φ`. -/
@[simp]
theorem tensorProduct_apply
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens F), ℝ))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    tensorProduct S T Φ =
      S (TestFunction.applyDistributionToSliceRight T Φ) :=
  rfl

/-- A distribution tensor product factors on an elementary test-function tensor. -/
theorem tensorProduct_apply_testFunction_tensorProduct
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens F), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    tensorProduct S T (TestFunction.tensorProduct φ ψ) =
      S φ * T ψ := by
  rw [tensorProduct_apply]
  have hfamily :
      TestFunction.applyDistributionToSliceRight T
          (TestFunction.tensorProduct φ ψ) =
        (T ψ) • φ := by
    ext x
    rw [TestFunction.applyDistributionToSliceRight_apply,
      TestFunction.sliceRight_tensorProduct]
    simp [mul_comm]
  rw [hfamily, map_smul]
  simp [mul_comm]

/-- The tensor product of two Dirac masses is the Dirac mass at the product point. -/
@[simp]
theorem tensorProduct_delta_delta (x : E) (y : F) :
    tensorProduct (delta x) (delta y) =
      delta (x, y) := by
  ext Φ
  simp

/-- Differentiating a tensor product in the first coordinate differentiates its first factor. -/
theorem lineDerivCLM_tensorProduct_left
    (v : E)
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens F), ℝ)) :
    lineDerivCLM (v, (0 : F)) (tensorProduct S T) =
      tensorProduct (lineDerivCLM v S) T := by
  ext Φ
  rw [lineDerivCLM_apply, tensorProduct_apply,
    tensorProduct_apply, lineDerivCLM_apply,
    TestFunction.lineDerivCLM_applyDistributionToSliceRight]

/-- Differentiating a tensor product in the second coordinate differentiates its second factor. -/
theorem lineDerivCLM_tensorProduct_right
    (w : F)
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens F), ℝ)) :
    lineDerivCLM ((0 : E), w) (tensorProduct S T) =
      tensorProduct S (lineDerivCLM w T) := by
  ext Φ
  rw [lineDerivCLM_apply, tensorProduct_apply, tensorProduct_apply]
  have hfamily :
      TestFunction.applyDistributionToSliceRight (lineDerivCLM w T) Φ =
        -TestFunction.applyDistributionToSliceRight T
          (TestFunction.lineDerivCLM ℝ ((0 : E), w) Φ) := by
    ext x
    rw [TestFunction.applyDistributionToSliceRight_apply,
      lineDerivCLM_apply, TestFunction.lineDerivCLM_sliceRight]
    rfl
  rw [hfamily, map_neg]

end Distribution
