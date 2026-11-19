/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.TensorProduct
public import PDE.FDeriv.SpaceTime

/-!
# Tensor tests in canonical Euclidean spacetime

The external product of a time test and a spatial test is pulled back through
the continuous linear spacetime coordinates. Its support and coordinate
derivatives are used in distributional slicing arguments.
-/

@[expose] public noncomputable section

namespace TestFunction

open Set TopologicalSpace PDE.Common
open PDE (time)
open scoped Distributions

variable {n : ℕ}

/-- A tensor test written in the canonical Euclidean spacetime coordinates. -/
def timeSpaceTensor (ψ : 𝓓((⊤ : Opens ℝ), ℝ))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : 𝓓((⊤ : Opens (ℝ^(n + 1))), ℝ) :=
  precompProper (timeSpaceContinuousLinearEquiv n)
    (timeSpaceContinuousLinearEquiv n).contDiff
    (timeSpaceContinuousLinearEquiv n).toHomeomorph.isProperMap (tensorProduct ψ φ)

/-- Evaluation of a tensor test in canonical spacetime. -/
@[simp] theorem timeSpaceTensor_apply
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (p : ℝ^(n + 1)) :
    timeSpaceTensor ψ φ p = ψ (time p) * φ (spatialPart p) :=
  rfl

/-- The slice of a tensor test is the corresponding scalar multiple of the
spatial test. -/
theorem timeSpaceTensor_timeSpaceCons
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (t : ℝ) (x : ℝ^n) :
    timeSpaceTensor ψ φ (timeSpaceCons t x) = ψ t * φ x := by
  simp

/-- The tensor support lies in the corresponding time slab. -/
theorem tsupport_timeSpaceTensor_subset
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {I : Set ℝ} (hψ : tsupport ψ ⊆ I) :
    tsupport (timeSpaceTensor ψ φ) ⊆ {p | p 0 ∈ I} := by
  have h : tsupport (timeSpaceTensor ψ φ) ⊆
      (timeSpaceContinuousLinearEquiv n) ⁻¹' (tsupport ψ ×ˢ tsupport φ) := by
    apply closure_minimal
    · intro p hp
      change ψ (time p) * φ (spatialPart p) ≠ 0 at hp
      exact ⟨subset_tsupport ψ (left_ne_zero_of_mul hp),
        subset_tsupport φ (right_ne_zero_of_mul hp)⟩
    · exact (ψ.hasCompactSupport.isClosed.prod φ.hasCompactSupport.isClosed).preimage
        (timeSpaceContinuousLinearEquiv n).continuous
  exact fun p hp ↦ hψ (h hp).1

/-- A spatial derivative acts on the spatial tensor factor. -/
theorem partialDeriv_timeSpaceTensor_succ
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (i : Fin n) (t : ℝ) (x : ℝ^n) :
    (∂[i.succ] (timeSpaceTensor ψ φ : ℝ^(n + 1) → ℝ)) (timeSpaceCons t x) =
      ψ t * (∂[i] (φ : ℝ^n → ℝ)) x := by
  rw [← PDE.partialDeriv_timeSpaceCons_spatial i _ t x
    ((timeSpaceTensor ψ φ).contDiff.differentiable (by simp)).differentiableAt]
  simp only [timeSpaceTensor_timeSpaceCons]
  exact PDE.partialDeriv_const_smul (ψ t)

/-- The time derivative acts on the time tensor factor. -/
theorem partialDeriv_timeSpaceTensor_zero
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (t : ℝ) (x : ℝ^n) :
    (∂[0] (timeSpaceTensor ψ φ : ℝ^(n + 1) → ℝ)) (timeSpaceCons t x) =
      deriv (ψ : ℝ → ℝ) t * φ x := by
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ x t
    ((timeSpaceTensor ψ φ).contDiff.differentiable (by simp)).differentiableAt]
  simp only [timeSpaceTensor_timeSpaceCons]
  exact ((ψ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt.mul_const
    (φ x)).deriv

end TestFunction
