/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A finite-dimensional projection with a prescribed kernel

The quotient map removes precisely the chosen subspace. When its quotient has
the same dimension as the desired target, a linear equivalence supplies the
remaining coordinates. Continuity then follows from finite dimensionality.

In `ℝ^3` this gives, for every nonzero `v`, a continuous surjection onto `ℝ^2` whose
kernel is the line through `v`.
-/

@[expose] public noncomputable section

open Module

namespace Submodule

/-- Realize a subspace as the kernel of a continuous surjection onto any
finite-dimensional space of the same dimension as its quotient. -/
theorem exists_surjective_continuousLinearMap_ker_eq
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : Submodule 𝕜 E) (h : finrank 𝕜 (E ⧸ p) = finrank 𝕜 F) :
    ∃ L : E →L[𝕜] F, Function.Surjective L ∧ LinearMap.ker L.toLinearMap = p := by
  let e : (E ⧸ p) ≃ₗ[𝕜] F := LinearEquiv.ofFinrankEq _ _ h
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap.comp p.mkQ), ?_, ?_⟩
  · exact e.surjective.comp p.mkQ_surjective
  · change LinearMap.ker (e.toLinearMap.comp p.mkQ) = p
    rw [LinearMap.ker_comp_of_ker_eq_bot _ e.ker, p.ker_mkQ]

end Submodule

namespace EuclideanSpace

/-- A nonzero direction in three dimensions is exactly the kernel of a
continuous surjection onto two dimensions. -/
theorem exists_surjective_projection_ker_span_singleton
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    ∃ L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      Function.Surjective L ∧
        LinearMap.ker L.toLinearMap = Submodule.span ℝ ({v} : Set _) := by
  apply Submodule.exists_surjective_continuousLinearMap_ker_eq
  rw [Submodule.finrank_quotient, finrank_span_singleton hv]
  simp

end EuclideanSpace
