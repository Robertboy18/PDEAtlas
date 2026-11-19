/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# A weak divergence equation as a continuous functional

For an `L²` flux and load, the residual of `-div q = f` is continuous on
`H¹₀`. Density extends both the full weak equation and a localized
equation from smooth tests. The localized equation says nothing outside the
support of its cutoff.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The signed weak residual `∫ q · Dv - ∫ f v`. -/
def weakDivergenceFunctional (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω) :
    H¹₀(Ω) →L[ℝ] ℝ :=
  (∑ i, (innerSL ℝ (q i)).comp (derivCoordCLM i)) -
    (innerSL ℝ f).comp baseCoordCLM

/-- Evaluation is the sum of the derivative-coordinate pairings. -/
theorem weakDivergenceFunctional_apply
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω) (v : H¹₀(Ω)) :
    weakDivergenceFunctional q f v = (∑ i, ⟪q i, derivCoordCLM i v⟫) -
      ⟪f, baseCoordCLM v⟫ := by
  simp only [weakDivergenceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Vanishing on smooth compactly supported tests implies the full weak equation. -/
theorem weakDivergence_pairing_of_testFunctions
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (h : ∀ φ : TestFunctionOn n Ω,
      (∑ i, ⟪q i, derivCoordCLM i (testFunctionToH10 φ)⟫) =
        ⟪f, baseCoordCLM (testFunctionToH10 φ)⟫) (v : H¹₀(Ω)) :
    (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫ := by
  suffices weakDivergenceFunctional q f v = 0 by
    simpa only [weakDivergenceFunctional_apply, sub_eq_zero] using this
  refine DenseRange.induction_on denseRange_testFunctionToH10Linear v ?_ ?_
  · exact isClosed_eq (weakDivergenceFunctional q f).continuous continuous_const
  · intro φ
    exact (weakDivergenceFunctional_apply q f _).trans (sub_eq_zero.mpr (h φ))

/-- The localized equation extends by density without changing the solution
or the flux outside the test cutoff. -/
theorem weakDivergence_cutoff_pairing_of_testFunctions (hΩ : IsOpen Ω)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (h : ∀ φ : TestFunctionOn n Ω,
      (∑ i, ⟪q i, derivCoordCLM i (cutoffH10 hΩ κ (testFunctionToH10 φ))⟫) =
        ⟪f, baseCoordCLM (cutoffH10 hΩ κ (testFunctionToH10 φ))⟫)
    (v : H¹₀(Ω)) :
    (∑ i, ⟪q i, derivCoordCLM i (cutoffH10 hΩ κ v)⟫) =
      ⟪f, baseCoordCLM (cutoffH10 hΩ κ v)⟫ := by
  suffices weakDivergenceFunctional q f (cutoffH10 hΩ κ v) = 0 by
    simpa only [weakDivergenceFunctional_apply, sub_eq_zero] using this
  refine DenseRange.induction_on denseRange_testFunctionToH10Linear v ?_ ?_
  · exact isClosed_eq ((weakDivergenceFunctional q f).continuous.comp
      (cutoffH10 hΩ κ).continuous) continuous_const
  · intro φ
    exact (weakDivergenceFunctional_apply q f _).trans (sub_eq_zero.mpr (h φ))

end SobolevSpace.GraphSpace
