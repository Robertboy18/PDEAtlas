/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Sobolev
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.DistributionTheory.TestFunction.ProperPrecomposition

/-!
# Affine rescaling preserves the zero-boundary Sobolev space

The bounded Sobolev pullback sends supported smooth functions to supported
smooth functions. Density and closedness of `H¹₀` therefore prove preservation
of zero trace, without a boundary regularity assumption. The weak
chain rule identifies the rescaled first derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- Pullback by the affine ball chart preserves zero trace, by density of
supported smooth functions and closedness of the zero-boundary subspace. -/
theorem scaledBallSobolevPullback_mem_H10 (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (u : H¹₀(ball z (a * r))) :
    WeakChangeOfVariables.boundedW1pPullbackCLM
      (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
      isBounded_ball (u : H¹(ball z (a * r))) ∈
        (h10SubmoduleOn (n := n) (Ω := ball (0 : ℝ^n) r)).toSubmodule := by
  let P : H¹(ball z (a * r)) →L[ℝ] H¹(ball (0 : ℝ^n) r) :=
    WeakChangeOfVariables.boundedW1pPullbackCLM (p := 2)
    (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
    isBounded_ball
  refine DenseRange.induction_on (denseRange_testFunctionToH10Linear
    (n := n) (Ω := ball z (a * r))) u ?_ ?_
  · exact (h10SubmoduleOn (n := n) (Ω := ball (0 : ℝ^n) r)).isClosed'.preimage
      (P.comp h10SubtypeL).continuous
  · intro φ
    let ψ : TestFunctionOn n (ball (0 : ℝ^n) r) :=
      ⟨TestFunction.precompProper (ballHomeomorph z ha)
        (contDiff_scaledBallChart z ha r ⊤) (ballHomeomorph z ha).isProperMap φ.1, by
          intro y hy
          have hh := φ.2 (tsupport_comp_subset_preimage φ.1
            (ballHomeomorph z ha).continuous hy)
          exact (preimage_ball_mul z ha r).subset hh⟩
    have he : P (testFunctionToH10 φ : H¹(ball z (a * r))) =
        (testFunctionToH10 ψ : H¹(ball (0 : ℝ^n) r)) := by
      apply WkpSpaceOn.ext_of_base_ae isOpen_ball
      have hp := WeakChangeOfVariables.boundedW1pPullbackCLM_base_ae
        (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
        isBounded_ball (testFunctionToH10 φ : H¹(ball z (a * r)))
      have hφ := (ae_comp_ballHomeomorph_iff z ha r _).mpr
        (baseCoordCLM_testFunction_apply_ae φ)
      filter_upwards [hp, hφ, baseCoordCLM_testFunction_apply_ae ψ] with y hp hφ hψ
      exact hp.trans (hφ.trans hψ.symm)
    change P (testFunctionToH10 φ : H¹(ball z (a * r))) ∈ _
    rw [he]
    exact (testFunctionToH10 ψ).property

/-- Affine rescaling of a zero-boundary state, with its base and weak
derivatives identified almost everywhere. -/
theorem exists_scaledBallDirichletPullback (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (u : H¹₀(ball z (a * r))) :
    ∃ v : H¹₀(ball (0 : ℝ^n) r),
      (baseCoordCLM v : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        (fun y ↦ baseCoordCLM u (ballHomeomorph z ha y)) ∧
      ∀ i, (derivCoordCLM i v : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        fun y ↦ a * derivCoordCLM i u (ballHomeomorph z ha y) := by
  obtain ⟨v, hv, hD⟩ := exists_scaledBallSobolevPullback z ha r (u : H¹(ball z (a * r)))
  let P : H¹(ball z (a * r)) →L[ℝ] H¹(ball (0 : ℝ^n) r) :=
    WeakChangeOfVariables.boundedW1pPullbackCLM (p := 2)
    (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
    isBounded_ball
  have he : v = P (u : H¹(ball z (a * r))) :=
    WkpSpaceOn.ext_of_base_ae isOpen_ball _ _ (hv.trans
      (WeakChangeOfVariables.boundedW1pPullbackCLM_base_ae
        (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
        isBounded_ball (u : H¹(ball z (a * r)))).symm)
  have hv0 : v ∈ (h10SubmoduleOn (n := n) (Ω := ball (0 : ℝ^n) r)).toSubmodule := by
    rw [he]
    exact scaledBallSobolevPullback_mem_H10 z ha r u
  exact ⟨⟨v, hv0⟩, hv, hD⟩

end SobolevSpace.GraphSpace.MeanScaling
