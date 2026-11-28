/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.BallCorrection
public import PDE.Analysis.MeasureTheory.Lp.RestrictedCoordinates
public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Subcritical.ZeroTraceL4

/-!
# Two facts about fields on a ball and their zero extensions

A problem on the ball `B(0, ρ)` is compared with the whole space through the zero extension.
This module identifies the zero extension of a smooth test field supported in the ball, and
bounds the `L²` norm of a zero-boundary field by its `L⁴` norm on the ball. With the first, a
whole-space form evaluated at zero extensions is tested by `Stationary.testFieldH1 φ`. With the
second, a functional that is continuous in `L²` is continuous for the `L⁴` norm of the ball,
which is what a compactness argument on the ball needs. The constant of the second fact is the
norm of the inclusion `L⁴(B) → L²(B)` and is not computed.

## Main results

* `zeroExtendBall_ballTestField`: on every ball, the zero extension of the test velocity of a
  smooth solenoidal field `φ` supported in the ball is its `H¹` class `Stationary.testFieldH1 φ`.
* `exists_norm_toLp_le_mul_norm_solenoidalL4Embedding`: on every ball and for every faithful
  inclusion `H¹₀ → L⁴`, `‖u‖_{L²(B)} ≤ c ‖u‖_{L⁴(B)}` with a constant `c` that depends on the
  ball.

## How it works

The zero extension of the test velocity of `φ` has the values of `φ` almost everywhere
(`zeroExtendLp_baseCoordCLM_ballTestField_ae`), so it is the `H¹` class of `φ`. On a set of
finite measure `L⁴` embeds into `L²` (`MeasureTheory.Lp.piLpExponentInclusion`), and through a
faithful inclusion the `L⁴` realization of a zero-boundary field is mapped to its `L²` values.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace NavierStokes.Symmetry
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "Vb" ρ => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))

variable {ρ : ℝ} {φ : ℝ^3 → ℝ^3}

/-- **The zero extension of a test velocity.** For a smooth solenoidal field `φ` supported in
`B(0, ρ)`, the zero extension of its zero-boundary velocity on the ball is the `H¹(ℝ³)³` class
of `φ`. -/
theorem zeroExtendBall_ballTestField (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    zeroExtendBall ρ (ballTestField hφ hsupp) = Stationary.testFieldH1 φ hφ.1 hφ.2.1 := by
  ext i : 1
  apply wkpBaseCoordinateCLM_injective (n := 3) (p := 2) isOpen_univ
  apply Lp.ext
  have h1 := zeroExtendLp_baseCoordCLM_ballTestField_ae hφ hsupp i
  have h2 := Stationary.testFieldH1_base_ae hφ.1 hφ.2.1 i
  simp only [domainMeasure, Measure.restrict_univ]
  exact h1.trans h2.symm

/-- **`L²` against `L⁴` on a ball.** For a faithful inclusion `J : H¹₀(B) → L⁴(B)` of the ball
`B = B(0, ρ)` there is a constant `c ≥ 0` with `‖u‖_{L²(B)} ≤ c ‖u‖_{L⁴(B)}` for every
solenoidal zero-boundary field `u`, the `L⁴` norm taken of its realization through `J`. -/
theorem exists_norm_toLp_le_mul_norm_solenoidalL4Embedding (ρ : ℝ)
    (J : H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ u, (J u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ u : Vb ρ,
      ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤
        c * ‖solenoidalL4Embedding J u‖ := by
  have : IsFiniteMeasure (domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)) :=
    isFiniteMeasure_domainMeasure_of_isBounded Metric.isBounded_ball
  refine ⟨‖Lp.piLpExponentInclusion (μ := domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ))
    (by norm_num : (2 : ℝ≥0∞) ≤ 4) (Fin 3)‖, norm_nonneg _, fun u ↦ ?_⟩
  have h : Lp.piLpExponentInclusion (by norm_num : (2 : ℝ≥0∞) ≤ 4) (Fin 3)
      (solenoidalL4Embedding J u) = solenoidalMassCoordinates u := by
    refine PiLp.ext fun i ↦ Lp.ext ?_
    filter_upwards [Lp.piLpExponentInclusion_apply_ae (by norm_num : (2 : ℝ≥0∞) ≤ 4)
      (solenoidalL4Embedding J u) i,
      hJ ((u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) i)] with x hx hJx
    rw [hx]
    exact hJx
  rw [← norm_solenoidalMassCoordinates, ← h]
  exact ContinuousLinearMap.le_opNorm _ _

end NavierStokes.Nonuniqueness
