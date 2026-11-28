/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.BallCorrection
public import PDE.Fluid.NavierStokes.Stationary.ConvectionSkew

/-!
# The transport term of a ball problem as a whole-space convection form

The fixed-point problems for the profile are posed on balls `B(0, ρ)`, where the transport term
is a pairing of an `L⁴` field, an `L²` matrix and the `L⁴` values of a zero-boundary field.
Estimates such as the strain bound and the sharp Sobolev inequality are statements about fields
of `H¹(ℝ³)³`. This module shows that the pairing on the ball is a value of the whole-space
convection form `b(a, d, w) = ∫ (a·∇)d·w` as soon as the ball data are restrictions of
whole-space fields, so that those estimates apply on every ball. The argument uses nothing of the
ball beyond measurability, but only balls are stated.

## Main results

* `transportPairing_vectorL4Embedding_eq_convectionTrilinear`: on every ball, for data that are
  the restrictions of a whole-space `H¹` field `a` and of the weak gradient of another one `d`,
  the ball pairing is `b(a, d, W)`, with `W` the zero extension.
* `transportPairing_reconstruction_eq_convectionTrilinear`: for finite-rank data that are
  restrictions of whole-space data, the transport term of the reconstruction
  `u + ∑ⱼ ⟨qⱼ, u⟩ φⱼ` is `b(W + G W, G W, W)`, with `G` the whole-space finite-rank correction.

## How it works

The zero extension `W` of a zero-boundary field `u` of the ball vanishes outside the ball. So the
whole-space integral `∫ aᵢ ∂ᵢdₖ Wₖ` is an integral over the ball, and there the three factors are
the ball data. For the reconstruction, the restricted fields are those of `W + G W` and of `G W`
(`representative_reconstruction_ae`, `gradientRepresentative_reconstruction_ae`).
`integral_weakProfileDensity_eq_zero_of_ball` makes the same passage for a smooth test field in
place of `W`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace NavierStokes.Symmetry
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))
local notation "M" => PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 univ)
local notation "Vb" ρ => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))

variable {ρ : ℝ}

/-- **The transport pairing on a ball as a whole-space convection form.** Let `A` (an `L⁴`
field of the ball) and `D` (an `L²` matrix of the ball) be the restrictions of a whole-space
`H¹` field `a` and of the weak gradient of a whole-space `H¹` field `d`. Then the pairing of `A`
and `D` with the `L⁴` values of a zero-boundary field `u` is `b(a, d, W)`, where `W` is the zero
extension of `u`. -/
theorem transportPairing_vectorL4Embedding_eq_convectionTrilinear
    (J : H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ u, (J u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ))
    (A : PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)))
    (D : PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))) (a d : H)
    (hA : ∀ i, (A i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative a x i)
    (hD : ∀ k i, (D (k, i) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.gradientRepresentative d x k i)
    (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ContinuousLinearMap.transportPairing A D (IncompressibleFlow.vectorL4Embedding J u) =
      Stationary.convectionTrilinear a d (zeroExtendBall ρ u) := by
  rw [ContinuousLinearMap.transportPairing_eq_integral,
    Stationary.convectionTrilinear_eq_integral, integral_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun i _ ↦ (Stationary.integral_convectionTerm a d _ k i).1]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ (Stationary.integral_convectionTerm a d _ k i).1]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hext := Extension.Lp.zeroExtendLp_apply_ae measurableSet_ball (baseCoordCLM (u k))
  simp only [domainMeasure, Measure.restrict_univ] at hext
  -- Outside the ball the zero extension vanishes.
  have hzero : ∀ᵐ x ∂(volume : Measure (ℝ^3)), x ∉ Metric.ball (0 : ℝ^3) ρ →
      Stationary.representative a x i * Stationary.gradientRepresentative d x k i *
        Stationary.representative (zeroExtendBall ρ u) x k = 0 := by
    filter_upwards [hext] with x hx hxB
    have h0 : Stationary.representative (zeroExtendBall ρ u) x k = 0 := by
      change (Extension.Lp.zeroExtendLp measurableSet_ball (baseCoordCLM (u k)) : ℝ^3 → ℝ) x = 0
      rw [hx, Extension.Lp.extensionByZero, indicator_of_notMem hxB]
    rw [h0, mul_zero]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hzero]
  refine integral_congr_ae ?_
  filter_upwards [hA i, hD k i, hJ (u k), ae_restrict_of_ae hext,
    ae_restrict_mem measurableSet_ball] with x h1 h2 h3 h4 hxB
  rw [h1, h2]
  congr 1
  change (J (u k) : ℝ^3 → ℝ) x =
    (Extension.Lp.zeroExtendLp measurableSet_ball (baseCoordCLM (u k)) : ℝ^3 → ℝ) x
  rw [h3, h4, Extension.Lp.extensionByZero, indicator_of_mem hxB]

variable {F : Type*} [Fintype F]

/-- **The transport term of the finite-rank reconstruction.** Let `qB`, `φB`, `gradB` be the
restrictions to the ball of whole-space data `q`, `Φ`, `∇Φ`, and for a solenoidal zero-boundary
field `u` let `A` be the reconstruction `u + ∑ⱼ ⟨qⱼ, u⟩ φⱼ` as an `L⁴` field of the ball. Then
the transport term with the gradient of the correction `∑ⱼ ⟨qⱼ, u⟩ ∇φⱼ`, tested with `u`, is

`b(W + G W, G W, W)`,

where `W` is the zero extension of `u` and `G` the whole-space finite-rank correction. -/
theorem transportPairing_reconstruction_eq_convectionTrilinear
    (J : H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ u, (J u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ))
    (q : F → M) (Φ : F → H)
    (qB φB : F → PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (gradB : F → PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (hqB : ∀ j i, (qB j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (q j i : ℝ^3 → ℝ))
    (hφB : ∀ j i, (φB j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative (Φ j) x i)
    (hgradB : ∀ j k i, (gradB j (k, i) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ Stationary.gradientRepresentative (Φ j) x k i)
    (u : Vb ρ) (A : PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)))
    (hA : ∀ i, (A i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      ((solenoidalMassCoordinates u +
        ∑ j, ⟪qB j, solenoidalMassCoordinates u⟫ • φB j) i : ℝ^3 → ℝ)) :
    ContinuousLinearMap.transportPairing A
        (∑ j, ⟪qB j, solenoidalMassCoordinates u⟫ • gradB j) (solenoidalL4Embedding J u) =
      Stationary.convectionTrilinear
        (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
          finiteRankCorrection q Φ (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))))
        (finiteRankCorrection q Φ (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))))
        (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))) := by
  set W := zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
  set c : F → ℝ := fun j ↦ ⟪qB j, solenoidalMassCoordinates u⟫ with hc
  have hcq (j : F) : c j = ⟪q j, Stationary.massCLM W⟫ :=
    inner_solenoidalMassCoordinates_eq (hqB j) u
  have hG : finiteRankCorrection q Φ W = ∑ j, c j • Φ j := by
    rw [finiteRankCorrection_apply]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hcq j]
  rw [hG]
  refine transportPairing_vectorL4Embedding_eq_convectionTrilinear J hJ A _ _ _
    (fun i ↦ (hA i).trans
      (representative_reconstruction_ae (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) Φ c φB hφB i))
    (fun k i ↦ ?_) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
  -- The gradient of the correction alone: the reconstruction of the zero field.
  have h := gradientRepresentative_reconstruction_ae (0 : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
    Φ c gradB hgradB k i
  have h0 := Lp.coeFn_zero ℝ 2 (domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ))
  filter_upwards [h, h0] with x hx hx0
  rw [map_zero, zero_add] at hx
  rw [← hx]
  have hz : (derivCoordCLM i ((0 : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) k) :
      DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)) = 0 := by
    rw [PiLp.zero_apply, map_zero]
  rw [hz, hx0, Pi.zero_apply, zero_add]

end NavierStokes.Nonuniqueness
