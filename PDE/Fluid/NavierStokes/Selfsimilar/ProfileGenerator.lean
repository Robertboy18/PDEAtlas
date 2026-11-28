/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileMild
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarGenerator
public import PDE.Analysis.Evolution.Semigroup.Complex.Perturbation

/-!
# The generator of the profile evolution contains `L₀ + B`

The evolution linearized at a self-similar profile is built from the free evolution `e^{tL₀}`,
`L₀ = Δ + ½(1 + ξ·∇)`, by Duhamel's formula with a first-order operator. With the coefficients
`b`, `c` of the profile, `T v = (b·∇) v + c v` and `B v = -Π T v`, where `Π` is the Leray
projection. Every element `x` of the domain of `L₀` is in the domain of the generator of the
profile evolution on vector `L²(ℝ³)`, with value `L₀ x + B x`. Here `B x` makes sense because
the domain of `L₀` lies in `H²`. Hou, Wang and Yang write the linearized operator `L_Ũ` in this
way, as `L₀ + B`.

The converse inclusion, that the domain of the generator is the domain of `L₀`, is not stated
here for general coefficients. For a divergence-free weak eigenfunction `v` with eigenvalue `μ`,
`exp_smul_eq_profileGain0_of_weakEigenEquation` gives the orbit `e^{μt} v` directly.

## Main results

* `hasGeneratorAt_profileSemigroup0_vectorLower`: for every coefficient pair with the bounds of
  orders zero and one and every `v ∈ H¹` in the domain of `L₀`, the generator of the profile
  evolution at `v` is `L₀ v - Π T v`.
* `hasGeneratorAt_profileSemigroup0_of_hasGeneratorAt`: the same for every `x` in the domain of
  `L₀`, with `T` applied to the `H²` field of `x`.

## How it works

The `H²` field of `x` comes from the resolvent: `x = R₁ (x - L₀ x)`, and `R₁` maps `L²` into `H²`
(`HeatEquation.WholeSpace.vectorLower_vectorSelfsimilarResolventH2_of_hasGeneratorAt`). For
`v ∈ H¹` the gaining path of the profile evolution starting at `v` is the profile evolution on
`H¹`, which is continuous up to time zero (`profileGain_vectorLower`). So the forcing
`-Π T S₁(s) v` of Duhamel's formula (`profileSemigroup0_duhamel_l2`) is continuous on `[0, ∞)`,
with the value `-Π T v` at `s = 0`, and the Duhamel integral has this derivative at `t = 0`
(`StronglyContinuousSemigroup.hasGeneratorAt_of_eq_orbit_add_duhamel`).

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.2, the linearized
  operator `L_Ũ` as a perturbation of `L₀`. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.Selfsimilar

open HeatEquation.WholeSpace

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ}

/-- **The generator of the profile evolution on the domain of `L₀`, for `H¹` fields.** Let
`v ∈ H¹` be in the domain of the generator `L₀` of the free evolution, with `L₀ v = y`. Then `v`
is in the domain of the generator of the profile evolution, with value `y - Π T v`, where
`T v = (b·∇) v + c v`. -/
theorem hasGeneratorAt_profileSemigroup0_vectorLower (hk : ProfileCoefficientBounds 0 b c)
    (hk' : ProfileCoefficientBounds (0 + 1) b c) {v : VectorH 3 1} {y : VectorH 3 0}
    (hv : (vectorSelfsimilarHeatSemigroup 3 0).HasGeneratorAt (vectorLower 3 0 v) y) :
    (profileSemigroup0 b c hk).HasGeneratorAt (vectorLower 3 0 v)
      (y - leraySobolev 3 0 (BoundedTransport.transport b c v)) := by
  have hg : Continuous fun s : ℝ ↦ profileSemigroup (0 + 1) b c hk' s.toNNReal v :=
    ((profileSemigroup (0 + 1) b c hk').continuous_orbit v).comp continuous_real_toNNReal
  have hf : Continuous fun s : ℝ ↦ -leraySobolev 3 0 (BoundedTransport.transport b c
      (profileSemigroup (0 + 1) b c hk' s.toNNReal v)) :=
    ((leraySobolev 3 0).continuous.comp
      ((BoundedTransport.transport b c).continuous.comp hg)).neg
  have h := StronglyContinuousSemigroup.hasGeneratorAt_of_eq_orbit_add_duhamel
    (S := profileSemigroup0 b c hk) (U := vectorSelfsimilarHeatSemigroup 3 0) hv hf ?_
  · simpa [sub_eq_add_neg] using h
  · intro t ht
    rw [StronglyContinuousSemigroup.realOrbit, StronglyContinuousSemigroup.realOrbit,
      profileSemigroup0_duhamel_l2, sub_eq_add_neg, StronglyContinuousSemigroup.duhamel,
      Real.coe_toNNReal t ht, ← intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [uIoc_of_le ht] at hs
    rw [← profileGain_zero hk, profileGain_vectorLower hk hk' hs.1 v,
      vectorSelfsimilarHeatSemigroup_apply, leraySobolev_vectorSelfsimilarHeat, map_neg]

/-- **`L₀ + B` is contained in the generator of the profile evolution.** Every `x` in the domain
of the generator `L₀` of the free evolution, with `L₀ x = y`, is in the domain of the generator
of the profile evolution, with value `y - Π T v`, where `v ∈ H¹` is the `H²` field of `x` with
one derivative forgotten. -/
theorem hasGeneratorAt_profileSemigroup0_of_hasGeneratorAt
    (hk : ProfileCoefficientBounds 0 b c) (hk' : ProfileCoefficientBounds (0 + 1) b c)
    {x y : VectorH 3 0} (hx : (vectorSelfsimilarHeatSemigroup 3 0).HasGeneratorAt x y) :
    (profileSemigroup0 b c hk).HasGeneratorAt x
      (y - leraySobolev 3 0 (BoundedTransport.transport b c (vectorLower 3 1
        (vectorSelfsimilarResolventH2 3 (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
          (x - y))))) := by
  have hlow := vectorLower_vectorSelfsimilarResolventH2_of_hasGeneratorAt (by norm_num) hx
  have h := hasGeneratorAt_profileSemigroup0_vectorLower hk hk'
    (v := vectorLower 3 1 (vectorSelfsimilarResolventH2 3 (by norm_num)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (x - y))) (y := y) (by rwa [hlow])
  rwa [hlow] at h

end NavierStokes.Selfsimilar
