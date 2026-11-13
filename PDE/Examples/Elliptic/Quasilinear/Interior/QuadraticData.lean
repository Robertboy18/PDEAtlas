/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Examples.CalculusOfVariations.GradientEnergy.Density
public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.Analysis.Calculus.Gradient.HessianBounds
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Quadratic data for a signed nonlinear divergence equation

For the signed density
`p²/2 + (1-cos p)/4 + 2p - 3`, the function `u(x)=x²` has
flux `2x + sin(2x)/4 + 2` and load `-2(1+cos(2x)/4)`. On every bounded open
`Ω ⊆ ℝ`, `u` is a weak solution of `-div F'(∇u) = f` with this load
(`exists_quadratic_weakSolution`). Both `u` and the flux are `H¹` functions.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Quasilinear.Interior

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Examples.GradientEnergy
open scoped ENNReal RealInnerProductSpace Sobolev

/-- The function `x²`. -/
def quadratic (x : ℝ^1) : ℝ := x 0 ^ 2

/-- The flux of the quadratic profile for the signed density. -/
def quadraticFlux (x : ℝ^1) : ℝ :=
  2 * x 0 + Real.sin (2 * x 0) / 4 + 2

/-- The load `-(flux)' = -2(1 + cos(2x)/4)`. -/
def quadraticLoad (x : ℝ^1) : ℝ :=
  -2 * (1 + Real.cos (2 * x 0) / 4)

/-- `quadratic` is `C¹`. -/
theorem quadratic_contDiff : ContDiff ℝ 1 quadratic := by
  cas

/-- The flux is `C¹`. -/
theorem quadraticFlux_contDiff : ContDiff ℝ 1 quadraticFlux := by
  cas

/-- The derivative of `x²` is `2x`. -/
theorem quadratic_partial (x : ℝ^1) : (∂[0] quadratic) x = 2 * x 0 := by
  cas

/-- The derivative of the flux is minus the load. -/
theorem quadraticFlux_partial (x : ℝ^1) :
    (∂[0] quadraticFlux) x = -quadraticLoad x := by
  cas

/-- The gradient of the signed density, including its constant term `2`. -/
theorem signedDensity_gradient_coordinate (p : ℝ^1) :
    gradient signedDensity p 0 = p 0 + Real.sin (p 0) / 4 + 2 := by
  have h := inner_gradient_left (f := signedDensity)
    (x := p) (y := EuclideanSpace.single 0 1)
  have hc : gradient signedDensity p 0 = (∂[0] signedDensity) p := by
    simpa only [EuclideanSpace.inner_single_right, one_mul,
      RCLike.conj_to_real, partialDeriv] using h
  exact hc.trans (signedDensity_firstPartial p)

private theorem first_coordinate_of_smooth_base {Ω : Set (ℝ^1)}
    (hΩ : IsOpen Ω) (U : H¹(Ω)) (g : ℝ^1 → ℝ)
    (hg : ContDiff ℝ 1 g) (hU : baseRepresentative U =ᵐ[domainMeasure 1 Ω] g) :
    (U.val (singleDerivIndex 1 0) : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω]
      ∂[0] g := by
  have hw : HasWeakDerivativeOn Ω [0] g
      (U.val (singleDerivIndex 1 0) : ℝ^1 → ℝ) :=
    by simpa only [singleDerivIndex_toList] using
      (U.property (singleDerivIndex 1 0)).congr_ae hU Filter.EventuallyEq.rfl
  exact hw.unique_ae hΩ (hasWeakDerivativeOn_iteratedPartialDeriv_finite [0] hg)

private theorem quadratic_flux_pairing {Ω : Set (ℝ^1)}
    (u Q : H¹(Ω))
    (hdu : (u.val (singleDerivIndex 1 0) : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω]
      ∂[0] quadratic)
    (hQ : baseRepresentative Q =ᵐ[domainMeasure 1 Ω] quadraticFlux)
    (v : H¹₀(Ω)) :
    (∫ x, ⟪gradient signedDensity (∇ u x), ∇ (v : H¹(Ω)) x⟫
      ∂domainMeasure 1 Ω) = ⟪Q.val (baseIndex 1 1), derivCoordCLM 0 v⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [wkpGradientCLM_apply_ae u, gradientCLM_apply_ae v, hdu, hQ]
    with x hx hv hd hq
  change ⟪gradient signedDensity (∇ u x), ∇ (v : H¹(Ω)) x⟫ =
    ⟪Q.val (baseIndex 1 1) x, derivCoordCLM 0 v x⟫
  simp only [PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply,
    RCLike.conj_to_real, signedDensity_gradient_coordinate, hx, hv, hd,
    quadratic_partial]
  change _ = _ * baseRepresentative Q x
  rw [hq]
  rfl

private theorem quadratic_load_representative {Ω : Set (ℝ^1)}
    (Q : H¹(Ω))
    (hdQ : (Q.val (singleDerivIndex 1 0) : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω]
      ∂[0] quadraticFlux) :
    (-Q.val (singleDerivIndex 1 0) : DerivLp 1 2 Ω) =ᵐ[domainMeasure 1 Ω]
      quadraticLoad := by
  filter_upwards [Lp.coeFn_neg (Q.val (singleDerivIndex 1 0)), hdQ] with x hx hd
  change (-Q.val (singleDerivIndex 1 0)) x = _
  rw [hx]
  change -Q.val (singleDerivIndex 1 0) x = _
  rw [hd, quadraticFlux_partial, neg_neg]

private theorem quadratic_weakEquation {Ω : Set (ℝ^1)}
    (u Q : H¹(Ω))
    (hdu : (u.val (singleDerivIndex 1 0) : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω]
      ∂[0] quadratic)
    (hQ : baseRepresentative Q =ᵐ[domainMeasure 1 Ω] quadraticFlux)
    (v : H¹₀(Ω)) :
    (∫ x, ⟪gradient signedDensity (∇ u x), ∇ (v : H¹(Ω)) x⟫
      ∂domainMeasure 1 Ω) =
      ∫ x, (-Q.val (singleDerivIndex 1 0)) x * baseCoordCLM v x
        ∂domainMeasure 1 Ω := by
  rw [quadratic_flux_pairing u Q hdu hQ v]
  have hDQ : HasWeakDerivativeOn Ω [0] (Q.val (baseIndex 1 1))
      (Q.val (singleDerivIndex 1 0)) := by
    simpa only [singleDerivIndex_toList] using Q.property (singleDerivIndex 1 0)
  have hweak := weakDerivative_integrationByParts_H10 0 (Q.val (baseIndex 1 1))
    (Q.val (singleDerivIndex 1 0)) hDQ v
  rw [hweak, ← inner_neg_left, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ ↦ mul_comm _ _

/-- On every bounded open `Ω ⊆ ℝ` there are `u ∈ H¹(Ω)` represented by `x²` and `f ∈ L²`
represented by `quadraticLoad` with `∫ F'(∇u) · ∇v = ∫ f v` for every `v ∈ H¹₀(Ω)`. -/
theorem exists_quadratic_weakSolution {Ω : Set (ℝ^1)}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ (u : H¹(Ω)) (f : DerivLp 1 2 Ω),
      baseRepresentative u =ᵐ[domainMeasure 1 Ω] quadratic ∧
      (f : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω] quadraticLoad ∧
      ∀ v : H¹₀(Ω),
        (∫ x, ⟪gradient signedDensity (∇ u x), ∇ (v : H¹(Ω)) x⟫
          ∂domainMeasure 1 Ω) =
        ∫ x, f x * baseCoordCLM v x ∂domainMeasure 1 Ω := by
  obtain ⟨u, hu⟩ : ∃ u : H¹(Ω),
      baseRepresentative u =ᵐ[domainMeasure 1 Ω] quadratic :=
    exists_HkSpaceOn_of_contDiff_of_isBounded
    hbounded quadratic quadratic_contDiff
  obtain ⟨Q, hQ⟩ : ∃ Q : H¹(Ω),
      baseRepresentative Q =ᵐ[domainMeasure 1 Ω] quadraticFlux :=
    exists_HkSpaceOn_of_contDiff_of_isBounded
    hbounded quadraticFlux quadraticFlux_contDiff
  have hdu := first_coordinate_of_smooth_base hΩ u quadratic quadratic_contDiff hu
  have hdQ := first_coordinate_of_smooth_base hΩ Q quadraticFlux quadraticFlux_contDiff hQ
  let f := -Q.val (singleDerivIndex 1 0)
  have hf : (f : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω] quadraticLoad := by
    exact quadratic_load_representative Q hdQ
  exact ⟨u, f, hu, hf, quadratic_weakEquation u Q hdu hQ⟩

/-- `x²` equals `1` at both endpoints `±1`. -/
theorem quadratic_unit_endpoints :
    quadratic (EuclideanSpace.single 0 1) = 1 ∧
      quadratic (EuclideanSpace.single 0 (-1)) = 1 := by
  norm_num [quadratic]

end PDE.Examples.Quasilinear.Interior
