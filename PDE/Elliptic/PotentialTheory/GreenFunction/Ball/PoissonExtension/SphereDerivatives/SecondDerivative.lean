/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.SphereDerivatives.Continuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep
public import PDE.FDeriv.Euclidean.Distance

/-!
# Second derivatives of the ball Poisson extension

`SphereDerivatives.FirstDerivative` shows that the singular sphere integral
`B(x) = ∫_{∂B(0,r)} g(y) ‖x - y‖⁻ⁿ dS(y)` has derivative
`B'(x)[v] = ∫ g(y) D(‖· - y‖⁻ⁿ)(x)[v] dS(y)` at interior points. We differentiate once
more: for fixed direction `v`, the scalar
function `x ↦ B'(x)[v]` is again Fréchet differentiable at every interior point, and its derivative
is the sphere integral of `g(y)` times the second derivative of the kernel,

`D²(‖· - y‖⁻ⁿ)(x)[v, w] = -n ⟪v, w⟫ / dⁿ⁺² + n (n + 2) ⟪v, x - y⟫ ⟪w, x - y⟫ / dⁿ⁺⁴`

with `d = ‖x - y‖`. The second term is written through the derivative of the inverse `(n+2)`-nd
power, `D(‖· - y‖⁻ⁿ⁻²)(x)[w] = -(n + 2) ⟪w, x - y⟫ / dⁿ⁺⁴`.

As in the first-order case, differentiation under the integral sign is justified by dominated
differentiation on a small ball around `x₀` that stays away from the sphere. This is the analytic
input for interior `C²` regularity (`InteriorRegularity`) and for the harmonicity computation in
`KernelLaplacian`.

## Main results

* `hasFDerivAt_sphereIntegral_invDistPowFDeriv_apply`: for `0 < r`, `g` continuous on the
  radius-`r` sphere, interior `x₀`, and any `v`, the map
  `x ↦ |r|ⁿ⁻¹ ∫ g(r • ω) D(‖· - y‖⁻ⁿ)(x)[v] dS(ω)` has the stated Fréchet derivative at `x₀`.
-/

@[expose] public section

namespace GreenFunction

open scoped BigOperators

open MeasureTheory
open PDE.Analysis
open PotentialTheory

variable {n : ℕ}

section SphereIntegralSecondDerivative

open scoped Topology

private theorem integrable_sphere_invDistPowFDeriv_apply
    {r : ℝ} (hr : 0 < r) {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) (v : ℝ^n) :
    Integrable
      (fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦
        g (r • (ω : ℝ^n)) *
          EuclideanDistance.invDistPowFDerivFormula n x₀ (r • (ω : ℝ^n)) v)
      ((volume : Measure ℝ^n).toSphere) := by
  have hy := continuous_sphere_smul (n := n) r
  have hK := EuclideanDistance.continuous_invDistPowFDerivFormula n continuous_const hy fun ω ↦
    dist_ne_zero.mp
      (distance_ne_zero_of_mem_ball_mem_sphere hx₀ (smul_unitSphere_mem_sphere hr.le ω))
  exact integrableOn_univ.1 (((hg.comp_continuous hy (smul_unitSphere_mem_sphere hr.le)).mul
    (hK.clm_apply continuous_const)).continuousOn.integrableOn_compact isCompact_univ)


private theorem aestronglyMeasurable_sphere_secondDerivativeIntegrand
    {r : ℝ} (hr : 0 < r) {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) (v : ℝ^n) :
    AEStronglyMeasurable
      (fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦
        (g (r • (ω : ℝ^n))) •
          (let y : ℝ^n := r • (ω : ℝ^n)
           let S : ℝ := (-(n : ℝ)) / dist x₀ y ^ (n + 2)
           let T : ℝ := (innerSL ℝ v) (x₀ - y)
           S • (innerSL ℝ v) +
            T • ((-(n : ℝ)) •
              EuclideanDistance.invDistPowFDerivFormula (n + 2) x₀ y)))
      ((volume : Measure ℝ^n).toSphere) := by
  have hy := continuous_sphere_smul (n := n) r
  have hne (ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ))) : dist x₀ (r • (ω : ℝ^n)) ≠ 0 :=
    distance_ne_zero_of_mem_ball_mem_sphere hx₀ (smul_unitSphere_mem_sphere hr.le ω)
  have hgω : Continuous fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦ g (r • (ω : ℝ^n)) :=
    hg.comp_continuous hy (smul_unitSphere_mem_sphere hr.le)
  have hK := EuclideanDistance.continuous_invDistPowFDerivFormula (n + 2) continuous_const hy
    fun ω ↦ dist_ne_zero.mp (hne ω)
  have hS : Continuous fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦
      (-(n : ℝ)) / dist x₀ (r • (ω : ℝ^n)) ^ (n + 2) :=
    continuous_const.div ((continuous_const.dist hy).pow _) fun ω ↦ pow_ne_zero _ (hne ω)
  have hT : Continuous fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦
      (innerSL ℝ v) (x₀ - r • (ω : ℝ^n)) :=
    (innerSL ℝ v).continuous.comp (continuous_const.sub hy)
  refine Continuous.aestronglyMeasurable ?_
  dsimp only
  exact hgω.smul ((hS.smul continuous_const).add (hT.smul (hK.const_smul (-(n : ℝ)))))

/-- Differentiate under the sphere integral sign a second time: for fixed `v`, the scalar function
`x ↦ ∮ g(y) * (d/dx)(|x-y|^{-n})[v] dS(y)` is Fréchet differentiable at interior points. -/
theorem hasFDerivAt_sphereIntegral_invDistPowFDeriv_apply {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) (v : ℝ^n) :
    HasFDerivAt
      (fun x : ℝ^n ↦
        (|r| ^ (n - 1) : ℝ) *
          ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
            g (r • (ω : ℝ^n)) * EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n)) v
              ∂((volume : Measure ℝ^n).toSphere))
      ((|r| ^ (n - 1) : ℝ) •
        ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          (g (r • (ω : ℝ^n))) •
            (let y : ℝ^n := r • (ω : ℝ^n)
             let S : ℝ := (-(n : ℝ)) / dist x₀ y ^ (n + 2)
             let T : ℝ := (innerSL ℝ v) (x₀ - y)
             S • (innerSL ℝ v) +
               T • ((-(n : ℝ)) •
                 EuclideanDistance.invDistPowFDerivFormula (n + 2) x₀ y))
            ∂((volume : Measure ℝ^n).toSphere)) x₀ := by
  classical
  let μ : Measure ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) := (volume : Measure ℝ^n).toSphere
  let F' : ℝ^n → ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) → ℝ^n →L[ℝ] ℝ := fun x ω ↦
    g (r • (ω : ℝ^n)) • EuclideanDistance.invDistPowSecondFDerivFormula n x (r • (ω : ℝ^n)) v
  obtain ⟨δ, hδpos, hδ⟩ := exists_ball_away_from_sphere (n := n) (r := r) (x₀ := x₀) hx₀
  have hball := Metric.ball_mem_nhds x₀ hδpos
  have hne {x : ℝ^n} (hx : x ∈ Metric.ball x₀ δ) (ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ))) :
      x ≠ r • (ω : ℝ^n) :=
    dist_pos.1 (hδpos.trans_le (le_dist_smul_of_mem_ball_away hr.le hδ hx ω))
  let A : ℝ := (n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖ * (δ ^ (n + 2))⁻¹
  have hy := continuous_sphere_smul (n := n) r
  have hI : HasFDerivAt (fun x : ℝ^n ↦ ∫ ω, g (r • (ω : ℝ^n)) *
      EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n)) v ∂μ) (∫ ω, F' x₀ ω ∂μ) x₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F' := F')
      (bound := fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦ A * |g (r • (ω : ℝ^n))|) hball
      (Filter.eventually_of_mem hball fun x hx ↦ Continuous.aestronglyMeasurable
        ((hg.comp_continuous hy (smul_unitSphere_mem_sphere hr.le)).mul
          ((EuclideanDistance.continuous_invDistPowFDerivFormula n continuous_const hy
            (hne hx)).clm_apply continuous_const)))
      (integrable_sphere_invDistPowFDeriv_apply hr hg hx₀ v)
      (aestronglyMeasurable_sphere_secondDerivativeIntegrand hr hg hx₀ v)
      (ae_of_all _ fun ω x hx ↦ ?_) (integrable_const_mul_abs_sphere_comp hr hg A)
      (ae_of_all _ fun ω x hx ↦
        (EuclideanDistance.hasFDerivAt_invDistPowFDerivFormula_apply (v := v) (hne hx ω)).const_mul
          (g (r • (ω : ℝ^n))))
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    gcongr
    refine (EuclideanDistance.norm_invDistPowFDerivFormula_apply_fderiv_le n (hne hx ω)).trans ?_
    dsimp only [A]
    gcongr
    exact le_dist_smul_of_mem_ball_away hr.le hδ hx ω
  exact hI.const_mul _


end SphereIntegralSecondDerivative

end GreenFunction
