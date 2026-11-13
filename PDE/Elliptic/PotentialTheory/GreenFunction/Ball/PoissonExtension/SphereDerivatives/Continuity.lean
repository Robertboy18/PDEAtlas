/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep

/-!
# Continuity and integrability for the ball Poisson kernel

The Poisson extension of a continuous `g : ℝ^n → ℝ` to the ball `B(0, r)` is

`u(x) = (r² - ‖x‖²) / (n α(n) r) · ∫_{∂B(0,r)} g(y) / ‖x - y‖ⁿ dS(y)`,

with the sphere integral parametrised by `ω ↦ r • ω` over the unit sphere. For `x` inside the ball
the denominator `‖x - y‖` is bounded below by `r - ‖x‖ > 0` uniformly over `y ∈ ∂B(0, r)`, so the
integrand is a continuous function of `(x, ω)` on `B(0, r) × Sⁿ⁻¹` and the integral depends
continuously on `x`. We collect that geometric separation, the resulting continuity of
`u` on the open ball, and the integrability of the sphere-parametrised integrand at each interior
point. Together with the uniform separation from the sphere on a small ball around `x`, these are
the hypotheses needed to differentiate under the integral sign in
`SphereDerivatives.FirstDerivative`.

## Main results

* `distance_pos_of_mem_ball_mem_sphere`, `sub_norm_le_distance_of_mem_sphere`,
  `exists_ball_away_from_sphere`: interior points are separated from the boundary sphere, with the
  quantitative bound `r - ‖x‖ ≤ dist x y` and a uniform version on a smaller ball around `x`.
* `integrable_poissonBall_integrand`: at each interior point the unit-sphere integrand
  `ω ↦ g(r • ω) / dist x (r • ω)ⁿ` is integrable for the sphere measure.
* `le_dist_smul_of_mem_ball_away`, `integrable_const_mul_abs_sphere_comp`: the separation and
  domination facts shared by the first- and second-derivative computations.

## Implementation notes

All integrals are taken over the unit sphere with the measure `Measure.toSphere` of Lebesgue
measure on `ℝ^n`; the radius `r` enters through the parametrisation `ω ↦ r • ω` and the Jacobian
factor `|r|ⁿ⁻¹` built into `sphereIntegral`, not through a rescaled measure. The boundary datum is
a function on all of `ℝ^n`; only its restriction to the sphere matters.
-/

@[expose] public section

namespace GreenFunction

open scoped BigOperators

open MeasureTheory
open PDE.Analysis
open PotentialTheory

variable {n : ℕ}

/-- Radial scaling of the unit sphere is continuous. -/
theorem continuous_sphere_smul (r : ℝ) :
    Continuous
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        r • (ω : ℝ^n)) := by
  have hr : Continuous (fun _ : Metric.sphere (0 : ℝ^n) 1 ↦ r) := continuous_const
  exact hr.smul continuous_subtype_val

/-- Scaling a point on the unit sphere by a nonnegative radius places it on the sphere of that
radius. -/
theorem smul_unitSphere_mem_sphere {r : ℝ} (hr : 0 ≤ r)
    (ω : Metric.sphere (0 : ℝ^n) (1 : ℝ)) :
    r • (ω : ℝ^n) ∈ Metric.sphere (0 : ℝ^n) r := by
  have hω := ω.property
  rw [Metric.mem_sphere, dist_zero_right] at hω ⊢
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hω]

/-- The sphere-valued second projection followed by subtype coercion is continuous. -/
theorem continuous_snd_sphere_val {X : Type*} [TopologicalSpace X] :
    Continuous
      (fun p : X × Metric.sphere (0 : ℝ^n) 1 ↦
        (p.2 : ℝ^n)) := by
  change Continuous
    (Subtype.val ∘
      (Prod.snd :
        X × Metric.sphere (0 : ℝ^n) 1 →
          Metric.sphere (0 : ℝ^n) 1))
  exact continuous_subtype_val.comp continuous_snd

/-- An interior point and a point on the boundary sphere have positive distance. -/
theorem distance_pos_of_mem_ball_mem_sphere {r : ℝ}
    {x y : ℝ^n}
    (hx : x ∈ Metric.ball (0 : ℝ^n) r) (hy : y ∈ Metric.sphere (0 : ℝ^n) r) :
    0 < dist x y :=
  dist_pos.mpr (Metric.sphere_disjoint_ball.ne_of_mem hy hx).symm

/-- An interior point is distinct from every point on the boundary sphere. -/
theorem distance_ne_zero_of_mem_ball_mem_sphere {r : ℝ}
    {x y : ℝ^n}
    (hx : x ∈ Metric.ball (0 : ℝ^n) r) (hy : y ∈ Metric.sphere (0 : ℝ^n) r) : dist x y ≠ 0 :=
  (distance_pos_of_mem_ball_mem_sphere (n := n) hx hy).ne'

/-- The radial gap `r - ‖x‖` is a lower bound for the distance from `x` to a radius-`r`
sphere point. -/
theorem sub_norm_le_distance_of_mem_sphere {r : ℝ}
    {x y : ℝ^n} (hy : y ∈ Metric.sphere (0 : ℝ^n) r) :
    r - ‖x‖ ≤ dist x y := by
  have hyr : ‖y‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy
  have hle : ‖y‖ - ‖x‖ ≤ ‖y - x‖ :=
    norm_sub_norm_le y x
  have : r - ‖x‖ ≤ ‖y - x‖ := by
    simpa [hyr] using hle
  simpa [dist_eq_norm, norm_sub_rev] using this

/-- Every point in an open ball has a smaller neighborhood uniformly separated from the boundary
sphere. -/
theorem exists_ball_away_from_sphere {r : ℝ}
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) :
    ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ y, y ∈ Metric.sphere (0 : ℝ^n) r →
      δ ≤ dist x y := by
  have hx₀lt : ‖x₀‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx₀
  -- Take a small ball around `x₀` that stays a fixed dist away from the sphere.
  let δ : ℝ := (r - ‖x₀‖) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨δ, hδpos, ?_⟩
  intro x hxx₀ y hy
  have hsub : ‖x - x₀‖ < δ := by
    simpa [dist_eq_norm] using hxx₀
  have hx_norm_le : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
    -- `x = (x - x₀) + x₀`
    simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (x - x₀) x₀)
  have hx_norm : ‖x‖ < ‖x₀‖ + δ := by
    have hlt : ‖x - x₀‖ + ‖x₀‖ < δ + ‖x₀‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_lt_add_right hsub ‖x₀‖)
    have : ‖x‖ < δ + ‖x₀‖ := lt_of_le_of_lt hx_norm_le hlt
    simpa [add_comm, add_left_comm, add_assoc] using this
  -- Subtracting from `r` reverses the inequality: `r - (‖x₀‖ + δ) < r - ‖x‖`.
  have haux : r - (‖x₀‖ + δ) = δ := by
    dsimp [δ]
    linarith
  have hδ_lt : δ < r - ‖x‖ := by
    -- `‖x‖ < ‖x₀‖ + δ`
    have : r - (‖x₀‖ + δ) < r - ‖x‖ := sub_lt_sub_left hx_norm r
    simpa [haux] using this
  have hdist_ge : r - ‖x‖ ≤ dist x y :=
    sub_norm_le_distance_of_mem_sphere (n := n) (x := x) hy
  exact le_of_lt (lt_of_lt_of_le hδ_lt hdist_ge)

/-- At every point in the open ball, the Poisson integrand on the unit sphere is integrable with
respect to surface measure. -/
theorem integrable_poissonBall_integrand {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    let Y : Type := ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ))
    let μ : Measure Y := (volume : Measure ℝ^n).toSphere
    Integrable (fun ω : Y ↦
      g (r • (ω : ℝ^n)) /
        dist x (r • (ω : ℝ^n)) ^ n) μ := by
  classical
  intro Y μ
  have : IsFiniteMeasureOnCompacts μ := by infer_instance
  have hYc : IsCompact (Set.univ : Set Y) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set Y))
  -- Continuity on `univ` implies integrability on the compact space.
  have hcont : Continuous fun ω : Y ↦
      g (r • (ω : ℝ^n)) /
        dist x (r • (ω : ℝ^n)) ^ n := by
    have hnum : Continuous fun ω : Y ↦ g (r • (ω : ℝ^n)) :=
      hg.comp_continuous (continuous_sphere_smul (n := n) r)
        (smul_unitSphere_mem_sphere hr.le)
    have hdist : Continuous fun ω : Y ↦ dist x (r • (ω : ℝ^n)) := by
      have hy : Continuous fun ω : Y ↦ r • (ω : ℝ^n) :=
        continuous_sphere_smul (n := n) r
      exact continuous_const.dist hy
    have hpow : Continuous fun ω : Y ↦
        dist x (r • (ω : ℝ^n)) ^ n := by
      exact hdist.pow n
    refine Continuous.div hnum hpow ?_
    intro ω
    have hy_mem : (r • (ω : ℝ^n)) ∈ Metric.sphere (0 : ℝ^n) r :=
      smul_unitSphere_mem_sphere (n := n) hr.le ω
    exact pow_ne_zero n <| distance_ne_zero_of_mem_ball_mem_sphere (n := n) hx hy_mem
  -- `IntegrableOn` on the compact set `univ`, then simplify.
  have : IntegrableOn (fun ω : Y ↦
      g (r • (ω : ℝ^n)) /
        dist x (r • (ω : ℝ^n)) ^ n) Set.univ μ :=
    (hcont.continuousOn.integrableOn_compact hYc)
  simpa [Measure.restrict_univ, IntegrableOn] using this

/-- On a ball `B(x₀, δ)` separated from the radius-`r` sphere by `δ`, every point is at distance
at least `δ` from each scaled unit-sphere point `r • ω`. -/
theorem le_dist_smul_of_mem_ball_away {r δ : ℝ} (hr : 0 ≤ r) {x₀ : ℝ^n}
    (hδ : ∀ x, dist x x₀ < δ → ∀ y, y ∈ Metric.sphere (0 : ℝ^n) r → δ ≤ dist x y)
    {x : ℝ^n} (hx : x ∈ Metric.ball x₀ δ) (ω : Metric.sphere (0 : ℝ^n) (1 : ℝ)) :
    δ ≤ dist x (r • (ω : ℝ^n)) :=
  hδ x (by simpa [Metric.mem_ball] using hx) _ (smul_unitSphere_mem_sphere (n := n) hr ω)

/-- The dominating function `ω ↦ A |g(r • ω)|` used for differentiation under the sphere
integral sign is integrable on the unit sphere. -/
theorem integrable_const_mul_abs_sphere_comp {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r)) (A : ℝ) :
    Integrable (fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦ A * |g (r • (ω : ℝ^n))|)
      ((volume : Measure ℝ^n).toSphere) := by
  let Y : Type := ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ))
  let μ : Measure Y := (volume : Measure ℝ^n).toSphere
  have : IsFiniteMeasureOnCompacts μ := by infer_instance
  have hYc : IsCompact (Set.univ : Set Y) := isCompact_univ
  have habs_cont : Continuous fun ω : Y ↦ |g (r • (ω : ℝ^n))| :=
    (hg.comp_continuous (continuous_sphere_smul (n := n) r)
      (smul_unitSphere_mem_sphere hr.le)).abs
  have habs_int_on :
      IntegrableOn (fun ω : Y ↦ |g (r • (ω : ℝ^n))|) Set.univ μ :=
    habs_cont.continuousOn.integrableOn_compact hYc
  have habs_int : Integrable (fun ω : Y ↦ |g (r • (ω : ℝ^n))|) μ := by
    simpa [IntegrableOn, Measure.restrict_univ] using habs_int_on
  exact habs_int.const_mul A

end GreenFunction
