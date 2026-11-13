/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.Topology.TietzeExtension

public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.BoundaryDecay
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.Normalization
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep

/-!
# Boundary convergence of the ball Poisson extension

For `0 < r` and `g : ℝ^n → ℝ` continuous on the sphere `∂B(0, r)`, the Poisson extension
`u = poissonBallExtension r g` is given inside the ball `B(0, r)` by integrating `g` against the
Poisson kernel over the sphere. We prove that `u` attains the boundary values of `g`: for every
`x₀ ∈ ∂B(0, r)`, `u(x) → g(x₀)` as `x → x₀` from inside the ball. With the interior regularity
and harmonicity results this gives `poisson_formula_ball`, which is Evans's §2.2.4(c), Theorem 15
(Poisson's formula for ball) with `C²` regularity in part (i); the `C^∞` statement is
`contDiffOn_poissonBallExtension`.

## Main results

* `poissonBallExtension_tendsto_g_on_sphere`: `ε`-`δ` boundary convergence of the Poisson
  extension of data continuous on the sphere, at every point of the sphere.
* `poisson_formula_ball`: the Poisson extension of such `g` is `C²` and harmonic in `B(0, r)`
  and converges to `g` at the boundary.

## How it works

Evans leaves the proof of Theorem 15 as an exercise, similar to that of Theorem 14, whose step 3
splits the integral into the parts of the boundary near `x₀` and away from it. We split the datum
instead. After extending `g` from the sphere to a continuous function on `ℝ^n` with Mathlib's
Tietze extension theorem (`ContinuousMap.exists_restrict_eq`), a Urysohn cutoff from Mathlib's
`exists_continuous_zero_one_of_isClosed` writes `g - g(x₀)` as a piece of size at most `ε/2`
everywhere plus a piece that vanishes near `x₀`. Since the kernel is positive with total mass one
(`poissonBallExtension_one_eq_one_on_ball`), the extension of the first piece is at most `ε/2`,
and the extension of the second tends to zero by
`poissonBallExtension_tendsto_zero_of_eq_zero_nhds`.

## Implementation notes

The boundary datum is a function on all of `ℝ^n`, continuous on the sphere; only its restriction
to the sphere enters the integral. Convergence is stated in explicit `ε`-`δ` form rather than
with filters; `continuousOn_poissonBallDirichletSolution` uses it to prove continuity of the
Dirichlet solution on the closed ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), step 3 of the proof of Theorem 14, (35)-(36),
  pp. 38-39; §2.2.4(c), Poisson's formula (45) and Theorem 15 (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace GreenFunction

open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

section PoissonBallBoundaryConvergence

open scoped Pointwise

variable {n : ℕ}

private theorem poissonBallExtension_add_of_mem_ball {r : ℝ} (hr : 0 < r)
    {g₁ g₂ : ℝ^n → ℝ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    poissonBallExtension (n := n) r (fun y : ℝ^n ↦ g₁ y + g₂ y) x =
      poissonBallExtension (n := n) r g₁ x + poissonBallExtension (n := n) r g₂ x := by
  unfold poissonBallExtension
  have h₁ : Integrable
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        g₁ ((0 : ℝ^n) + r • (ω : ℝ^n)) /
          dist x ((0 : ℝ^n) + r • (ω : ℝ^n)) ^ n)
      ((volume : Measure ℝ^n).toSphere) := by
    simpa using integrable_poissonBall_integrand
      (n := n) (r := r) hr (g := g₁) hg₁.continuousOn (x := x) hx
  have h₂ : Integrable
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        g₂ ((0 : ℝ^n) + r • (ω : ℝ^n)) /
          dist x ((0 : ℝ^n) + r • (ω : ℝ^n)) ^ n)
      ((volume : Measure ℝ^n).toSphere) := by
    simpa using integrable_poissonBall_integrand
      (n := n) (r := r) hr (g := g₂) hg₂.continuousOn (x := x) hx
  have hSI :
      sphereIntegral n (fun y : ℝ^n ↦ (g₁ y + g₂ y) / dist x y ^ n) 0 r =
        sphereIntegral n (fun y : ℝ^n ↦ g₁ y / dist x y ^ n) 0 r +
          sphereIntegral n (fun y : ℝ^n ↦ g₂ y / dist x y ^ n) 0 r := by
    simpa only [add_div] using
      sphereIntegral_add
        (fun y : ℝ^n ↦ g₁ y / dist x y ^ n)
        (fun y : ℝ^n ↦ g₂ y / dist x y ^ n) 0 r h₁ h₂
  rw [hSI, mul_add]

private theorem poissonBallExtension_const_mul_one {r c : ℝ} (x : ℝ^n) :
    poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ c) x =
      c * poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ)) x := by
  unfold poissonBallExtension
  have hSI :
      sphereIntegral n (fun y : ℝ^n ↦ c / dist x y ^ n) 0 r =
        c * sphereIntegral n (fun y : ℝ^n ↦ (1 : ℝ) / dist x y ^ n) 0 r := by
    simpa [div_eq_mul_inv] using
      sphereIntegral_const_mul c (fun y : ℝ^n ↦ (dist x y ^ n)⁻¹) 0 r
  simp [hSI, mul_left_comm, mul_comm]

private theorem poissonBallExtension_abs_le_of_forall_abs_le [Fact (0 < n)] {r : ℝ}
    (hr : 0 < r) {g : ℝ^n → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y : ℝ^n, |g y| ≤ M) :
    ∀ x ∈ Metric.ball (0 : ℝ^n) r, |poissonBallExtension (n := n) r g x| ≤ M := by
  classical
  intro x hx
  have hone := poissonBallExtension_one_eq_one_on_ball (n := n) (r := r) hr x hx
  have hInt : Integrable (fun ω : ↑(Metric.sphere (0 : ℝ^n) 1) ↦
      g (r • (ω : ℝ^n)) / dist x (r • (ω : ℝ^n)) ^ n) (volume : Measure ℝ^n).toSphere :=
    integrable_poissonBall_integrand hr hg.continuousOn hx
  have hInt1 : Integrable (fun ω : ↑(Metric.sphere (0 : ℝ^n) 1) ↦
      (1 : ℝ) / dist x (r • (ω : ℝ^n)) ^ n) (volume : Measure ℝ^n).toSphere :=
    integrable_poissonBall_integrand hr continuous_const.continuousOn hx
  have hA : 0 ≤ (r ^ 2 - ‖x‖ ^ 2) / (n * unitBallVolume n * r) := by
    have hxr : ‖x‖ < r := by simpa using hx
    have := unitBallVolume_pos n
    exact div_nonneg (by nlinarith [norm_nonneg x]) (by positivity)
  rw [← mul_one M, ← hone]
  simp only [poissonBallExtension, PDE.Analysis.sphereIntegral, zero_add, abs_mul,
    abs_of_nonneg hA, abs_of_nonneg (pow_nonneg (abs_nonneg r) (n - 1))]
  rw [mul_left_comm M, mul_left_comm M]
  gcongr
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  refine integral_mono hInt.abs (hInt1.const_mul M) fun ω ↦ ?_
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ dist x (r • (ω : ℝ^n)) ^ n), mul_one_div]
  gcongr
  exact hM _


/-- The Poisson extension approaches continuous boundary data from within the ball. -/
theorem poissonBallExtension_tendsto_g_on_sphere {r : ℝ}
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r)) :
    ∀ x₀ ∈ Metric.sphere (0 : ℝ^n) r, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Metric.ball (0 : ℝ^n) r,
      dist x x₀ < δ → |poissonBallExtension (n := n) r g x - g x₀| < ε := by
  classical
  intro x₀ hx₀ ε hε
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨1, one_pos, fun x hx _ ↦
      absurd (dist_nonneg.trans_lt (Metric.mem_ball.mp hx)) (not_lt.mpr hr)⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := Metric.mem_sphere.mp hx₀
    rw [Subsingleton.elim x₀ 0, dist_self] at h
    linarith
  have : Fact (0 < n) := ⟨hn⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq Metric.isClosed_sphere
    (⟨_, hg.domRestrict⟩ : C(Metric.sphere (0 : ℝ^n) r, ℝ))
  have hEq : Set.EqOn g G (Metric.sphere (0 : ℝ^n) r) := fun y hy ↦
    (congrArg (fun F : C(Metric.sphere (0 : ℝ^n) r, ℝ) ↦ F ⟨y, hy⟩) hG).symm
  rw [poissonBallExtension_congr hr hEq, hEq hx₀]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.continuousAt_iff.mp G.continuous.continuousAt (ε / 2) (by linarith)
  -- Urysohn cutoff: `χ = 0` on `closedBall x₀ (δ₁ / 2)` and `χ = 1` outside `ball x₀ δ₁`.
  obtain ⟨χ, hχ0, hχ1, hχIcc⟩ := exists_continuous_zero_one_of_isClosed (X := ℝ^n)
    (Metric.isClosed_closedBall (x := x₀) (ε := δ₁ / 2)) Metric.isOpen_ball.isClosed_compl
    (Set.disjoint_left.2 fun y (hy : dist y x₀ ≤ δ₁ / 2) hy' ↦
      hy' (Metric.mem_ball.2 (by linarith)))
  let φ : ℝ^n → ℝ := fun y ↦ G y - G x₀
  let gFar : ℝ^n → ℝ := fun y ↦ χ y * φ y
  let gNear : ℝ^n → ℝ := fun y ↦ (1 - χ y) * φ y
  have hφ : Continuous φ := G.continuous.sub continuous_const
  have hgFar : Continuous gFar := χ.continuous.mul hφ
  have hgNear : Continuous gNear := (continuous_const.sub χ.continuous).mul hφ
  have hgFar0 : ∀ᶠ y in nhds x₀, gFar y = 0 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ (by linarith : 0 < δ₁ / 2)) fun y hy ↦ by
      simp [gFar, hχ0 (Metric.mem_closedBall.2 (le_of_lt hy))]
  have hgNear_bound (y : ℝ^n) : |gNear y| ≤ ε / 2 := by
    by_cases hy : y ∈ Metric.ball x₀ δ₁
    · have h := hδ₁ hy
      rw [Real.dist_eq] at h
      simp only [gNear, φ, abs_mul, abs_of_nonneg (sub_nonneg.2 (hχIcc y).2)]
      nlinarith [(hχIcc y).1, abs_nonneg (G y - G x₀)]
    · simp only [gNear, hχ1 hy, Pi.one_apply, sub_self, zero_mul, abs_zero]
      positivity
  obtain ⟨δ, hδpos, hδ⟩ :=
    poissonBallExtension_tendsto_zero_of_eq_zero_nhds hr hgFar hx₀ hgFar0 (ε / 2) (by linarith)
  refine ⟨δ, hδpos, fun x hx hxx₀ ↦ ?_⟩
  have hsplit : poissonBallExtension (n := n) r G x - G x₀ =
      poissonBallExtension (n := n) r gNear x + poissonBallExtension (n := n) r gFar x := by
    rw [← poissonBallExtension_add_of_mem_ball hr hgNear hgFar hx, ← mul_one (G x₀),
      ← poissonBallExtension_one_eq_one_on_ball (n := n) (r := r) hr x hx,
      ← poissonBallExtension_const_mul_one, sub_eq_iff_eq_add,
      ← poissonBallExtension_add_of_mem_ball (g₁ := fun y ↦ gNear y + gFar y) hr
        (hgNear.add hgFar) continuous_const hx]
    congr 1 with y
    simp only [gNear, gFar, φ]
    ring
  rw [hsplit]
  calc _ ≤ |poissonBallExtension (n := n) r gNear x| + |poissonBallExtension (n := n) r gFar x| :=
        abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt
        (poissonBallExtension_abs_le_of_forall_abs_le hr hgNear hgNear_bound x hx) (hδ x hx hxx₀)
    _ = ε := add_halves ε


/-- The Poisson extension is `C²` and harmonic in the ball and converges to
the prescribed continuous boundary data. -/
theorem poisson_formula_ball {n : ℕ} (r : ℝ) (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r)) :
    (∀ x ∈ Metric.ball (0 : ℝ^n) r,
        laplacian (n := n) (poissonBallExtension (n := n) r g) x = 0) ∧
      ContDiffOn ℝ 2 (poissonBallExtension (n := n) r g)
        (Metric.ball (0 : ℝ^n) r) ∧
      (∀ x₀ ∈ Metric.sphere (0 : ℝ^n) r, ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ Metric.ball (0 : ℝ^n) r,
          dist x x₀ < δ → |poissonBallExtension (n := n) r g x - g x₀| < ε) := by
  refine ⟨?_, contDiffOn_poissonBallExtension (m := 2) (n := n) hr hg, ?_⟩
  · intro x hx
    exact laplacian_poissonBallExtension_eq_zero (n := n) hr hg hx
  · exact poissonBallExtension_tendsto_g_on_sphere (n := n) hg

end PoissonBallBoundaryConvergence

end GreenFunction
