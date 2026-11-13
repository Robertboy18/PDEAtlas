/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import PDE.Analysis.Convolution.LocalRegularity
import Mathlib.Topology.TietzeExtension

/-!
# Interior smoothness of the ball Poisson extension

For `0 < r` and boundary data continuous on the sphere `∂B(0, r)`, the Poisson extension
`poissonBallExtension r g` is `C^m` in the open ball for every `m : ℕ∞`
(`contDiffAt_poissonBallExtension`, `contDiffOn_poissonBallExtension`); with `m = ∞` this is part
(i) of Evans's §2.2.4(c), Theorem 15. For a fixed interior point, the boundary lies in an annulus
separated from that point, so a smooth compact cutoff removes the inverse-distance singularity
without changing the integral nearby. `MeasureTheory.contDiffAt_integral_smul_sub_of_annulus`,
which rests on Mathlib's `HasCompactSupport.contDiff_convolution_right`, then supplies all
derivative orders at once.

The usual `C²` statement used by the classical harmonicity predicate is the specialization
`m = 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(c), Theorem 15 (Poisson's formula for ball), part (i),
  p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Function MeasureTheory Metric Set
open scoped Topology ContDiff

namespace GreenFunction

/-- A sphere potential with any nonnegative integer inverse-distance power is
smooth in the open ball. Continuity of the boundary data suffices. -/
theorem contDiffAt_sphereIntegral_div_distance_pow
    {m : ℕ∞} {n k : ℕ} {r : ℝ} (hr : 0 < r) {g : ℝ^n → ℝ}
    (hg : ContinuousOn g (sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ ball (0 : ℝ^n) r) :
    ContDiffAt ℝ m
      (fun z : ℝ^n ↦ PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist z y ^ k) 0 r) x := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq isClosed_sphere
    (⟨_, hg.domRestrict⟩ : C(sphere (0 : ℝ^n) r, ℝ))
  have hEq : EqOn g G (sphere (0 : ℝ^n) r) := by
    intro y hy
    exact (congrArg (fun F : C(sphere (0 : ℝ^n) r, ℝ) ↦ F ⟨y, hy⟩) hG).symm
  have hfun : (fun z : ℝ^n ↦ PDE.Analysis.sphereIntegral n
        (fun y ↦ g y / dist z y ^ k) 0 r) =
      fun z : ℝ^n ↦ PDE.Analysis.sphereIntegral n (fun y ↦ G y / dist z y ^ k) 0 r := by
    funext z
    apply PDE.Analysis.sphereIntegral_congr_on_sphere hr
    intro y hy
    exact congrArg (fun v : ℝ ↦ v / dist z y ^ k) (hEq hy)
  rw [hfun]
  let Y := sphere (0 : ℝ^n) 1
  let σ : Measure Y := (volume : Measure (ℝ^n)).toSphere
  let yOf : Y → ℝ^n := fun θ ↦ r • (θ : ℝ^n)
  have hyOf : Continuous yOf := by
    dsimp [yOf]
    fun_prop
  let ν : Measure (ℝ^n) := σ.map yOf
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  have hsphere : ∀ᵐ y ∂ν, ‖y‖ = r := by
    apply (ae_map_iff hyOf.measurable.aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet).2
    apply Eventually.of_forall
    intro θ
    have hθ : ‖(θ : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    simp [yOf, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hr]
  have hxr : ‖x‖ < r := mem_ball_zero_iff.mp hx
  have hsource : ∀ᵐ y ∂ν, r - ‖x‖ ≤ dist x y ∧ dist x y ≤ ‖x‖ + r := by
    filter_upwards [hsphere] with y hy
    constructor
    · have htriangle := dist_triangle (0 : ℝ^n) x y
      simp only [dist_zero_left, hy] at htriangle
      linarith
    · simpa [hy] using dist_triangle x (0 : ℝ^n) y
  let K : ℝ^n → ℝ := fun z ↦ (‖z‖ ^ k)⁻¹
  have hK : ContDiffOn ℝ m K ({0}ᶜ : Set (ℝ^n)) := by
    intro z hz
    exact (((contDiffAt_norm ℝ hz).pow k).inv
      (pow_ne_zero k (norm_ne_zero_iff.mpr hz))).contDiffWithinAt
  have hpot := contDiffAt_integral_smul_sub_of_annulus hK
    (G.continuous.locallyIntegrable (μ := ν)) (sub_pos.mpr hxr) hsource
  have heq (z : ℝ^n) :
      (∫ y, G y • K (z - y) ∂ν) =
        ∫ θ : Y, G (yOf θ) / dist z (yOf θ) ^ k ∂σ := by
    have hmeas : Measurable (fun y : ℝ^n ↦ G y • K (z - y)) := by
      exact G.continuous.measurable.smul
        ((((measurable_const.sub measurable_id).norm).pow_const k).inv)
    rw [integral_map hyOf.measurable.aemeasurable hmeas.aestronglyMeasurable]
    congr 1
  have hsmooth := (contDiffAt_const (c := |r| ^ (n - 1))).mul hpot
  simpa only [heq, PDE.Analysis.sphereIntegral, yOf, σ, Y, zero_add] using hsmooth

/-- The ball Poisson extension of continuous boundary data has every derivative
order at an interior point. Taking `m = ∞` gives smoothness. -/
theorem contDiffAt_poissonBallExtension
    {m : ℕ∞} {n : ℕ} {r : ℝ} (hr : 0 < r) {g : ℝ^n → ℝ}
    (hg : ContinuousOn g (sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ ball (0 : ℝ^n) r) :
    ContDiffAt ℝ m (poissonBallExtension (n := n) r g) x := by
  have hA : ContDiff ℝ m (fun z : ℝ^n ↦
      (r ^ 2 - ‖z‖ ^ 2) / (n * PDE.Analysis.unitBallVolume n * r)) :=
    (contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _
  exact hA.contDiffAt.mul (contDiffAt_sphereIntegral_div_distance_pow hr hg hx)

/-- The ball Poisson extension has every derivative order throughout the open ball. -/
theorem contDiffOn_poissonBallExtension
    {m : ℕ∞} {n : ℕ} {r : ℝ} (hr : 0 < r) {g : ℝ^n → ℝ}
    (hg : ContinuousOn g (sphere (0 : ℝ^n) r)) :
    ContDiffOn ℝ m (poissonBallExtension (n := n) r g) (ball (0 : ℝ^n) r) :=
  fun _ hx ↦ (contDiffAt_poissonBallExtension hr hg hx).contDiffWithinAt

end GreenFunction
