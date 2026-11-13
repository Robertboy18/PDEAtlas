/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.MovingPlanes.Continuation
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder
import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import PDE.FDeriv.Laplacian.Congruence

/-!
# Radial symmetry of a positive semilinear solution on the unit ball

Let `f` be Lipschitz, and let `u` be `C²` up to the boundary of the unit ball, positive in the ball
and zero on the sphere, with `-Δu = f(u)` in the ball. Then `u(x) = v(‖x‖)` on the closed ball for a
continuous profile `v ≥ 0` that is strictly decreasing on `[0, 1]` with `v(1) = 0`
(`Elliptic.Semilinear.exists_strictAntiOn_radial_profile_of_lipschitz`). For `u` that is `C²` on
`ℝ^n`, the moving-plane comparison gives equality under the reflection in every hyperplane through
the center (`eq_reflection_zero`), equal values at points of equal norm (`eq_of_norm_eq`), and the
profile (`exists_strictAntiOn_radial_profile`). Strict decrease includes both endpoints, and the
case `n = 0` is included.

This is Evans's §9.5.2, Theorem 2, for the problem (2)-(3), with his hypothesis that `f` is
Lipschitz continuous.

## How it works

Evans proves (15_λ) for `0 < λ < 1`, deduces that `u` is symmetric in the plane through the center,
and then rotates the axes. We apply `le_reflection` at the plane through the center for both `e` and
`-e`, which gives equality under the reflection in that plane (`eq_reflection_zero`), and the
reflection that exchanges two points of equal norm gives `eq_of_norm_eq`. For `0 ≤ s < r ≤ 1`, the
strict comparison `lt_reflection` at the plane `⟪y, e⟫ = (s + r)/2` gives `u(r e) < u(s e)`, so the
profile `v(r) = u(r e)` is strictly decreasing. The final theorem extends `u` to a `C²` function on
`ℝ^n` that agrees with `u` on the closed ball, and the equation transfers because the Laplacians
agree near each point of the ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.5.2 (Radial symmetry), (2)-(3), pp. 555-556, the
  moving-plane notation and Theorem 2 (Radial symmetry), p. 558, and its proof, (15)-(20), p. 559.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

open Set Metric PDE.Analysis
open scoped Topology RealInnerProductSpace NNReal

namespace Elliptic.Semilinear.MovingPlanes

variable {n : ℕ} [Fact (0 < n)]
variable [SobolevSpace.Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)]
variable {u : ℝ^n → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}

/-- Moving the plane in both orientations gives equality under the reflection in the
hyperplane through the center orthogonal to `e`. -/
theorem eq_reflection_zero
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {e x : ℝ^n} (he : ‖e‖ = 1) (hx : x ∈ closedBall (0 : ℝ^n) 1) :
    u x = u (reflectHyperplane e 0 x) := by
  have hnorm (d y : ℝ^n) : ‖reflectHyperplane d 0 y‖ = ‖y‖ := by
    simp [reflectHyperplane]
  have hle (d : ℝ^n) (hd : ‖d‖ = 1) (y : ℝ^n) (hy : y ∈ ball (0 : ℝ^n) 1) :
      u y ≤ u (reflectHyperplane d 0 y) := by
    rcases lt_trichotomy 0 ⟪y, d⟫ with h | h | h
    · exact le_reflection hu hf hpde hpos hzero hd le_rfl y hy h
    · rw [reflectHyperplane_eq_self hd h.symm]
    · have hn := le_reflection hu hf hpde hpos hzero (by simpa using hd :
          ‖-d‖ = 1) (a := 0) le_rfl y hy (by simpa using h)
      have hR : reflectHyperplane (-d) 0 y = reflectHyperplane d 0 y := by
        simpa only [neg_zero] using reflectHyperplane_neg hd 0 y
      simpa only [hR] using hn
  have hxn : ‖x‖ ≤ 1 := by simpa using hx
  rcases lt_or_eq_of_le hxn with hi | hs
  · have hx' : x ∈ ball (0 : ℝ^n) 1 := by simpa using hi
    have hRx : reflectHyperplane e 0 x ∈ ball (0 : ℝ^n) 1 := by
      simpa [hnorm] using hi
    exact le_antisymm (hle e he x hx') (by
      simpa only [reflectHyperplane_involutive he 0 x] using
        hle e he (reflectHyperplane e 0 x) hRx)
  · rw [hzero x (by simpa using hs), hzero _ (by simpa [hnorm] using hs)]

/-- A positive solution has equal values at every pair of equal-norm points in the closed ball. -/
theorem eq_of_norm_eq
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x y : ℝ^n} (hx : x ∈ closedBall (0 : ℝ^n) 1) (hxy : ‖x‖ = ‖y‖) :
    u x = u y := by
  by_cases h : x = y
  · exact congrArg u h
  have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  let e := ‖x - y‖⁻¹ • (x - y)
  have he : ‖e‖ = 1 := by
    simp [e, norm_smul, hn]
  have hspan : (ℝ ∙ e) = ℝ ∙ (x - y) :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn)) _
  have hR : reflectHyperplane e 0 x = y := by
    simpa only [reflectHyperplane, hspan, mul_zero, zero_smul, add_zero] using
      Submodule.reflection_sub hxy
  simpa only [hR] using eq_reflection_zero hu hf hpde hpos hzero he hx

/-- The moving-plane inequalities give a continuous nonnegative profile strictly
decreasing on the entire radius interval, for a `C²` representative. -/
theorem exists_strictAntiOn_radial_profile
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc 0 1) ∧ StrictAntiOn v (Icc 0 1) ∧
      (∀ r ∈ Icc 0 1, 0 ≤ v r) ∧ v 1 = 0 ∧
      ∀ x ∈ closedBall (0 : ℝ^n) 1, u x = v ‖x‖ := by
  let e : ℝ^n := EuclideanSpace.single ⟨0, Fact.out⟩ 1
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  let v : ℝ → ℝ := fun r ↦ u (r • e)
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖r • e‖ = r := by
    simp [norm_smul, he, abs_of_nonneg hr]
  have hv1 : v 1 = 0 := by
    simpa [v] using hzero e (by simpa using he)
  have hanti : StrictAntiOn v (Icc 0 1) := by
    intro s hs r hr hsr
    have hrpos : 0 < r := hs.1.trans_lt hsr
    have hplane : ⟪r • e, e⟫ = r := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      ring
    have hR : reflectHyperplane e ((s + r) / 2) (r • e) = s • e := by
      rw [reflectHyperplane_eq he, hplane]
      module
    have hcmp := lt_reflection hu hf hpde hpos hzero he
      (a := (s + r) / 2) (by linarith [hs.1]) (r • e)
      (by simpa [hnorm r hr.1] using hr.2) (by rw [hplane]; linarith)
    simpa only [v, hR] using hcmp
  refine ⟨v, (hu.continuous.comp (continuous_id.smul continuous_const)).continuousOn,
    hanti, ?_, hv1, ?_⟩
  · intro r hr
    simpa only [hv1] using hanti.antitoneOn hr (by simp) hr.2
  · intro x hx
    exact eq_of_norm_eq hu hf hpde hpos hzero hx (hnorm ‖x‖ (norm_nonneg x)).symm

end Elliptic.Semilinear.MovingPlanes

namespace Elliptic.Semilinear

/-- Radial symmetry on the unit ball, Evans's §9.5.2, Theorem 2: a positive solution of
`-Δu = f(u)` that is `C²` up to the boundary and vanishes on the sphere is `v(‖x‖)` for a
continuous profile `v ≥ 0` that is strictly decreasing on `[0, 1]` with `v(1) = 0`. As in
Evans, `f` is Lipschitz; since `u` is bounded, a locally Lipschitz reaction can be replaced
by a Lipschitz one that agrees with it on the range of `u`. The zero-dimensional case is
included directly. No derivative or sign of the reaction, ambient extension, or comparison
is assumed. -/
theorem exists_strictAntiOn_radial_profile_of_lipschitz
    {n : ℕ} {u : ℝ^n → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f)
    (hu : SobolevSpace.ContDiffUpToBoundary 2 u (ball (0 : ℝ^n) 1))
    (hc : ContinuousOn u (closedBall (0 : ℝ^n) 1))
    (hpde : ∀ x ∈ ball (0 : ℝ^n) 1, -laplacian u x = f (u x))
    (hpos : ∀ x ∈ ball (0 : ℝ^n) 1, 0 < u x)
    (hzero : ∀ x ∈ sphere (0 : ℝ^n) 1, u x = 0) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc 0 1) ∧ StrictAntiOn v (Icc 0 1) ∧
      (∀ r ∈ Icc 0 1, 0 ≤ v r) ∧ v 1 = 0 ∧
      ∀ x ∈ closedBall (0 : ℝ^n) 1, u x = v ‖x‖ := by
  by_cases hn : n = 0
  · subst n
    have h0 : 0 < u 0 := hpos 0 (by simp)
    refine ⟨fun r ↦ u 0 * (1 - r), by fun_prop, ?_, ?_, by simp, ?_⟩
    · intro s _ r _ hsr
      dsimp
      nlinarith
    · intro r hr
      exact mul_nonneg h0.le (sub_nonneg.mpr hr.2)
    · intro x _
      rw [show x = (0 : ℝ^0) from Subsingleton.elim _ _]
      simp
  · let : Fact (0 < n) := ⟨Nat.pos_of_ne_zero hn⟩
    have hgraph : SobolevSpace.Boundary.HasContDiffGraphBoundary 2 (ball (0 : ℝ^n) 1) :=
      SobolevSpace.Boundary.Atlas.UnitBall.hasContDiffGraphBoundary n 2
    obtain ⟨U, hU, _, hUu⟩ :=
      hu.exists_contDiff_succ_extension 1 isOpen_ball isBounded_ball hgraph
    have hclosed : EqOn U u (closedBall (0 : ℝ^n) 1) :=
      hUu.of_subset_closure hU.continuous.continuousOn hc ball_subset_closedBall
        (by rw [closure_ball _ one_ne_zero])
    obtain ⟨atlas, _, _⟩ := hgraph.exists_c1ExtensionAtlas (by norm_num)
      isOpen_ball isBounded_ball
    let := atlas
    have hUpde (x : ℝ^n) (hx : x ∈ ball (0 : ℝ^n) 1) :
        -laplacian U x = f (U x) := by
      rw [EuclideanLaplacian.laplacian_congr_nhds
        (hUu.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)), hUu hx]
      exact hpde x hx
    obtain ⟨v, hvcont, hvanti, hvnonneg, hvzero, hrad⟩ :=
      MovingPlanes.exists_strictAntiOn_radial_profile hU hf hUpde
        (fun x hx ↦ (hUu hx).symm ▸ hpos x hx)
        (fun x hx ↦ (hclosed (sphere_subset_closedBall hx)).trans (hzero x hx))
    exact ⟨v, hvcont, hvanti, hvnonneg, hvzero, fun x hx ↦
      (hclosed hx).symm.trans (hrad x hx)⟩

end Elliptic.Semilinear
