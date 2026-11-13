/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Reflection.Ball
public import PDE.Analysis.InnerProductSpace.Ball.HalfSpace
public import PDE.FDeriv.Reflection.Hyperplane
public import PDE.Elliptic.Classical.MaximumPrinciple.Superharmonic
public import PDE.Elliptic.Classical.MaximumPrinciple.Hopf.Laplacian

/-!
# Strict comparison and the flat face of a moving cap

Let `u` be `C²` on `ℝ^n` with `-Δu = f(u)` in the unit ball, where `f` is Lipschitz with constant
`L`. For a unit vector `e` and `a ≥ 0`, let `w(y) = u(R y) - u(y)`, where `R` is the reflection in
the plane `⟪y, e⟫ = a`. At a point of the cap `{⟪y, e⟫ > a}` where `w ≥ 0`, `-Δw + L w ≥ 0`
(`neg_laplacian_reflection_sub_add_mul_nonneg`). If `a > 0`, `u` is positive in the ball and zero on
the sphere, and `w ≥ 0` in the cap, then `w > 0` on the cap and on its spherical boundary
(`lt_reflection_of_le_reflection`), and `u` has negative derivative in the direction `e` on the flat
face inside the ball (`fderiv_neg_on_plane_of_le_reflection`).

These are Evans's (18) and (19) in the proof of §9.5.2, Theorem 2, at a plane where weak comparison
holds.

## How it works

Evans writes `-Δw = -c w` with a coefficient `c` defined by integrating `f'` and applies his
Lemma 1, the strong maximum principle and Hopf's lemma for a bounded zeroth-order coefficient of
either sign. We do not differentiate `f`. Since `w ≥ 0`, the Lipschitz bound
`|f(u(R y)) - f(u(y))| ≤ L w(y)` gives `-Δw + L w ≥ 0` with the constant coefficient `L ≥ 0`, so the
usual strong maximum principle on the connected cap
(`EllipticMaximum.pos_of_nonneg_of_neg_laplacian_add_mul_nonneg`) and Hopf's lemma in a ball inside
the cap tangent to the flat face
(`EllipticMaximum.hopf_fderiv_neg_of_pos_of_neg_laplacian_add_mul_nonneg`) apply. Points of the cap
near the pole `e`, where `w(e) = u(R e) > 0`, show that `w` is not identically zero. On the flat
face `R` fixes the point and reverses `e`, so the derivative of `w` in the direction `e` is `-2`
times that of `u`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.5.2 (Radial symmetry), Lemma 1 (A refinement of Hopf's
  Lemma), p. 556, and the proof of Theorem 2 (Radial symmetry), (18)-(19), p. 559.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace Elliptic.Semilinear.MovingPlanes

open Set Metric PDE.Analysis
open scoped Topology RealInnerProductSpace NNReal

variable {n : ℕ} {u : ℝ^n → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}

/-- A nonnegative reflection difference is a supersolution with constant potential
equal to the reaction's Lipschitz constant. -/
theorem neg_laplacian_reflection_sub_add_mul_nonneg
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    {e x : ℝ^n} {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (hx : x ∈ ball (0 : ℝ^n) 1) (hcoord : a < ⟪x, e⟫)
    (hcomp : u x ≤ u (reflectHyperplane e a x)) :
    0 ≤ -laplacian (fun y ↦ u (reflectHyperplane e a y) - u y) x +
      (L : ℝ) * (u (reflectHyperplane e a x) - u x) := by
  have hxR : reflectHyperplane e a x ∈ ball (0 : ℝ^n) 1 := by
    have hxn : ‖x‖ < 1 := by simpa using hx
    simpa using (norm_reflectHyperplane_le he ha hcoord.le).trans_lt hxn
  have hR := hu.comp (contDiff_reflectHyperplane e a 2)
  change 0 ≤ -laplacian (fun y ↦ (u ∘ reflectHyperplane e a) y - u y) x +
    (L : ℝ) * (u (reflectHyperplane e a x) - u x)
  rw [PDE.laplacian_sub _ _ x hR.contDiffAt hu.contDiffAt]
  rw [laplacian_comp_reflectHyperplane_at e a x hu.contDiffAt]
  have hLip := hf.le_add_mul (u x) (u (reflectHyperplane e a x))
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hcomp)] at hLip
  linarith [hpde x hx, hpde (reflectHyperplane e a x) hxR]

/-- At positive displacement, weak reflection comparison improves to strict comparison
throughout the cap, including the spherical part of its closure. This is Evans's (18) in
§9.5.2. -/
theorem lt_reflection_of_le_reflection
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {e : ℝ^n} {a : ℝ} (he : ‖e‖ = 1) (ha : 0 < a)
    (hcomp : ∀ y ∈ ball (0 : ℝ^n) 1,
      a < ⟪y, e⟫ → u y ≤ u (reflectHyperplane e a y)) :
    ∀ x ∈ closedBall (0 : ℝ^n) 1,
      a < ⟪x, e⟫ → u x < u (reflectHyperplane e a x) := by
  let Ω := ball (0 : ℝ^n) 1 ∩ {y | a < ⟪y, e⟫}
  let w : ℝ^n → ℝ := fun y ↦ u (reflectHyperplane e a y) - u y
  have hw : ContDiff ℝ 2 w := (hu.comp (contDiff_reflectHyperplane e a 2)).sub hu
  have hopen : IsOpen Ω := isOpen_ball.inter (isOpen_lt continuous_const
    (continuous_id.inner continuous_const))
  intro x hx hcoord
  have hxn : ‖x‖ ≤ 1 := by simpa using hx
  have hi : ⟪x, e⟫ ≤ ‖x‖ := by simpa [he] using real_inner_le_norm x e
  have ha1 : a < 1 := hcoord.trans_le (hi.trans hxn)
  have hsphere (y : ℝ^n) (hy : ‖y‖ = 1) (hycoord : a < ⟪y, e⟫) :
      0 < w y := by
    have hyR : reflectHyperplane e a y ∈ ball (0 : ℝ^n) 1 := by
      simpa [hy] using norm_reflectHyperplane_lt he ha hycoord
    dsimp [w]
    rw [hzero y (by simp [hy]), sub_zero]
    exact hpos _ hyR
  rcases lt_or_eq_of_le hxn with hinside | hsph
  · have hecoord : a < ⟪e, e⟫ := by simpa [real_inner_self_eq_norm_sq, he] using ha1
    have heclosure : e ∈ closure Ω := by
      apply (isOpen_lt continuous_const
        (continuous_id.inner continuous_const)).closure_inter
      exact ⟨by simp [closure_ball _ one_ne_zero, he], hecoord⟩
    obtain ⟨y, hypos, hyΩ⟩ := mem_closure_iff.mp heclosure {y | 0 < w y}
      (isOpen_lt continuous_const hw.continuous) (hsphere e he hecoord)
    have hpositive := EllipticMaximum.pos_of_nonneg_of_neg_laplacian_add_mul_nonneg
      hopen (convex_ball_inter_inner_gt e a 1).isPreconnected
      (fun _ _ ↦ hw.contDiffAt)
      (fun y hy ↦ sub_nonneg.mpr (hcomp y hy.1 hy.2))
      (fun y hy ↦ neg_laplacian_reflection_sub_add_mul_nonneg hu hf hpde he ha.le
        hy.1 hy.2 (hcomp y hy.1 hy.2)) ⟨y, hyΩ, hypos⟩
    exact sub_pos.mp (hpositive x ⟨by simpa using hinside, hcoord⟩)
  · exact sub_pos.mp (hsphere x hsph hcoord)

/-- Weak reflection comparison at a positive plane gives a strictly negative derivative
on its flat face inside the ball, using an interior tangent ball. This is Evans's (19) in
§9.5.2. -/
theorem fderiv_neg_on_plane_of_le_reflection
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {e x : ℝ^n} {a : ℝ} (he : ‖e‖ = 1) (ha : 0 < a)
    (hcomp : ∀ y ∈ ball (0 : ℝ^n) 1,
      a < ⟪y, e⟫ → u y ≤ u (reflectHyperplane e a y))
    (hx : x ∈ ball (0 : ℝ^n) 1) (hplane : ⟪x, e⟫ = a) :
    fderiv ℝ u x e < 0 := by
  obtain ⟨R, hR, hball, hdist, hnormal⟩ :=
    exists_ball_subset_unitBall_cap (by simpa using hx) he hplane
  let w : ℝ^n → ℝ := fun y ↦ u (reflectHyperplane e a y) - u y
  have hw : ContDiff ℝ 2 w := (hu.comp (contDiff_reflectHyperplane e a 2)).sub hu
  have hxR : reflectHyperplane e a x = x := reflectHyperplane_eq_self he hplane
  have hstrict := lt_reflection_of_le_reflection hu hf hpde hpos hzero he ha hcomp
  have hh := EllipticMaximum.hopf_fderiv_neg_of_pos_of_neg_laplacian_add_mul_nonneg
    (u := w) hR L.coe_nonneg hdist (by simp [w, hxR]) hw.continuous.continuousOn
    (fun _ _ ↦ hw.contDiffAt)
    (fun y hy ↦ sub_pos.mpr
      (hstrict y (ball_subset_closedBall (hball hy).1) (hball hy).2))
    (fun y hy ↦ neg_laplacian_reflection_sub_add_mul_nonneg hu hf hpde he ha.le
      (hball hy).1 (hball hy).2 (hcomp y (hball hy).1 (hball hy).2))
    (hw.differentiable (by norm_num) x)
  rw [hnormal, map_neg] at hh
  have hwderiv : fderiv ℝ w x e = -(2 * fderiv ℝ u x e) := by
    rw [show fderiv ℝ w x = fderiv ℝ (u ∘ reflectHyperplane e a) x - fderiv ℝ u x from
      fderiv_sub ((hu.comp (contDiff_reflectHyperplane e a 2)).differentiable
        (by norm_num) x) (hu.differentiable (by norm_num) x)]
    simp only [sub_apply, fderiv_comp_reflectHyperplane_normal
      e a x (hu.differentiable (by norm_num) _), hxR]
    ring
  rw [hwderiv] at hh
  linarith

end Elliptic.Semilinear.MovingPlanes
