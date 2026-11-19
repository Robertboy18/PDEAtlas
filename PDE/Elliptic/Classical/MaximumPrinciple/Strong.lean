/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.Hopf
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Strong maximum principle with locally bounded coefficients

A classical elliptic subsolution of `Lu = -∑ D²u[σₖ, σₖ] + Du[b] + cu` that attains its maximum `M`
over a connected open domain is constant, provided `c ≥ 0` and `cM ≥ 0`
(`eqOn_const_of_isPreconnected_of_isMaxOn`). This includes nonnegative maxima for nonnegative
potential, Evans's §6.4.2, Theorem 4 (Strong maximum principle with `c ≥ 0`), and maxima of any sign
when the potential vanishes, his Theorem 3 (Strong maximum principle). The matrix-coefficient
formulation is developed in `PDE.Elliptic.Classical.MaximumPrinciple.MatrixStrong`.

Uniform ellipticity, an upper trace bound, and bounds for the drift and potential are required only
on a neighborhood of each point. The domain need not be bounded, and the coefficients need not be
continuous.

## Main results

* `eqOn_const_of_isPreconnected_of_isMaxOn`: the strong maximum principle.
* `exists_tangent_ball_of_isCompact_inter_closedBall`: near a set whose local part is compact there
  is a ball that misses the set and touches it.

## How it works

Evans takes `V = {u < M}`, chooses `y ∈ V` closer to `{u = M}` than to `∂U`, and lets `B` be the
largest ball centered at `y` inside `V`; Hopf's Lemma at a point where `B` touches `{u = M}`
contradicts `Du = 0` there. We argue locally. The maximum set is closed relative to the domain, so
by connectedness it suffices to show that it is open. Near a maximizer we minimize the distance to
the compact intersection of the maximum set with a small closed ball
(`exists_tangent_ball_of_isCompact_inter_closedBall`). This gives a ball whose interior misses the
maximum set, whose boundary touches it, and which stays inside the neighborhood carrying the
coefficient bounds. Hopf's lemma (`hopf_normal_fderiv_pos`) then contradicts the vanishing
derivative at the interior maximizer.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Theorem 3 (Strong maximum principle) and its proof,
  pp. 349-350, and Theorem 4 (Strong maximum principle with `c ≥ 0`), pp. 350-351.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Metric Set
open scoped InnerProductSpace Topology

/-- A point near a set admits a ball disjoint from the set and touching it, provided the
local portion of the set is compact. The closed ball stays inside the prescribed larger
ball, so local analytic hypotheses can be restricted to it. -/
theorem exists_tangent_ball_of_isCompact_inter_closedBall
    {X : Type*} [MetricSpace X] {S : Set X} {p y : X} {r : ℝ}
    (hr : 0 < r) (hp : p ∈ S) (hcompact : IsCompact (S ∩ closedBall p r))
    (hy : y ∈ ball p (r / 2)) (hyS : y ∉ S) :
    ∃ z R, z ∈ S ∧ 0 < R ∧ dist z y = R ∧
      closedBall y R ⊆ ball p r ∧ ∀ x ∈ ball y R, x ∉ S := by
  have hpK : p ∈ S ∩ closedBall p r := ⟨hp, mem_closedBall_self hr.le⟩
  obtain ⟨z, hz, hzmin⟩ := hcompact.exists_isMinOn ⟨p, hpK⟩
    (f := fun x ↦ dist x y) (continuous_id.dist continuous_const).continuousOn
  let R : ℝ := dist z y
  have hR : 0 < R := by
    apply dist_pos.mpr
    intro hzy
    apply hyS
    rw [← hzy]
    exact hz.1
  have hRle : R ≤ dist y p := by
    calc
      R ≤ dist p y := hzmin hpK
      _ = dist y p := dist_comm p y
  have hcontain : closedBall y R ⊆ ball p r := by
    intro x hx
    apply mem_ball.mpr
    have hxy : dist x y ≤ R := mem_closedBall.mp hx
    have hyp : dist y p < r / 2 := mem_ball.mp hy
    have htriangle := dist_triangle x y p
    linarith
  refine ⟨z, R, hz.1, hR, rfl, hcontain, ?_⟩
  intro x hx hxS
  have hxK : x ∈ S ∩ closedBall p r :=
    ⟨hxS, ball_subset_closedBall (hcontain (ball_subset_closedBall hx))⟩
  have hmin : R ≤ dist x y := hzmin hxK
  exact (not_lt_of_ge hmin) (mem_ball.mp hx)

variable {n : ℕ}

/-- A subsolution attaining an interior maximum on a connected open domain is constant.
Ellipticity and coefficient bounds are local. The compatibility condition `cM ≥ 0`
covers a nonnegative maximum for `c ≥ 0`, and a maximum of either sign for `c = 0`. -/
theorem eqOn_const_of_isPreconnected_of_isMaxOn
    {ι : Type*} [Fintype ι] {Ω : Set (ℝ^n)}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (σ : ℝ^n → ι → ℝ^n) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (hlocal : ∀ p ∈ Ω, ∃ r κ A B C : ℝ,
      0 < r ∧ 0 < κ ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ closedBall p r ⊆ Ω ∧
      ∀ x ∈ ball p r,
        (∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤ ∑ k, ⟪v, σ x k⟫_ℝ ^ 2) ∧
        (∑ k, ‖σ x k‖ ^ 2) ≤ A ∧ ‖b x‖ ≤ B ∧ 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, factoredOperator σ b c u x ≤ 0)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Ω) (hmax : IsMaxOn u Ω x₀)
    (hcM : ∀ x ∈ Ω, 0 ≤ c x * u x₀) :
    Set.EqOn u (fun _ ↦ u x₀) Ω := by
  classical
  let M : ℝ := u x₀
  have hucont : ContinuousOn u Ω :=
    fun x hx ↦ (hureg x hx).continuousAt.continuousWithinAt
  let S : Set Ω := {p | u p = M}
  have hSclosed : IsClosed S :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hucont) continuous_const
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpmax : u p = M := hp
    obtain ⟨r, κ, A, B, C, hr, hκ, hA, hB, hC, hclosed, hcoeff⟩ :=
      hlocal p p.property
    have hKcompact : IsCompact ({x | u x = M} ∩ closedBall (p : ℝ^n) r) := by
      rw [inter_comm]
      exact (isCompact_closedBall (p : ℝ^n) r).of_isClosed_subset
        (isClosed_closedBall.isClosed_eq (hucont.mono hclosed) continuousOn_const)
        (fun _ hx ↦ hx.1)
    have hballS : ball p (r / 2) ⊆ S := by
      intro y hy
      change dist (y : ℝ^n) (p : ℝ^n) < r / 2 at hy
      change u y = M
      by_contra hymax
      obtain ⟨z, R, hzmax, hR, hzy, hcontain, hdisjoint⟩ :=
        exists_tangent_ball_of_isCompact_inter_closedBall
          (S := {x : ℝ^n | u x = M}) hr hpmax hKcompact (mem_ball.mpr hy) hymax
      have hballΩ : closedBall (y : ℝ^n) R ⊆ Ω :=
        hcontain.trans (ball_subset_closedBall.trans hclosed)
      have hzΩ : z ∈ Ω := hballΩ (mem_closedBall.mpr hzy.le)
      let v : ℝ^n → ℝ := fun x ↦ u x - M
      have hvz : v z = 0 := sub_eq_zero.mpr hzmax
      have hvcont : ContinuousOn v (closedBall (y : ℝ^n) R) :=
        (hucont.mono hballΩ).sub continuousOn_const
      have hvreg (x : ℝ^n) (hx : x ∈ ball (y : ℝ^n) R) : ContDiffAt ℝ 2 v x :=
        (hureg x (hballΩ (ball_subset_closedBall hx))).sub contDiffAt_const
      have hvsub (x : ℝ^n) (hx : x ∈ ball (y : ℝ^n) R) :
          factoredOperator σ b c v x ≤ 0 := by
        have hxΩ := hballΩ (ball_subset_closedBall hx)
        rw [show v = (fun x ↦ u x - M) from rfl, factoredOperator_sub_const]
        exact sub_nonpos.mpr ((hsub x hxΩ).trans (hcM x hxΩ))
      have hvstrict (x : ℝ^n) (hx : x ∈ ball (y : ℝ^n) R) : v x < v z := by
        rw [hvz]
        exact sub_lt_zero.mpr
          (lt_of_le_of_ne (hmax (hballΩ (ball_subset_closedBall hx))) (hdisjoint x hx))
      have hcoeffball (x : ℝ^n) (hx : ‖x - (y : ℝ^n)‖ < R) :=
        hcoeff x (hcontain (mem_closedBall.mpr
          (by simpa only [dist_eq_norm] using hx.le)))
      have hnormal := hopf_normal_fderiv_pos (u := v) (x₀ := z)
        σ b c (y : ℝ^n) hR hκ hA hB hC
          (fun x _ hx ↦ (hcoeffball x hx).1)
          (fun x _ hx ↦ (hcoeffball x hx).2.1)
          (fun x _ hx ↦ (hcoeffball x hx).2.2.1)
          (fun x _ hx ↦ (hcoeffball x hx).2.2.2)
          (by simpa only [dist_eq_norm] using hzy)
          (by simp only [hvz, le_refl]) hvcont hvreg hvsub hvstrict
          (((hureg z hzΩ).sub contDiffAt_const).differentiableAt (by norm_num))
      have hvmax : IsMaxOn v Ω z := fun x hx ↦ by
        change u x - M ≤ u z - M
        linarith [show u x ≤ M from hmax hx]
      rw [(hvmax.isLocalMax (hΩopen.mem_nhds hzΩ)).fderiv_eq_zero, zero_apply] at hnormal
      exact lt_irrefl _ hnormal
    exact Filter.mem_of_superset (ball_mem_nhds p (by linarith)) hballS
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hΩconn
  have hSuniv : S = univ := (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ ⟨⟨x₀, hx₀⟩, rfl⟩
  exact fun x hx ↦ Set.eq_univ_iff_forall.1 hSuniv ⟨x, hx⟩

end EllipticMaximum
