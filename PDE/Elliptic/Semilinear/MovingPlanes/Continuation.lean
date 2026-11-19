/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.MovingPlanes.Boundary
public import PDE.Elliptic.Semilinear.MovingPlanes.Comparison
public import PDE.Analysis.Calculus.MovingPlanes.CompactComparison

/-!
# Moving a comparison plane to the center of the ball

Let `u` be `C²` on `ℝ^n`, positive in the unit ball and zero on the sphere, with `-Δu = f(u)` in the
ball for a Lipschitz `f`. For a unit vector `e` and `a ≥ 0`, `u(y) ≤ u(R y)` at every point `y` of
the ball with `⟪y, e⟫ > a`, where `R` is the reflection in the plane `⟪y, e⟫ = a` (`le_reflection`).
For `a > 0` the inequality is strict on the cap and on its spherical boundary (`lt_reflection`).

This is Evans's (15_λ) for `0 < λ < 1` and (17) in the proof of §9.5.2, Theorem 2, with the
direction `e` in place of the last coordinate direction.

## How it works

Evans starts from planes near the pole with his Lemma 2, lets `λ₀` be the infimum of the `λ` such
that (15_μ) holds for all `μ` in `[λ, 1)`, (16), and derives a contradiction from `λ₀ > 0` with
(18)-(20). We argue by connectedness. The set of parameters `a` at which weak comparison holds is
closed (`isClosed_setOf_le_reflection`) and contains `1`, where the cap is empty. At a parameter
`a > 0` in the set, comparison is strict (`lt_reflection_of_le_reflection`), and `u` has negative
derivative in the direction `e` near the flat face, inside the ball by
`fderiv_neg_on_plane_of_le_reflection` and at the sphere by `eventually_fderiv_neg`. A compactness
argument over the closed ball (`eventually_le_reflection`) then gives weak comparison at all nearby
parameters, the weak form of Evans's (20), so the set contains `(0, ∞)` and, being closed, `[0, ∞)`.
No small-volume maximum principle or corner Hopf lemma is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.5.2 (Radial symmetry), Lemma 2 (Boundary estimates),
  p. 557, the moving-plane notation and Theorem 2 (Radial symmetry), p. 558, and its proof,
  (15)-(20), p. 559.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace Elliptic.Semilinear.MovingPlanes

open Set Metric Filter PDE.Analysis
open scoped Topology RealInnerProductSpace NNReal

variable {n : ℕ} [Fact (0 < n)]
variable [SobolevSpace.Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)]

/-- The semilinear equation implies reflection comparison at every plane
between the center and the positive pole, and vacuously at every higher plane. -/
theorem le_reflection {u : ℝ^n → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {e : ℝ^n} (he : ‖e‖ = 1) {a : ℝ} (ha : 0 ≤ a) :
    ∀ x ∈ ball (0 : ℝ^n) 1, a < ⟪x, e⟫ → u x ≤ u (reflectHyperplane e a x) := by
  let S : Set ℝ := {b | ∀ x ∈ ball (0 : ℝ^n) 1,
    b < ⟪x, e⟫ → u x ≤ u (reflectHyperplane e b x)}
  have hclosed : IsClosed S := isClosed_setOf_le_reflection hu.continuous e
  have hopen : IsOpen (S ∩ Ioi 0) := by
    apply isOpen_iff_mem_nhds.mpr
    intro b hb
    have hstrict := lt_reflection_of_le_reflection hu hf hpde hpos hzero he hb.2 hb.1
    have hflat (x : ℝ^n) (hx : x ∈ closedBall (0 : ℝ^n) 1)
        (hplane : ⟪x, e⟫ = b) :
        ∀ᶠ y in 𝓝 x, y ∈ ball (0 : ℝ^n) 1 → fderiv ℝ u y e < 0 := by
      have hxn : ‖x‖ ≤ 1 := by simpa using hx
      rcases lt_or_eq_of_le hxn with hinside | hsphere
      · have hd := fderiv_neg_on_plane_of_le_reflection hu hf hpde hpos hzero he
          hb.2 hb.1 (by simpa using hinside) hplane
        exact (((hu.continuous_fderiv (by norm_num)).clm_apply
          continuous_const).continuousAt.eventually_lt_const hd).mono fun _ h _ ↦ h
      · exact eventually_fderiv_neg hu hf hpde hpos hzero hsphere he
          (by rw [hplane]; exact hb.2)
    exact (eventually_le_reflection (hu.differentiable (by norm_num))
      he hb.2 hstrict hflat).and (isOpen_Ioi.mem_nhds hb.2)
  have hone : (1 : ℝ) ∈ S := by
    intro x hx hcoord
    have hxn : ‖x‖ < 1 := by simpa using hx
    have hi : ⟪x, e⟫ ≤ ‖x‖ := by simpa [he] using real_inner_le_norm x e
    linarith
  have hsubset : Ioi (0 : ℝ) ⊆ S ∩ Ioi 0 :=
    isPreconnected_Ioi.subset_of_closure_inter_subset hopen
      ⟨1, zero_lt_one, hone, zero_lt_one⟩ (fun _ hx ↦
        ⟨closure_minimal inter_subset_left hclosed hx.1, hx.2⟩)
  have hall : Ici (0 : ℝ) ⊆ S := by
    rw [← closure_Ioi]
    exact closure_minimal (fun x hx ↦ (hsubset hx).1) hclosed
  exact hall ha

/-- Every positive displacement gives strict reflection comparison on the upper cap,
including its spherical part. This is Evans's (15_λ) in §9.5.2 for the direction `e`. -/
theorem lt_reflection {u : ℝ^n → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {e : ℝ^n} (he : ‖e‖ = 1) {a : ℝ} (ha : 0 < a) :
    ∀ x ∈ closedBall (0 : ℝ^n) 1,
      a < ⟪x, e⟫ → u x < u (reflectHyperplane e a x) :=
  lt_reflection_of_le_reflection hu hf hpde hpos hzero he ha
    (le_reflection hu hf hpde hpos hzero he ha.le)

end Elliptic.Semilinear.MovingPlanes
