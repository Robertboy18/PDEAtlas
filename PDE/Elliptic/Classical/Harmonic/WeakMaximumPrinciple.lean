/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
import PDE.Analysis.Calculus.LocalExtrema
import PDE.FDeriv.Calculus

/-!
# Local and boundary maximum principles for the Laplacian

At a `C²` local maximum the coordinate second partials and the Laplacian are nonpositive.
Consequences are comparison and uniqueness on closed Euclidean balls for subharmonic and
harmonic functions.

These are the ball-domain forms of Evans's Theorem 4 (i) and Theorem 5 in §2.2.3. Evans proves
them with the mean-value property; we use the perturbation argument he suggests in Problem 4 of
§2.5, which needs no mean values. The variable-coefficient maximum principles are in
`PDE.Elliptic.Classical.MaximumPrinciple`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 4 (Strong maximum principle) (i), p. 27, and
  Theorem 5 (Uniqueness), p. 28; §2.5, Problems 4 and 5, p. 85; §6.4.1, Theorem 1 (Weak maximum
  principle) and the strict case (5)-(8) of its proof, pp. 344-345.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian coordinateLine)

namespace LaplacianEquation


/-- Every pure coordinate second derivative of a `C²` function is nonpositive at a local
maximum.

The proof restricts the function to the affine coordinate line through the point and applies the
one-dimensional curvature lemma.  The repeated-partial/coordinate-line theorem identifies the
resulting ordinary second derivative with the Euclidean coordinate second partial. -/
theorem secondPartial_nonpos_at_localMax {n : ℕ}
    {u : ℝ^n → ℝ} {x : ℝ^n}
    (hmax : IsLocalMax u x) (hu : ContDiffAt ℝ 2 u x) (i : Fin n) :
    (∂[i] (fun y ↦ (∂[i] u) y)) x ≤ 0 := by
  have hlineMax : IsLocalMax (u ∘ coordinateLine i x) (x i) := by
    rw [← PDE.coordinateLine_self i x] at hmax
    exact hmax.comp_continuous (PDE.hasDerivAt_coordinateLine i x (x i)).continuousAt
  have hlineReg : ContDiffAt ℝ 2 (u ∘ coordinateLine i x) (x i) := by
    have hu' : ContDiffAt ℝ 2 u (coordinateLine i x (x i)) := by
      simpa using hu
    exact hu'.comp (x i)
      ((PDE.contDiff_coordinateLine i x).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hline := IsLocalMax.deriv_deriv_nonpos hlineMax hlineReg.continuousAt
  have hline' : iteratedDeriv 2 (u ∘ coordinateLine i x) (x i) ≤ 0 := by
    simpa [iteratedDeriv_eq_iterate, Function.iterate_succ_apply] using hline
  have hidentify := PDE.iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at i 2 hu
  simpa [partialDeriv, Function.iterate_succ_apply] using hidentify.trans_le hline'

/-- At a local maximum of a `C²` function, its Euclidean Laplacian is nonpositive.

This is the pointwise differential form of the maximum principle: the Hessian is nonpositive on
every coordinate direction, hence its trace is nonpositive. -/
theorem laplacian_nonpos_at_localMax {n : ℕ}
    {u : ℝ^n → ℝ} {x : ℝ^n}
    (hmax : IsLocalMax u x) (hu : ContDiffAt ℝ 2 u x) :
    laplacian u x ≤ 0 := by
  classical
  unfold laplacian
  exact Finset.sum_nonpos fun i _ ↦ secondPartial_nonpos_at_localMax hmax hu i

/-- Strict subharmonic functions attain no value above their boundary upper bound on a closed
Euclidean ball.

This is the strict case of Evans's proof of the weak maximum principle (§6.4.1, Theorem 1), on a
closed ball. Continuity gives a maximizer on the closed ball. If its value exceeded the boundary
bound, the maximizer would lie in the open ball and hence be a local maximum. The local
differential maximum principle would then give `Δu ≤ 0`, contradicting strict subharmonicity. -/
theorem strictSubharmonic_le_of_boundary_le {n : ℕ}
    {u : ℝ^n → ℝ} {c : ℝ^n}
    {r M : ℝ} (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hu_reg : ∀ x ∈ Metric.ball c r, ContDiffAt ℝ 2 u x)
    (hu_strict : ∀ x ∈ Metric.ball c r, 0 < laplacian u x)
    (hu_boundary : ∀ x ∈ Metric.sphere c r, u x ≤ M) :
    ∀ x ∈ Metric.closedBall c r, u x ≤ M := by
  intro x hx
  by_contra hnot
  obtain ⟨z, hzclosed, hzmax⟩ :=
    (isCompact_closedBall c r).exists_isMaxOn ⟨c, Metric.mem_closedBall_self hr.le⟩ hu_cont
  have hzball : z ∈ Metric.ball c r :=
    lt_of_le_of_ne (Metric.mem_closedBall.1 hzclosed) fun hdist ↦
      hnot ((show u x ≤ u z from hzmax hx).trans (hu_boundary z (Metric.mem_sphere.2 hdist)))
  exact (laplacian_nonpos_at_localMax (hzmax.isLocalMaxOn.isLocalMax
    (Metric.closedBall_mem_nhds_of_mem hzball)) (hu_reg z hzball)).not_gt (hu_strict z hzball)

/-- Weak maximum principle on a closed Euclidean ball for functions that are subharmonic in the PDE
sense.

The proof is the perturbation argument of Evans's §2.5, Problem 4, with one squared coordinate in
place of `|x|²`. If an interior value exceeded the boundary bound, add a sufficiently small
positive multiple of that squared coordinate. Its Laplacian is
the positive constant `2ε`, while its boundary growth is at most `εr²`; the strict maximum
principle then gives a contradiction. -/
theorem subharmonic_le_of_boundary_le {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {c : ℝ^n}
    {r M : ℝ} (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hu_reg : ∀ x ∈ Metric.ball c r, ContDiffAt ℝ 2 u x)
    (hu_sub : ∀ x ∈ Metric.ball c r, 0 ≤ laplacian u x)
    (hu_boundary : ∀ x ∈ Metric.sphere c r, u x ≤ M) :
    ∀ x ∈ Metric.closedBall c r, u x ≤ M := by
  let k : Fin n := ⟨0, Fact.out⟩
  intro x hx
  by_contra hnot
  let ε : ℝ := (u x - M) / (2 * r ^ 2)
  have hε : 0 < ε := div_pos (by linarith [not_le.1 hnot]) (by positivity)
  let q : ℝ^n → ℝ := fun y ↦ (y k - c k) ^ 2
  have hq : ContDiff ℝ 2 q := by
    simpa only [EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).contDiff.sub contDiff_const).pow 2
  have hpert (y : ℝ^n) : ContDiffAt ℝ 2 (fun z ↦ ε * q z) y := (contDiff_const.mul hq).contDiffAt
  have hcoord (y : ℝ^n) (hy : y ∈ Metric.sphere c r) : q y ≤ r ^ 2 := by
    have h : |y k - c k| ≤ r := by
      simpa [← dist_eq_norm, Metric.mem_sphere.1 hy, Real.dist_eq] using
        PiLp.norm_apply_le (y - c) k
    exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  have hbound : u x + ε * q x ≤ M + ε * r ^ 2 :=
    strictSubharmonic_le_of_boundary_le (u := fun y ↦ u y + ε * q y) hr
      (hu_cont.add (contDiff_const.mul hq).continuous.continuousOn)
      (fun y hy ↦ (hu_reg y hy).add (hpert y))
      (fun y hy ↦ by
        rw [PDE.laplacian_add u (fun z ↦ ε * q z) y (hu_reg y hy) (hpert y),
          PDE.laplacian_const_smul ε q y,
          show laplacian q y = 2 from PDE.laplacian_coordinate_sq_sub k (c k) y]
        linarith [hu_sub y hy])
      (fun y hy ↦ add_le_add (hu_boundary y hy) (mul_le_mul_of_nonneg_left (hcoord y hy) hε.le))
      x hx
  have hqx : 0 ≤ q x := sq_nonneg _
  have heps : ε * r ^ 2 = (u x - M) / 2 := by
    dsimp only [ε]
    field_simp
  linarith [mul_nonneg hε.le hqx, not_le.1 hnot]

/-- Weak maximum principle for a PDE-harmonic function on an open Euclidean ball, continuous up to
its boundary. -/
theorem IsHarmonicPDE.le_of_boundary_le {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {c : ℝ^n}
    {r M : ℝ} (hu : IsHarmonicPDE n u (Metric.ball c r)) (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hu_boundary : ∀ x ∈ Metric.sphere c r, u x ≤ M) :
    ∀ x ∈ Metric.closedBall c r, u x ≤ M := by
  apply subharmonic_le_of_boundary_le hr hu_cont
  · intro x hx
    exact hu.contDiffAt_of_isOpen Metric.isOpen_ball hx
  · intro x hx
    rw [hu.laplacian_eq_zero hx]
  · exact hu_boundary

/-- Weak minimum principle for a PDE-harmonic function on a Euclidean ball, continuous up to its
boundary. -/
theorem IsHarmonicPDE.ge_of_boundary_ge {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {c : ℝ^n}
    {r m : ℝ} (hu : IsHarmonicPDE n u (Metric.ball c r)) (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hu_boundary : ∀ x ∈ Metric.sphere c r, m ≤ u x) :
    ∀ x ∈ Metric.closedBall c r, m ≤ u x := by
  intro x hx
  have hneg := hu.neg.le_of_boundary_le (M := -m) hr hu_cont.neg fun y hy ↦ by
    exact neg_le_neg (hu_boundary y hy)
  have := hneg x hx
  simpa using neg_le_neg this

/-- Comparison principle on a Euclidean ball: ordered boundary data order two harmonic functions
throughout the closed ball. -/
theorem IsHarmonicPDE.le_of_boundary_le_function {n : ℕ} [Fact (0 < n)]
    {u v : ℝ^n → ℝ} {c : ℝ^n}
    {r : ℝ} (hu : IsHarmonicPDE n u (Metric.ball c r))
    (hv : IsHarmonicPDE n v (Metric.ball c r)) (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hv_cont : ContinuousOn v (Metric.closedBall c r))
    (hboundary : ∀ x ∈ Metric.sphere c r, u x ≤ v x) :
    ∀ x ∈ Metric.closedBall c r, u x ≤ v x := by
  have hsub : IsHarmonicPDE n (u - v) (Metric.ball c r) :=
    hu.sub hv Metric.isOpen_ball
  have hbound := hsub.le_of_boundary_le (M := 0) hr (hu_cont.sub hv_cont) fun y hy ↦ by
    change u y - v y ≤ 0
    exact sub_nonpos.mpr (hboundary y hy)
  intro x hx
  have := hbound x hx
  change u x - v x ≤ 0 at this
  exact sub_nonpos.mp this

/-- Uniqueness for the Dirichlet problem on a Euclidean ball: two harmonic functions continuous on
the closed ball and agreeing on its boundary sphere agree throughout the closed ball. -/
theorem IsHarmonicPDE.eq_of_boundary_eq {n : ℕ} [Fact (0 < n)]
    {u v : ℝ^n → ℝ} {c : ℝ^n}
    {r : ℝ} (hu : IsHarmonicPDE n u (Metric.ball c r))
    (hv : IsHarmonicPDE n v (Metric.ball c r)) (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hv_cont : ContinuousOn v (Metric.closedBall c r))
    (hboundary : ∀ x ∈ Metric.sphere c r, u x = v x) :
    Set.EqOn u v (Metric.closedBall c r) := by
  intro x hx
  apply le_antisymm
  · exact hu.le_of_boundary_le_function hv hr hu_cont hv_cont
      (fun y hy ↦ (hboundary y hy).le) x hx
  · exact hv.le_of_boundary_le_function hu hr hv_cont hu_cont
      (fun y hy ↦ (hboundary y hy).ge) x hx

end LaplacianEquation
