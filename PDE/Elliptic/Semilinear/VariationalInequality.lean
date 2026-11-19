/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Variational
import PDE.Analysis.Operator.Coercivity
import PDE.Analysis.WeakCompactness
import PDE.CalculusOfVariations.DirectMethod
import PDE.CalculusOfVariations.WeakLowerSemicontinuity

/-!
# Semilinear variational inequalities

Minimizing a symmetric elliptic energy over a closed convex admissible set gives
a variational inequality. If

`J(u) = (1 / 2) B(u,u) + Phi(u) - ell(u)`,

the inequality is `ell(v-u) ≤ B(u,v-u) + DPhi(u)(v-u)` for every admissible `v`.
It replaces the unconstrained Euler–Lagrange equation at an active constraint.

The direct method constructs the minimizer; ellipticity gives uniqueness.
For a differentiable convex potential, its supporting hyperplane supplies the
lower bound needed for coercivity. The conclusion therefore does not require a
Lipschitz bound or a smallness condition on the nonlinear derivative.

This is the Hilbert-space variational-inequality step in the treatment of convex
constraints in Evans, *Partial Differential Equations*, second edition, §8.4.
An obstacle problem additionally requires proving that its pointwise admissible
class is nonempty, closed, and convex in the chosen Sobolev space.
-/

@[expose] public section

open Filter Set PDE.CalculusOfVariations

namespace PDE.Elliptic.Semilinear

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A symmetric coercive quadratic form and a convex potential with an affine
lower bound have a unique energy minimizer on every nonempty closed convex set. -/
theorem existsUnique_variationalEnergy_minimizerOn
    [CompleteSpace V]
    (B : V →L[ℝ] StrongDual ℝ V)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ) (hPhiConvex : ConvexOn ℝ univ Phi)
    (hPhiLsc : LowerSemicontinuous Phi)
    (a b : ℝ) (ha : 0 ≤ a)
    (hPhiLower : ∀ u, -(a * ‖u‖ + b) ≤ Phi u)
    (ell : StrongDual ℝ V) {K : Set V}
    (hKconvex : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty) :
    ∃! u, u ∈ K ∧ IsMinOn (variationalEnergy B Phi ell) K u := by
  have hstrict :=
    (strongConvexOn_variationalEnergy B hBsymm c hBcoercive Phi hPhiConvex ell).strictConvexOn hc
  apply existsUnique_isMinOn_of_strictConvex_lowerSemicontinuousOn_of_coercive
      PDE.Analysis.inclusionInDoubleDual_surjective (variationalEnergy B Phi ell)
      (hstrict.subset (subset_univ K) hKconvex)
      hKclosed hKne
      ((lowerSemicontinuous_variationalEnergy B Phi hPhiLsc ell).lowerSemicontinuousOn K)
  exact (tendsto_variationalEnergy_atTop B c hc hBcoercive Phi a b ha hPhiLower ell).mono_left
    inf_le_left

/-- The first-order condition for a convex semilinear energy on a convex set.
At a constrained minimizer, feasible first variations are nonnegative. -/
theorem isMinOn_variationalEnergy_iff
    (B : V →L[ℝ] StrongDual ℝ V)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : V → ℝ) (hPhiConvex : ConvexOn ℝ univ Phi)
    (ell : StrongDual ℝ V) {K : Set V} (hKconvex : Convex ℝ K)
    {u : V} (hu : u ∈ K) {DPhi : StrongDual ℝ V}
    (hPhiDiff : HasFDerivAt Phi DPhi u) :
    IsMinOn (variationalEnergy B Phi ell) K u ↔
      ∀ v ∈ K, ell (v - u) ≤ B u (v - u) + DPhi (v - u) := by
  have hconvex :=
    (convexOn_variationalEnergy B hBsymm hBnonneg Phi hPhiConvex ell).subset
      (subset_univ K) hKconvex
  simpa only [sub_apply, add_apply, sub_nonneg] using
    PDE.CalculusOfVariations.isMinOn_iff_forall_fderiv_sub_nonneg hconvex hu
      (hasFDerivAt_variationalEnergy B hBsymm Phi ell hPhiDiff)

/-- A semilinear variational inequality with symmetric coercive principal form
and a differentiable convex potential has exactly one solution on a nonempty
closed convex set in a real Hilbert space. -/
theorem existsUnique_semilinear_variationalInequality
    [CompleteSpace V]
    (B : V →L[ℝ] StrongDual ℝ V)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ) (hPhiConvex : ConvexOn ℝ univ Phi)
    (DPhi : V → StrongDual ℝ V) (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (ell : StrongDual ℝ V) {K : Set V}
    (hKconvex : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, ell (v - u) ≤ B u (v - u) + DPhi u (v - u) := by
  have hPhiLsc : LowerSemicontinuous Phi :=
    (continuous_iff_continuousAt.mpr fun u ↦ (hPhiDiff u).continuousAt).lowerSemicontinuous
  have hPhiLower : ∀ u, -(‖DPhi 0‖ * ‖u‖ + -Phi 0) ≤ Phi u := by
    intro u
    have h := PDE.Analysis.sub_norm_mul_norm_sub_le_of_convex_of_hasFDerivAt
      hPhiConvex (hPhiDiff 0) u
    simp only [sub_zero] at h
    simpa only [neg_add_rev, neg_neg, sub_eq_add_neg] using h
  have hBnonneg : ∀ u, 0 ≤ B u u :=
    IsCoercive.self_nonneg_of_bound hc hBcoercive
  obtain ⟨u, ⟨huK, hu⟩, huniq⟩ := existsUnique_variationalEnergy_minimizerOn
    B hBsymm c hc hBcoercive Phi hPhiConvex hPhiLsc
    ‖DPhi 0‖ (-Phi 0) (norm_nonneg _) hPhiLower ell hKconvex hKclosed hKne
  have hiff (v : V) (hv : v ∈ K) :=
    isMinOn_variationalEnergy_iff B hBsymm hBnonneg Phi hPhiConvex ell
      hKconvex hv (hPhiDiff v)
  refine ⟨u, ⟨huK, (hiff u huK).mp hu⟩, fun v ⟨hvK, hv⟩ ↦ ?_⟩
  exact huniq v ⟨hvK, (hiff v hvK).mpr hv⟩

end PDE.Elliptic.Semilinear
