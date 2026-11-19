/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FixedPoint.Brouwer.ClosedBall

/-!
# Finite-dimensional compact convex fixed points

Nearest-point retraction and rescaling reduce a Euclidean compact convex set to the unit
ball, even when its interior is empty. A continuous linear equivalence then transfers the
result to any finite-dimensional real normed space, whose norm need not come from an
inner product.

Evans uses this form in step 2 of his proof of Schauder's theorem (§9.2.2, Theorem 3), for the
convex hull of finitely many points, which he identifies with a closed ball by a homeomorphism.
The nearest-point retraction `exists_lipschitzWith_retraction_of_isComplete_convex` lets us
avoid that homeomorphism.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.2, step 2 of the proof of Theorem 3, p. 539.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Metric Function

namespace PDE.FixedPoint

open Analysis

/-- The Euclidean compact convex version of Brouwer, including sets with empty interior. -/
theorem exists_isFixedPt_of_isCompact_convex_euclidean {n : ℕ} {K : Set (ℝ^n)}
    (hne : K.Nonempty) (hcompact : IsCompact K) (hconv : Convex ℝ K) (f : C(K, K)) :
    ∃ x, IsFixedPt f x := by
  obtain ⟨p, hp, hpK, hpid⟩ :=
    exists_lipschitzWith_retraction_of_isComplete_convex hne hcompact.isComplete hconv
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let q : C(closedBall (0 : ℝ^n) 1, K) :=
    ⟨fun x ↦ ⟨p (R • (x : ℝ^n)), hpK _⟩,
      (hp.continuous.comp
        ((continuous_const (y := R)).smul continuous_subtype_val)).subtype_mk _⟩
  have hball (x : closedBall (0 : ℝ^n) 1) :
      R⁻¹ • (f (q x) : ℝ^n) ∈ closedBall (0 : ℝ^n) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹ * ‖(f (q x) : ℝ^n)‖ ≤ R⁻¹ * R :=
        mul_le_mul_of_nonneg_left (hbound _ (f (q x)).property) (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  let T : C(closedBall (0 : ℝ^n) 1, closedBall (0 : ℝ^n) 1) :=
    ⟨fun x ↦ ⟨R⁻¹ • (f (q x) : ℝ^n), hball x⟩,
      ((continuous_const (y := R⁻¹)).smul
        (f.continuous.subtype_val.comp q.continuous)).subtype_mk _⟩
  obtain ⟨x, hx⟩ := exists_isFixedPt_unitClosedBall n T
  have hscale := congrArg (fun y : closedBall (0 : ℝ^n) 1 ↦ R • (y : ℝ^n)) hx
  change R • (R⁻¹ • (f (q x) : ℝ^n)) = R • (x : ℝ^n) at hscale
  rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at hscale
  have hmem : R • (x : ℝ^n) ∈ K := hscale ▸ (f (q x)).property
  refine ⟨q x, Subtype.ext ?_⟩
  change (f (q x) : ℝ^n) = p (R • (x : ℝ^n))
  rw [hpid hmem]
  exact hscale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Brouwer's theorem for any nonempty compact convex set in a finite-dimensional real
normed space, with its original norm and topology. -/
theorem exists_isFixedPt_of_isCompact_convex_finiteDimensional {K : Set E}
    (hne : K.Nonempty) (hcompact : IsCompact K) (hconv : Convex ℝ K) (f : C(K, K)) :
    ∃ x, IsFixedPt f x := by
  let e : E ≃L[ℝ] ℝ^(Module.finrank ℝ E) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let eK := e.toHomeomorph.image K
  let g : C(e '' K, e '' K) :=
    ⟨fun y ↦ eK (f (eK.symm y)),
      eK.continuous.comp (f.continuous.comp eK.symm.continuous)⟩
  obtain ⟨y, hy⟩ := exists_isFixedPt_of_isCompact_convex_euclidean
    (hne.image e) (hcompact.image e.continuous) (hconv.linear_image e.toLinearMap) g
  refine ⟨eK.symm y, ?_⟩
  have := congrArg eK.symm hy
  change eK.symm (eK (f (eK.symm y))) = eK.symm y at this
  exact (eK.symm_apply_apply _).symm.trans this

/-- Every continuous self-map of a closed ball of nonnegative radius has a fixed point.
The zero-radius and zero-dimensional cases are included. -/
theorem exists_isFixedPt_closedBall (c : E) {r : ℝ} (hr : 0 ≤ r)
    (f : C(closedBall c r, closedBall c r)) : ∃ x, IsFixedPt f x :=
  exists_isFixedPt_of_isCompact_convex_finiteDimensional (nonempty_closedBall.mpr hr)
    (isCompact_closedBall c r) (convex_closedBall c r) f

end PDE.FixedPoint
