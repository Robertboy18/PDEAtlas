/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram

/-!
# Lax–Milgram in an affine class

## Motivation

A boundary value problem with inhomogeneous data asks for a state `u` in a space `U` such that
`u - g` lies in the image of a Hilbert space `V`, the states with zero boundary values, and
`B u v = ell v` for every test vector `v ∈ V`. The form `B` takes a state in `U` and a test
vector in `V`. Is there exactly one such `u`?

## The idea

Yes, when the form is coercive on states that come from `V`. Write `u = g + ι w` with
`ι : V → U` the inclusion. The correction `w` solves `B (ι w) v = ell v - B g v`, a
Lax–Milgram problem on `V` whose load is `ell - B g`. Its unique solution gives `u`, and two
solutions in the class differ by a solution of the homogeneous problem on `V`, which is zero.
The space `U` needs no norm or topology: only the functional `B g` on `V` has to be
continuous.

## Main results

* `existsUnique_eq_add_and_forall_eq` (all additive groups `U`, all Hilbert spaces `V`, all
  maps `ι : V → U`, all `B : U → V → ℝ` additive in the state whose composition with `ι` is a
  coercive bounded form and whose value at `g` is continuous, all loads on `V` and all data
  `g ∈ U`): there is exactly one `u = g + ι w` with `B u v = ell v` for all `v`.
* `norm_le_of_forall_add_eq`: the correction satisfies `‖w‖ ≤ ‖ell - B g‖ / c` for a
  coercivity constant `c`.

## Relations

* The proof applies `solve` and `IsWeakSolution.unique` to the form `B₀` and the load
  `ell - B g`. For `U = V`, `ι` the identity and `g = 0` the statement is that of
  `IsWeakSolution.existsUnique`, the Lax–Milgram theorem.
* `SobolevSpace.GraphSpace.existsUnique_interiorVariableCoeffForm_prescribed_boundary` is the
  case `U = H¹(Ω)`, `V = H¹₀(Ω)` of a divergence-form operator.

## What stays open

Forms that are not coercive on `V`, where the Fredholm alternative replaces uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), p. 315, the
  source of `PDE.Analysis.Variational.LaxMilgram`. The translation by `g` is proved here.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

variable {U V : Type*} [AddCommGroup U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Lax–Milgram with inhomogeneous data. Let `ι : V → U` map a Hilbert space into an additive
group, and let `B u v` be additive in the state `u ∈ U`, with `B (ι w) v = B₀ w v` for a
coercive bounded form `B₀` on `V` and `B g v = ℓg v` for a continuous functional `ℓg`. For
every load `ell` on `V` there is exactly one `u` of the form `g + ι w` with `B u v = ell v`
for all `v`.

The correction `w` is the Lax–Milgram solution for the load `ell - ℓg`. The maps `ι` and `B`
are plain functions, so the statement applies to a space `U` whichever way its algebraic
structure is given. -/
theorem existsUnique_eq_add_and_forall_eq
    (ι : V → U) (B : U → V → ℝ) (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (B₀ : V →L[ℝ] V →L[ℝ] ℝ) (hB₀ : IsCoercive B₀) (hι : ∀ w v, B (ι w) v = B₀ w v)
    (ell ℓg : StrongDual ℝ V) (g : U) (hg : ∀ v, B g v = ℓg v) :
    ∃! u : U, (∃ w, u = g + ι w) ∧ ∀ v, B u v = ell v := by
  let w : V := solve B₀ hB₀ (ell - ℓg)
  have hw : IsWeakSolution B₀ (ell - ℓg) w := solve.isWeakSolution B₀ hB₀ (ell - ℓg)
  refine ⟨g + ι w, ⟨⟨w, rfl⟩, fun v ↦ ?_⟩, ?_⟩
  · -- the equation for `g + ι w` is the equation for the correction
    have h : B₀ w v = ell v - ℓg v := hw v
    rw [hadd, hι, hg, h]
    ring
  · -- two solutions in the class have the same correction
    rintro u ⟨⟨w', rfl⟩, hu⟩
    have hsol : IsWeakSolution B₀ (ell - ℓg) w' := by
      intro v
      have h := hu v
      rw [hadd, hι, hg] at h
      change B₀ w' v = ell v - ℓg v
      linarith
    rw [IsWeakSolution.unique B₀ hB₀ (ell - ℓg) hsol hw]

/-- The correction of a solution in an affine class is bounded by the load and the datum: if
`c ‖w‖² ≤ B₀ w w` on `V` and `B (g + ι w) v = ell v` for all `v`, then
`‖w‖ ≤ ‖ell - ℓg‖ / c`. -/
theorem norm_le_of_forall_add_eq
    (ι : V → U) (B : U → V → ℝ) (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (B₀ : V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (hB₀ : ∀ w, c * ‖w‖ * ‖w‖ ≤ B₀ w w)
    (hι : ∀ w v, B (ι w) v = B₀ w v)
    (ell ℓg : StrongDual ℝ V) (g : U) (hg : ∀ v, B g v = ℓg v) (w : V)
    (hu : ∀ v, B (g + ι w) v = ell v) :
    ‖w‖ ≤ ‖ell - ℓg‖ / c := by
  have hcoercive : IsCoercive B₀ := ⟨c, hc, hB₀⟩
  have hsol : IsWeakSolution B₀ (ell - ℓg) w := by
    intro v
    have h := hu v
    rw [hadd, hι, hg] at h
    change B₀ w v = ell v - ℓg v
    linarith
  rw [IsWeakSolution.eq_solve B₀ hcoercive (ell - ℓg) hsol]
  exact solve.norm_le_div B₀ hcoercive c hc hB₀ (ell - ℓg)

end PDE.Analysis.Variational
