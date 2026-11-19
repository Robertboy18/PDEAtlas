/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram

/-!
# Lax–Milgram on a closed subspace

Let `V` be a closed subspace of a real Hilbert space `E` and `B` a bounded bilinear form on `V`
with `κ ‖u‖² ≤ B u u`. For every continuous linear functional `f` on `E` there is `u ∈ V` with
`B u w = f w` for all `w ∈ V` and `‖u‖ ≤ κ⁻¹ ‖f‖`. Exhaustion arguments solve on an increasing
family of subspaces with one ambient load and pass to a weak limit; the bound is uniform in the
subspace.

With `V = E` this is the Lax–Milgram theorem, Evans, §6.2.1, Theorem 1. We apply `solve` from
`PDE.Analysis.Variational.LaxMilgram` to `B` and the restriction of `f` to `V`.

## Main results

* `exists_forall_eq_of_coercive_subspace`: the solution `u ∈ V` with `‖u‖ ≤ κ⁻¹ ‖f‖`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), p. 315.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

/-- Lax–Milgram on a closed subspace with the load restricted from the ambient space. -/
theorem exists_forall_eq_of_coercive_subspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : Submodule ℝ E) [CompleteSpace V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    {κ : ℝ} (hκ : 0 < κ) (hB : ∀ u, κ * ‖u‖ ^ 2 ≤ B u u) (f : StrongDual ℝ E) :
    ∃ u : V, (∀ w, B u w = f w) ∧ ‖u‖ ≤ κ⁻¹ * ‖f‖ := by
  have hc : ∀ v, κ * ‖v‖ * ‖v‖ ≤ B v v := fun v ↦ by
    rw [mul_assoc, ← sq]
    exact hB v
  have hcoe : IsCoercive B := ⟨κ, hκ, hc⟩
  set g : StrongDual ℝ V := f.comp V.subtypeL
  have hg : ‖g‖ ≤ ‖f‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun w ↦ ?_
    rw [← Submodule.norm_coe w]
    exact f.le_opNorm _
  refine ⟨solve B hcoe g, fun w ↦ solve.isWeakSolution B hcoe g w, ?_⟩
  calc ‖solve B hcoe g‖ ≤ ‖g‖ / κ := solve.norm_le_div B hcoe κ hκ hc g
    _ ≤ κ⁻¹ * ‖f‖ := by
        rw [div_eq_inv_mul]
        gcongr

end PDE.Analysis.Variational
