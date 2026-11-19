/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Two nonzero determinant evaluations on a basis

Let `r` be a basis of `ℝ^3`, let `v` have three nonzero coefficients in `r`, and let `W` not
lie on the line through `v`. Then at least two distinct basis vectors `r i`, `r j` give
nonzero determinants `det (v, r i, W)` and `det (v, r j, W)`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace PDE.Analysis

/-- If all three coefficients of `v` in a basis are nonzero and `W ∉ span {v}`,
at least two distinct basis vectors give nonzero determinants with `v, W`.
The displayed matrices have rows `v, r i, W`, in that order. -/
theorem exists_distinct_det_ne_zero_of_basis
    (r : Module.Basis (Fin 3) ℝ (ℝ^3)) (a : Fin 3 → ℝ)
    (ha : ∀ i, a i ≠ 0) {v W : ℝ^3}
    (hv : v = ∑ i, a i • r i)
    (hW : W ∉ Submodule.span ℝ ({v} : Set (ℝ^3))) :
    ∃ i j : Fin 3, i ≠ j ∧
      Matrix.det ![⇑v, ⇑(r i), ⇑W] ≠ 0 ∧
      Matrix.det ![⇑v, ⇑(r j), ⇑W] ≠ 0 := by
  classical
  have hrepr : (r.repr v : Fin 3 → ℝ) = a := by
    rw [hv, r.repr_sum_self]
  have hvne : v ≠ 0 := by
    intro hz
    have h0 := congrFun hrepr 0
    exact ha 0 (by simpa [hz] using h0.symm)
  let e : (ℝ^3) ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hvc : e v ≠ 0 := by
    intro hz
    exact hvne (e.injective (hz.trans e.map_zero.symm))
  have hpair : LinearIndependent ℝ ![e v, e W] := by
    apply (LinearIndependent.pair_iff' hvc).2
    intro c hc
    apply hW
    exact Submodule.mem_span_singleton.mpr
      ⟨c, e.injective ((e.map_smul c v).trans hc)⟩
  have hcross : e W ⨯₃ e v ≠ 0 := by
    rw [← cross_anticomm (e v) (e W)]
    exact neg_ne_zero.mpr (crossProduct_ne_zero_iff_linearIndependent.mpr hpair)
  let ℓ : (ℝ^3) →ₗ[ℝ] ℝ :=
    (dotProductBilin ℝ ℝ (e W ⨯₃ e v)).comp e.toLinearMap
  have hdet (x : ℝ^3) : ℓ x = Matrix.det ![⇑v, ⇑x, ⇑W] := by
    change (e W ⨯₃ e v) ⬝ᵥ e x = Matrix.det ![e v, e x, e W]
    rw [dotProduct_comm (e W ⨯₃ e v) (e x),
      ← triple_product_permutation (e v) (e x) (e W), triple_product_eq_det]
  have hℓv : ℓ v = 0 := by
    change (e W ⨯₃ e v) ⬝ᵥ e v = 0
    rw [dotProduct_comm (e W ⨯₃ e v) (e v), dot_cross_self]
  have hℓ : ℓ ≠ 0 := by
    intro hz
    apply hcross
    apply dotProduct_eq_zero (e W ⨯₃ e v)
    intro w
    have hx := congrArg (fun f : (ℝ^3) →ₗ[ℝ] ℝ ↦ f (e.symm w)) hz
    change (e W ⨯₃ e v) ⬝ᵥ e (e.symm w) = 0 at hx
    simpa only [e.apply_symm_apply] using hx
  obtain ⟨i, hi⟩ : ∃ i, ℓ (r i) ≠ 0 := by
    by_contra hn
    have hall (i : Fin 3) : ℓ (r i) = 0 := by
      by_contra hi
      exact hn ⟨i, hi⟩
    exact hℓ (r.ext hall)
  have hsum : ∑ k, a k * ℓ (r k) = 0 := by
    calc
      ∑ k, a k * ℓ (r k) = ℓ (∑ k, a k • r k) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = ℓ v := congrArg ℓ hv.symm
      _ = 0 := hℓv
  obtain ⟨j, hij, hj⟩ : ∃ j, i ≠ j ∧ ℓ (r j) ≠ 0 := by
    by_contra hn
    have hz (j : Fin 3) (hji : j ≠ i) : ℓ (r j) = 0 := by
      by_contra hj
      exact hn ⟨j, hji.symm, hj⟩
    have hsingle : ∑ k, a k * ℓ (r k) = a i * ℓ (r i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, mul_zero]
      · intro hiun
        exact (hiun (Finset.mem_univ i)).elim
    exact (mul_ne_zero (ha i) hi) (hsingle.symm.trans hsum)
  refine ⟨i, j, hij, ?_, ?_⟩
  · simpa only [hdet] using hi
  · simpa only [hdet] using hj

end PDE.Analysis
