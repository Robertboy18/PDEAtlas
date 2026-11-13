/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import PDE.Analysis.Matrix.Determinant.Derivative

/-!
# Piola's identity

The rows of the cofactor matrix of a Jacobian have zero divergence. This is Piola's identity,
the lemma on divergence-free rows in Evans, §8.1.4(b), which he states for smooth maps
`ℝ^n → ℝ^n`; we need only a `C²` germ at the point. The same identity holds for any square
selection of columns of a rectangular Jacobian, even when the selected directions repeat. This
form is useful for minors.

## Main results

* `sum_partialDeriv_adjugate_jacobianMatrix_submatrix_eq_zero`: the identity for a square
  selection of columns of a rectangular Jacobian.
* `sum_partialDeriv_adjugate_jacobianMatrix_eq_zero`,
  `divergence_cofactor_jacobianMatrix_eq_zero`: Piola's identity at a point where the map is
  `C²`, as a sum of partial derivatives and as a divergence. The `_on` versions hold on an
  open domain.

## How it works

Evans differentiates the identity `(det P) I = Pᵀ cof P` along `P = Du`, which gives his (24)
and the conclusion where `det Du ≠ 0`; at a singular point he applies this to `u + εx` and lets
`ε → 0`. We differentiate the determinant in its columns instead: one column is fixed by the
cofactor, and differentiating each other column inserts a second derivative. Interchanging
those two column indices negates the determinant, while commutation of mixed partials leaves
the second derivative unchanged, so the terms cancel in pairs. This works at singular
Jacobians directly.

## Implementation notes

The cofactor matrix is `adjugate.transpose`, and its rows index components of the original
map: row `k` is `fun i ↦ adjugate (jacobianMatrix u x) i k`, which is Evans's `(cof Du)^k_i`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), the cofactor notation, the lemma on
  divergence-free rows, (20), and its proof, (21)-(24), pp. 462-463.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open PDE.Analysis.Matrix (detContinuousAlternating)

variable {n : ℕ}

private theorem alternating_update_swap
    (c : Fin n → Fin n → ℝ) (e w : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    detContinuousAlternating (Function.update (Function.update c j e) i w) =
      -detContinuousAlternating (Function.update (Function.update c i e) j w) := by
  have hs :
      Function.update (Function.update c j e) i w =
        Function.update (Function.update c i e) j w ∘ Equiv.swap i j := by
    funext a
    by_cases hai : a = i
    · subst a
      simp
    by_cases haj : a = j
    · subst a
      simp [hij, hij.symm]
    simp [Equiv.swap_apply_of_ne_of_ne hai haj, hai, haj]
  rw [hs]
  exact detContinuousAlternating.toAlternatingMap.map_swap _ hij

/-- A cofactor of a selected Jacobian minor has one fewer derivative than the map.
This statement also covers repeated columns and singular matrices. -/
theorem contDiffAt_adjugate_jacobianMatrix_submatrix
    {m : ℕ} {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (r : ℕ) (hu : ContDiffAt ℝ (r + 1) u x)
    (σ : Fin m → Fin n) (k i : Fin m) :
    ContDiffAt ℝ r (fun y ↦ ((jacobianMatrix u y).submatrix id σ).adjugate i k) x := by
  have heq :
      (fun y ↦ ((jacobianMatrix u y).submatrix id σ).adjugate i k) =
        fun y ↦ detContinuousAlternating
          (Function.update (fun a ↦ jacobianColumn u (σ a) y) i (Pi.single k 1)) := by
    funext y
    exact Matrix.adjugate_eq_det_update_column _ k i
  rw [heq]
  apply
    (detContinuousAlternating (ι := Fin m)).toContinuousMultilinearMap.contDiff.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using
      (contDiffAt_const (𝕜 := ℝ) (c := (Pi.single k 1 : Fin m → ℝ)) (x := x))
  · simpa only [Function.update_of_ne hji] using contDiffAt_jacobianColumn r hu (σ j)

private theorem partialDeriv_adjugate_jacobianMatrix_submatrix
    {m : ℕ} {u : ℝ^n → ℝ^m} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x)
    (σ : Fin m → Fin n) (k i : Fin m) :
    (∂[(σ i)] (fun y ↦ ((jacobianMatrix u y).submatrix id σ).adjugate i k)) x =
      ∑ j, if j = i then 0 else
        detContinuousAlternating
          (Function.update (Function.update (fun a ↦ jacobianColumn u (σ a) x)
            i (Pi.single k 1)) j (fderiv ℝ (jacobianColumn u (σ j)) x
              (EuclideanSpace.single (σ i) (1 : ℝ)))) := by
  let g : Fin m → ℝ^n → Fin m → ℝ :=
    fun j y ↦ Function.update (fun a ↦ jacobianColumn u (σ a) y) i (Pi.single k 1) j
  have hg (j : Fin m) : DifferentiableAt ℝ (g j) x := by
    by_cases hji : j = i
    · subst j
      simpa only [g, Function.update_self] using
        (differentiableAt_const (𝕜 := ℝ) (c := (Pi.single k 1 : Fin m → ℝ)) (x := x))
    · simpa only [g, Function.update_of_ne hji] using
        differentiableAt_jacobianColumn hu (σ j)
  have hcofactor :
      (fun y ↦ ((jacobianMatrix u y).submatrix id σ).adjugate i k) =
        fun y ↦ detContinuousAlternating (g · y) := by
    funext y
    exact Matrix.adjugate_eq_det_update_column _ k i
  rw [partialDeriv, hcofactor,
    fderiv_continuousAlternatingMap_apply_apply (differentiableAt_const _) hg]
  simp only [fderiv_const_apply, zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
    zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [g]
  · simp only [hji, ↓reduceIte]
    have hj : g j = jacobianColumn u (σ j) := by
      funext y
      exact Function.update_of_ne hji _ _
    rw [hj]

/-- Piola cancellation for a square minor of a rectangular Jacobian.
The derivative directions are the selected columns. Neither injectivity of the
selection nor invertibility of the minor is needed. -/
theorem sum_partialDeriv_adjugate_jacobianMatrix_submatrix_eq_zero
    {m : ℕ} {u : ℝ^n → ℝ^m} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x)
    (σ : Fin m → Fin n) (k : Fin m) :
    ∑ i, (∂[(σ i)] (fun y ↦ ((jacobianMatrix u y).submatrix id σ).adjugate i k)) x = 0 := by
  let t (i j : Fin m) : ℝ := if j = i then 0 else
    detContinuousAlternating
      (Function.update (Function.update (fun a ↦ jacobianColumn u (σ a) x)
        i (Pi.single k 1)) j (fderiv ℝ (jacobianColumn u (σ j)) x
          (EuclideanSpace.single (σ i) (1 : ℝ))))
  have hskew (i j : Fin m) : t j i = -t i j := by
    by_cases hij : i = j
    · subst j
      simp [t]
    · simp only [t, hij, Ne.symm hij, ↓reduceIte]
      rw [fderiv_jacobianColumn_comm hu (σ j) (σ i)]
      exact alternating_update_swap _ _ _ hij
  have hsum : (∑ i, ∑ j, t i j) = -(∑ i, ∑ j, t i j) := by
    calc
      (∑ i, ∑ j, t i j) = ∑ j, ∑ i, t i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -t j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hskew j i
      _ = -(∑ j, ∑ i, t j i) := by simp only [Finset.sum_neg_distrib]
  simp_rw [partialDeriv_adjugate_jacobianMatrix_submatrix hu]
  change (∑ i, ∑ j, t i j) = 0
  linarith

/-- Piola's identity for a Jacobian at a `C²` germ. The cofactor's row `k` is
`fun i ↦ adjugate (jacobianMatrix u x) i k`, including at singular Jacobians. -/
theorem sum_partialDeriv_adjugate_jacobianMatrix_eq_zero
    {u : ℝ^n → ℝ^n} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x) (k : Fin n) :
    ∑ i, (∂[i] (fun y ↦ (jacobianMatrix u y).adjugate i k)) x = 0 := by
  simpa only [Matrix.submatrix_id_id, id_eq] using
    sum_partialDeriv_adjugate_jacobianMatrix_submatrix_eq_zero hu id k

/-- On an open domain, `C²` regularity on the domain suffices for Piola's identity at
each of its points. No regularity across the boundary is required. -/
theorem sum_partialDeriv_adjugate_jacobianMatrix_eq_zero_on
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {u : ℝ^n → ℝ^n}
    (hu : ContDiffOn ℝ 2 u Ω) {x : ℝ^n} (hx : x ∈ Ω) (k : Fin n) :
    ∑ i, (∂[i] (fun y ↦ (jacobianMatrix u y).adjugate i k)) x = 0 :=
  sum_partialDeriv_adjugate_jacobianMatrix_eq_zero (hu.contDiffAt (hΩ.mem_nhds hx)) k

/-- The cofactor row field has zero Euclidean divergence `∇·`. -/
theorem divergence_cofactor_jacobianMatrix_eq_zero
    {u : ℝ^n → ℝ^n} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x) (k : Fin n) :
    ∇· (fun y ↦ WithLp.toLp 2 (fun i ↦ (jacobianMatrix u y).adjugate i k)) x = 0 :=
  sum_partialDeriv_adjugate_jacobianMatrix_eq_zero hu k

/-- The divergence form of Piola's identity on any open domain. This includes every
natural dimension; in dimension zero there are no cofactor rows to quantify over. -/
theorem divergence_cofactor_jacobianMatrix_eq_zero_on
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {u : ℝ^n → ℝ^n}
    (hu : ContDiffOn ℝ 2 u Ω) {x : ℝ^n} (hx : x ∈ Ω) (k : Fin n) :
    ∇· (fun y ↦ WithLp.toLp 2 (fun i ↦ (jacobianMatrix u y).adjugate i k)) x = 0 :=
  divergence_cofactor_jacobianMatrix_eq_zero (hu.contDiffAt (hΩ.mem_nhds hx)) k

end PDE.Analysis
