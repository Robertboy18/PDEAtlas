/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Ordered minors of finite matrices

A rectangular matrix is totally nonnegative when every square minor with rows
and columns taken in increasing order is nonnegative.  We define that notion
for `Matrix (Fin m) (Fin n) R`, encoding an ordered selection of
indices as a strictly monotone map from `Fin size`, which avoids the
enumeration signs that would appear with unordered index sets.  The central
tool is the rectangular Cauchy–Binet formula: the determinant of a product
`A * B` of an `s × m` and an `m × s` matrix is the sum over increasing
`s`-element selections of the products of the corresponding minors.  From it,
total nonnegativity is closed under products, and one positive intermediate
minor makes a minor of the product positive.  The positivity results are stated
over any linearly ordered commutative ring.

## Main definitions and results

* Increasing index selections use Mathlib's `OrderEmbedding`;
  `CAS.Splines.Matrix.injectiveMapEquivOrderedSelectionPerm` decomposes an injective
  tuple into its increasing order embedding and a permutation.
* `CAS.Splines.Matrix.det_mul_rectangular`: the rectangular Cauchy–Binet formula.
* `CAS.Splines.Matrix.IsOrderedMinorNonnegative`: total nonnegativity on ordered minors.
* `CAS.Splines.Matrix.isOrderedMinorNonnegative_one`,
  `CAS.Splines.Matrix.IsOrderedMinorNonnegative.mul`:
  the identity is totally nonnegative and the property is closed under
  rectangular products.
* `CAS.Splines.Matrix.orderedMinor_mul_pos_of_witness`: strict positivity of a minor of a
  product from one strictly positive Cauchy–Binet term.

## References

* S. Karlin, *Total Positivity*, Vol. I, Stanford University Press, 1968.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013.
  <https://doi.org/10.1017/CBO9781139020411>
-/

@[expose] public section

open _root_.Matrix

namespace CAS.Splines.Matrix

open Equiv Equiv.Perm Finset Function

open scoped BigOperators

/-- Sorting an injective finite tuple produces an order embedding. -/
def orderedSelectionOfInjective {size ambient : ℕ}
    (selection : Fin size → Fin ambient) (hinjective : Injective selection) :
    Fin size ↪o Fin ambient :=
  OrderEmbedding.ofStrictMono (selection ∘ Tuple.sort selection)
    ((Tuple.monotone_sort selection).strictMono_of_injective
      (hinjective.comp (Tuple.sort selection).injective))

/-- Every injective finite tuple decomposes uniquely into its increasing
rearrangement followed by a permutation. -/
def injectiveMapEquivOrderedSelectionPerm (size ambient : ℕ) :
    {selection : Fin size → Fin ambient // Injective selection} ≃
      (Fin size ↪o Fin ambient) × Equiv.Perm (Fin size) where
  toFun selection :=
    (orderedSelectionOfInjective selection.1 selection.2,
      (Tuple.sort selection.1)⁻¹)
  invFun selection :=
    ⟨selection.1 ∘ selection.2,
      selection.1.injective.comp selection.2.injective⟩
  left_inv selection := by
    apply Subtype.ext
    funext index
    change
      selection.1
          (Tuple.sort selection.1 ((Tuple.sort selection.1)⁻¹ index)) =
        selection.1 index
    simp
  right_inv selection := by
    rcases selection with ⟨ordered, permutation⟩
    have hsorted :
        (ordered ∘ permutation) ∘ Tuple.sort (ordered ∘ permutation) =
          ordered := by
      calc
        (ordered ∘ permutation) ∘ Tuple.sort (ordered ∘ permutation) =
            ordered ∘ Tuple.sort ordered :=
          Tuple.comp_perm_comp_sort_eq_comp_sort
        _ = ordered := by
          rw [Tuple.sort_eq_refl_iff_monotone.mpr ordered.monotone]
          rfl
    have hsort :
        Tuple.sort (ordered ∘ permutation) = permutation⁻¹ := by
      apply Equiv.ext
      intro index
      apply permutation.injective
      calc
        permutation (Tuple.sort (ordered ∘ permutation) index) = index := by
          apply ordered.injective
          simpa [Function.comp_apply] using congrFun hsorted index
        _ = permutation (permutation⁻¹ index) :=
          (permutation.apply_symm_apply index).symm
    change
      (orderedSelectionOfInjective
          (ordered ∘ permutation)
          (ordered.injective.comp permutation.injective),
        (Tuple.sort (ordered ∘ permutation))⁻¹) =
        (ordered, permutation)
    apply Prod.ext
    · exact DFunLike.ext _ _ (congrFun hsorted)
    · simp [hsort]

private theorem determinantExpansion_eq_zero_of_not_injective
    {R : Type*} [CommRing R] {size middle : ℕ}
    (left : Matrix (Fin size) (Fin middle) R)
    (right : Matrix (Fin middle) (Fin size) R)
    {selection : Fin size → Fin middle}
    (hselection : ¬Injective selection) :
    (∑ permutation : Equiv.Perm (Fin size),
        ((Equiv.Perm.sign permutation : ℤ) : R) *
          ∏ index,
            left (permutation index) (selection index) *
              right (selection index) index) = 0 := by
  obtain ⟨leftIndex, rightIndex, hsame, hne⟩ := Function.not_injective_iff.mp hselection
  refine Finset.sum_involution (fun permutation _ ↦ permutation * Equiv.swap leftIndex rightIndex)
    (fun permutation _ ↦ ?_) (fun permutation _ _ ↦ (not_congr mul_swap_eq_iff).mpr hne)
    (fun _ _ ↦ Finset.mem_univ _) (fun permutation _ ↦ mul_swap_involutive _ _ permutation)
  have hproduct : (∏ index, left (permutation index) (selection index)) =
      ∏ index, left ((permutation * Equiv.swap leftIndex rightIndex) index) (selection index) :=
    Fintype.prod_equiv (Equiv.swap leftIndex rightIndex) _ _ (by simp [apply_swap_eq_self hsame])
  simp [hproduct, sign_swap hne, -sign_swap', Finset.prod_mul_distrib]

private theorem sum_permutations_eq_det_mul
    {R : Type*} [CommRing R] {size : ℕ}
    (left right : Matrix (Fin size) (Fin size) R) :
    (∑ intermediate : Equiv.Perm (Fin size),
        ∑ rows : Equiv.Perm (Fin size),
          ((Equiv.Perm.sign rows : ℤ) : R) *
            ∏ index,
              left (rows index) (intermediate index) *
                right (intermediate index) index) =
      left.det * right.det := by
  calc
    _ = ∑ intermediate : Equiv.Perm (Fin size),
          ∑ rows : Equiv.Perm (Fin size),
            (∏ index, right (intermediate index) index) *
              ((Equiv.Perm.sign rows : ℤ) : R) *
                ∏ index, left (rows index) (intermediate index) := by
      simp only [mul_comm, mul_left_comm, Finset.prod_mul_distrib, mul_assoc]
    _ = ∑ intermediate : Equiv.Perm (Fin size),
          ∑ rows : Equiv.Perm (Fin size),
            (∏ index, right (intermediate index) index) *
              (((Equiv.Perm.sign intermediate : ℤ) : R) *
                ((Equiv.Perm.sign rows : ℤ) : R)) *
                  ∏ index, left (rows index) index := by
      refine Finset.sum_congr rfl fun intermediate _ ↦
        Fintype.sum_equiv (Equiv.mulRight intermediate⁻¹) _ _ fun rows ↦ ?_
      have hproduct :
          (∏ index,
              left (rows index) (intermediate index)) =
            ∏ index,
              left ((rows * intermediate⁻¹) index) index := by
        rw [← (intermediate⁻¹ : Fin size ≃ Fin size).prod_comp]
        simp
      have hsign : ((sign intermediate : ℤ) : R) * ((sign (rows * intermediate⁻¹) : ℤ) : R) =
          ((sign rows : ℤ) : R) := by
        rw [mul_comm, ← Int.cast_mul, ← Units.val_mul, ← Equiv.Perm.sign_mul,
          inv_mul_cancel_right]
      simp_rw [Equiv.coe_mulRight, hsign]
      simp only [hproduct]
    _ = left.det * right.det := by
      simp only [Matrix.det_apply', Finset.mul_sum, mul_comm,
        mul_left_comm, mul_assoc]

/-- Rectangular Cauchy–Binet, indexed by increasing choices of the
intermediate coordinates. -/
theorem det_mul_rectangular
    {R : Type*} [CommRing R] {size middle : ℕ}
    (left : Matrix (Fin size) (Fin middle) R)
    (right : Matrix (Fin middle) (Fin size) R) :
    (left * right).det =
      ∑ selection : (Fin size ↪o Fin middle),
        (left.submatrix id selection).det *
          (right.submatrix selection id).det := by
  calc
    (left * right).det = ∑ selection : Fin size → Fin middle, ∑ permutation : Perm (Fin size),
        ((sign permutation : ℤ) : R) *
          ∏ index, left (permutation index) (selection index) * right (selection index) index := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ selection : Fin size → Fin middle with Injective selection,
          ∑ permutation : Perm (Fin size), ((sign permutation : ℤ) : R) *
            ∏ index, left (permutation index) (selection index) * right (selection index) index :=
      (Finset.sum_subset (Finset.filter_subset _ _) fun selection _ hselection ↦
        determinantExpansion_eq_zero_of_not_injective left right (by simpa using hselection)).symm
    _ = ∑ selection : {selection : Fin size → Fin middle // Injective selection},
          ∑ permutation : Perm (Fin size), ((sign permutation : ℤ) : R) *
            ∏ index, left (permutation index) (selection.1 index) *
              right (selection.1 index) index := by
      simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun selection : Fin size → Fin middle ↦ Injective selection)
        (f := fun selection ↦ ∑ permutation : Perm (Fin size), ((sign permutation : ℤ) : R) *
          ∏ index, left (permutation index) (selection index) *
            right (selection index) index)).symm
    _ = ∑ data : (Fin size ↪o Fin middle) × Perm (Fin size),
          ∑ permutation : Perm (Fin size), ((sign permutation : ℤ) : R) *
            ∏ index, left (permutation index) (data.1 (data.2 index)) *
              right (data.1 (data.2 index)) index := by
      let equivalence := injectiveMapEquivOrderedSelectionPerm size middle
      refine Fintype.sum_equiv equivalence _ _ fun selection ↦ ?_
      have hdecompose : (equivalence selection).1 ∘ (equivalence selection).2 = selection.1 :=
        congrArg Subtype.val (equivalence.symm_apply_apply selection)
      simp_rw [← congrFun hdecompose]
      rfl
    _ = ∑ selection : (Fin size ↪o Fin middle), ∑ intermediate : Perm (Fin size),
          ∑ permutation : Perm (Fin size), ((sign permutation : ℤ) : R) *
            ∏ index, left (permutation index) (selection (intermediate index)) *
              right (selection (intermediate index)) index := Fintype.sum_prod_type _
    _ = _ := Finset.sum_congr rfl fun selection _ ↦ by
      simpa only [Matrix.submatrix_apply, id_eq] using
        sum_permutations_eq_det_mul (left.submatrix id selection) (right.submatrix selection id)

/-- Every ordered square minor of a rectangular matrix is nonnegative. -/
def IsOrderedMinorNonnegative {R : Type*} [CommRing R] [LE R]
    {rowCount columnCount : ℕ}
    (matrix : Matrix (Fin rowCount) (Fin columnCount) R) : Prop :=
  ∀ {size : ℕ}
    (rows : Fin size → Fin rowCount)
    (columns : Fin size → Fin columnCount),
    StrictMono rows →
    StrictMono columns →
    0 ≤ (matrix.submatrix rows columns).det

/-- An ordered minor of the identity matrix is its identity-permutation
term. -/
theorem det_submatrix_one_eq_prod
    {R : Type*} [CommRing R] [IsDomain R]
    (count size : ℕ)
    (rows columns : Fin size → Fin count)
    (hrows : StrictMono rows)
    (hcolumns : StrictMono columns) :
    (((1 : Matrix (Fin count) (Fin count) R).submatrix
      rows columns).det) =
      ∏ index, (1 : Matrix (Fin count) (Fin count) R)
        (rows index) (columns index) := by
  rw [Matrix.det_apply']
  refine (Finset.sum_eq_single (1 : Perm (Fin size)) (fun permutation _ hpermutation ↦ ?_)
    (by simp)).trans (by simp [Matrix.submatrix])
  have hproduct : (∏ index, (1 : Matrix (Fin count) (Fin count) R)
      (rows (permutation index)) (columns index)) = 0 := by
    by_contra hproduct
    have heq (index : Fin size) : rows (permutation index) = columns index := by
      by_contra hne
      exact Finset.prod_ne_zero_iff.mp hproduct index (Finset.mem_univ _)
        (Matrix.one_apply_ne hne)
    have hpermutationMono : StrictMono (fun index ↦ permutation index) := fun a b hab ↦
      hrows.lt_iff_lt.1 (by rw [heq a, heq b]; exact hcolumns hab)
    exact hpermutation (Equiv.ext fun index ↦ hpermutationMono.apply_eq)
  simp only [Matrix.submatrix_apply, hproduct, mul_zero]

/-- The identity matrix has nonnegative ordered minors. -/
theorem isOrderedMinorNonnegative_one
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (count : ℕ) :
    IsOrderedMinorNonnegative
      (1 : Matrix (Fin count) (Fin count) R) := by
  intro size rows columns hrows hcolumns
  rw [det_submatrix_one_eq_prod
    count size rows columns hrows hcolumns]
  exact Finset.prod_nonneg fun index _ ↦ by
    simp only [Matrix.one_apply]
    positivity

/-- Ordered-minor nonnegativity is closed under rectangular matrix
multiplication. -/
theorem IsOrderedMinorNonnegative.mul
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {rowCount middleCount columnCount : ℕ}
    {left : Matrix (Fin rowCount) (Fin middleCount) R}
    {right : Matrix (Fin middleCount) (Fin columnCount) R}
    (hleft : IsOrderedMinorNonnegative left)
    (hright : IsOrderedMinorNonnegative right) :
    IsOrderedMinorNonnegative (left * right) := by
  intro size rows columns hrows hcolumns
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, det_mul_rectangular]
  exact Finset.sum_nonneg fun selection _ ↦
    mul_nonneg
      (hleft rows selection hrows selection.strictMono)
      (hright selection columns selection.strictMono hcolumns)

/-- A sign `±1` times a nonnegative quantity is positive only if the sign is `1`. -/
private theorem sign_eq_one_of_mul_pos {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {size : ℕ} (σ : Perm (Fin size)) {d : R} (hd : 0 ≤ d)
    (hpos : 0 < ((sign σ : ℤ) : R) * d) : sign σ = 1 := by
  rcases Int.units_eq_one_or (sign σ) with h | h
  · exact h
  · rw [h] at hpos
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
      Left.neg_pos_iff] at hpos
    exact absurd hd (not_le.mpr hpos)

/-- One strictly positive intermediate minor makes the corresponding
minor of a product strictly positive when all other Cauchy–Binet terms
are nonnegative. The row and column maps need not be increasing: the positive minors make
them injective, and sorting them changes no sign. -/
theorem orderedMinor_mul_pos_of_witness
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {rowCount middleCount columnCount size : ℕ}
    {left : Matrix (Fin rowCount) (Fin middleCount) R}
    {right : Matrix (Fin middleCount) (Fin columnCount) R}
    (hleft : IsOrderedMinorNonnegative left)
    (hright : IsOrderedMinorNonnegative right)
    (rows : Fin size → Fin rowCount)
    (columns : Fin size → Fin columnCount)
    (intermediate : Fin size ↪o Fin middleCount)
    (hleftPositive :
      0 < (left.submatrix rows intermediate).det)
    (hrightPositive :
      0 < (right.submatrix intermediate columns).det) :
    0 < ((left * right).submatrix rows columns).det := by
  -- positive minors have injective row and column maps
  have hrinj : Function.Injective rows := fun i j hij ↦ by
    by_contra hne
    exact hleftPositive.ne' (Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]))
  have hcinj : Function.Injective columns := fun i j hij ↦ by
    by_contra hne
    exact hrightPositive.ne' (Matrix.det_zero_of_column_eq hne fun l ↦ by simp [hij])
  -- sort them
  set τ := Tuple.sort rows
  set ρ := Tuple.sort columns
  have hrows : StrictMono (rows ∘ τ) :=
    (Tuple.monotone_sort rows).strictMono_of_injective (hrinj.comp τ.injective)
  have hcolumns : StrictMono (columns ∘ ρ) :=
    (Tuple.monotone_sort columns).strictMono_of_injective (hcinj.comp ρ.injective)
  have hL : (left.submatrix (rows ∘ τ) intermediate).det =
      ((sign τ : ℤ) : R) * (left.submatrix rows intermediate).det := by
    rw [← Matrix.det_permute]; rfl
  have hR : (right.submatrix intermediate (columns ∘ ρ)).det =
      ((sign ρ : ℤ) : R) * (right.submatrix intermediate columns).det := by
    rw [← Matrix.det_permute']; rfl
  have hτ : sign τ = 1 := sign_eq_one_of_mul_pos τ hleftPositive.le
    (hL ▸ (hleft _ _ hrows intermediate.strictMono).lt_of_ne' ?_)
  · have hρ : sign ρ = 1 := sign_eq_one_of_mul_pos ρ hrightPositive.le
      (hR ▸ (hright _ _ intermediate.strictMono hcolumns).lt_of_ne' ?_)
    · -- the sorted product minor is positive by Cauchy–Binet
      have hsorted : 0 < ((left * right).submatrix (rows ∘ τ) (columns ∘ ρ)).det := by
        rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, det_mul_rectangular]
        refine Finset.sum_pos' (fun selection _ ↦ mul_nonneg
          (hleft (rows ∘ τ) selection hrows selection.strictMono)
          (hright selection (columns ∘ ρ) selection.strictMono hcolumns))
          ⟨intermediate, Finset.mem_univ _, ?_⟩
        simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp, hL, hR, hτ,
          hρ, Units.val_one, Int.cast_one, one_mul] using mul_pos hleftPositive hrightPositive
      have hP : ((left * right).submatrix (rows ∘ τ) (columns ∘ ρ)).det =
          ((left * right).submatrix rows columns).det := by
        have h1 := Matrix.det_permute τ (((left * right).submatrix rows columns).submatrix id ρ)
        have h2 := Matrix.det_permute' ρ ((left * right).submatrix rows columns)
        rw [hτ, Units.val_one, Int.cast_one, one_mul] at h1
        rw [hρ, Units.val_one, Int.cast_one, one_mul] at h2
        rw [← h2, ← h1]
        rfl
      rwa [hP] at hsorted
    · rw [hR]
      exact (mul_ne_zero (by simp) hrightPositive.ne')
  · rw [hL]
    exact (mul_ne_zero (by simp) hleftPositive.ne')

end CAS.Splines.Matrix
