/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Field

/-!
# Packed evaluation of a row of cells

For a row of cells `[x_p, x_{p+1}] × [c, d]` of a multilevel tensor B-spline field the node
engine computes, for each order `l` and end `f` of `[c, d]`, the scaled corner derivatives of the
cell functions of a block of cells in three steps:

* `stageOne`: for each level, the packed row over the tangential index `i` of
  `∑_t (R_t - α₁) D_{j₀ + t}`, where `D_j` is the packed column `j` of the coefficients at scale
  `2 ^ pa` and `R_t - α₁` the floor of `2 ^ pr` times the scaled normal jet of the normal mode
  `j₀ + t`, over the window of normal modes active on `[c, d]`;
* `stageTwo`: for each level, the packed row over the slots of the block of
  `∑_u H_{i₀ + u} G_{i₀ + u}`, where `H_i` is slot `i` of the first stage and `G_i` the packed
  table of the scaled corner jets of the tangential mode `i` at scale `2 ^ pt`, over the window of
  tangential modes active on the block;
* `mergeRows`: the sum over the levels.

`abs_signedSlot_mergeRows_sub_le` proves that each slot is within `cellRowError` of
`2 ^ (pa + pr + pt)` times `(b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ` of the cell function at the corner the
slot stands for. The error is computed from the integers of the evaluation and is local to the
block: an absolute error in the units of the cell, so the far field, where cells are large and
values small, is not charged with the errors of the large values near the origin. The theorem
needs only checkable hypotheses: the inputs are within stated numbers of units of their scaled
exact values (`εA`, `εR`, `εT`; `abs_modeTable_sub_le` gives `n + 3` units per term of a mode
for the integer tables), the modes outside the windows are inactive on the cells, and every
entry fits its slot.

## Main definitions

* `stageOneError`: the error of a slot of the first stage.
* `cellRowError`: the error of a slot of the merged row, from the first-stage errors and the
  bounds of the table entries.

## Main results

* `abs_signedSlot_mergeRows_sub_le`: every slot of the merged block row is within `cellRowError`
  of `2 ^ (pa + pr + pt)` times `(b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ` of the cell function at its corner.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset

/-- The first stage of one level: the coefficient columns `D (j₀ + t)` combined with the biased
normal jets `R t`, `t < n₁`, as a packed row over the tangential index. -/
def stageOne (w₁ α₁ rows : ℕ) (D R : ℕ → ℕ) (j₀ n₁ : ℕ) : ℕ :=
  packedRowCombination w₁ rows n₁ α₁ R (fun t ↦ D (j₀ + t))

/-- The second stage of one level on a block: the tangential tables `G (i₀ + u)` combined with
the first-stage slots `coef (i₀ + u)`, `u < n₂`, as a packed row over the slots of the block. -/
def stageTwo (w₁ w₂ q₂ : ℕ) (coef G : ℕ → ℕ) (i₀ n₂ : ℕ) : ℕ :=
  packedRowCombination w₂ q₂ n₂ (slotBias w₁) (fun u ↦ coef (i₀ + u)) (fun u ↦ G (i₀ + u))

/-- The error of slot `i` of the first stage, `∑_t (|R_t - α₁| εA + εR (|D_{j₀+t}(i)| + εA))`, for
coefficients within `εA` and normal jets within `εR` of their scaled values. -/
def stageOneError (w₁ α₁ εA εR : ℕ) (D R : ℕ → ℕ) (j₀ n₁ i : ℕ) : ℕ :=
  natSum n₁ fun t ↦ ((R t : ℤ) - α₁).natAbs * εA +
    εR * ((signedSlot w₁ i (D (j₀ + t))).natAbs + εA)

/-- The error of a slot of the merged row, given bounds `Tb m i` of the table entries of the
slot, tables within `εT`: `∑_m ∑_u (|H_{m,i}| εT + E_{m,i} (Tb m i + εT))` with `i = i₀ m + u`
and `E` the first-stage error. -/
def cellRowError (w₁ α₁ εA εR εT L : ℕ) (D R : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (Tb : ℕ → ℕ → ℕ)
    (i₀ n₂ j₀ n₁ : ℕ → ℕ) : ℕ :=
  natSum L fun m ↦ natSum (n₂ m) fun u ↦
    (signedSlot w₁ (i₀ m + u) (H m)).natAbs * εT +
      stageOneError w₁ α₁ εA εR (D m) (R m) (j₀ m) (n₁ m) (i₀ m + u) * (Tb m (i₀ m + u) + εT)

/-- A sum over `range N` of a function vanishing outside `[i₀, i₀ + n)` is the sum over the
window. -/
theorem sum_range_eq_sum_window {M : Type*} [AddCommMonoid M] {N i₀ n : ℕ} (F : ℕ → M)
    (hN : i₀ + n ≤ N) (hF : ∀ i < N, (i < i₀ ∨ i₀ + n ≤ i) → F i = 0) :
    ∑ i ∈ range N, F i = ∑ u ∈ range n, F (i₀ + u) := by
  rw [show ∑ u ∈ range n, F (i₀ + u) = ∑ i ∈ Finset.Ico i₀ (i₀ + n), F i by
    rw [Finset.sum_Ico_eq_sum_range]; simp]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    exact Finset.mem_range.mpr (by omega)
  · intro i hi hni
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hni
    exact hF i (Finset.mem_range.mp hi) (by omega)

/-- **Soundness of the cell-row evaluation.** Every slot of the merged block row is within
`cellRowError` of `2 ^ (pa + pr + pt)` times the scaled mixed derivative
`(b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ` of the cell function on `[a, b] × [c, d]` at the corner `(e, f)`
the slot holds, when the coefficient columns, the biased normal jets and the tangential tables
at the slot are within `εA`, `εR` and `εT` units of their scaled values, the modes outside the
windows are inactive on the cell, and every entry fits its slot. -/
theorem abs_signedSlot_mergeRows_sub_le {n L w₁ w₂ pa pr pt q₂ α₁ εA εR εT : ℕ}
    (lv : ℕ → Level)
    {wt : ℝ → ℝ} {l : ℕ} (hwt : ContDiff ℝ l wt) (a b c d : ℚ) (k : ℕ) (e f : Bool)
    {s : ℕ} (hs : s < q₂) (D R G coef : ℕ → ℕ → ℕ) (Tb : ℕ → ℕ → ℕ) (i₀ n₂ j₀ n₁ : ℕ → ℕ)
    (hL : 0 < L) (hxK : ∀ m < L, StrictMono (lv m).xKnots)
    (hyK : ∀ m < L, StrictMono (lv m).yKnots)
    (hi : ∀ m < L, i₀ m + n₂ m ≤ (lv m).rows) (hj : ∀ m < L, j₀ m + n₁ m ≤ (lv m).cols)
    (hxw : ∀ m < L, ∀ i < (lv m).rows, (i < i₀ m ∨ i₀ m + n₂ m ≤ i) →
      ∀ τ ∈ (lv m).xModes i, τ.Inactive n (lv m).xKnots a b)
    (hyw : ∀ m < L, ∀ j < (lv m).cols, (j < j₀ m ∨ j₀ m + n₁ m ≤ j) →
      ∀ τ ∈ (lv m).yModes j, τ.Inactive n (lv m).yKnots c d)
    (hD : ∀ m < L, ∀ t < n₁ m, D m (j₀ m + t) < 2 ^ (w₁ * (lv m).rows))
    (hDv : ∀ m < L, ∀ i < (lv m).rows, ∀ t < n₁ m,
      |(signedSlot w₁ i (D m (j₀ m + t)) : ℝ) - 2 ^ pa * ((lv m).coeff i (j₀ m + t) : ℝ)| ≤ εA)
    (hR : ∀ m < L, ∀ t < n₁ m, |(((R m t : ℤ) - α₁ : ℤ) : ℝ) -
      2 ^ pr * weightedJet n (lv m).yKnots ((lv m).yModes (j₀ m + t)) wt c d l f| ≤ εR)
    (hfit₁ : ∀ m < L, ∀ i < (lv m).rows, FitsSlot w₁
      (∑ t ∈ range (n₁ m), ((R m t : ℤ) - α₁) * signedSlot w₁ i (D m (j₀ m + t))))
    (hcoef : ∀ m < L, ∀ u < n₂ m, coef m (i₀ m + u) =
      slot w₁ (i₀ m + u) (stageOne w₁ α₁ (lv m).rows (D m) (R m) (j₀ m) (n₁ m)))
    (hG : ∀ m < L, ∀ u < n₂ m, G m (i₀ m + u) < 2 ^ (w₂ * q₂))
    (hGv : ∀ m < L, ∀ u < n₂ m, |(signedSlot w₂ s (G m (i₀ m + u)) : ℝ) -
      2 ^ pt * (cornerJet n (lv m).xKnots ((lv m).xModes (i₀ m + u)) a b k e : ℝ)| ≤ εT)
    (hTb : ∀ m < L, ∀ u < n₂ m, (signedSlot w₂ s (G m (i₀ m + u))).natAbs ≤ Tb m (i₀ m + u))
    (hfit₂ : ∀ m < L, ∀ s' < q₂, FitsSlot w₂ (∑ u ∈ range (n₂ m),
      ((coef m (i₀ m + u) : ℤ) - slotBias w₁) * signedSlot w₂ s' (G m (i₀ m + u))))
    (hfit : ∀ s' < q₂, FitsSlot w₂ (∑ m ∈ range L,
      signedSlot w₂ s' (stageTwo w₁ w₂ q₂ (coef m) (G m) (i₀ m) (n₂ m)))) :
    |(signedSlot w₂ s (mergeRows w₂ q₂ L
        fun m ↦ stageTwo w₁ w₂ q₂ (coef m) (G m) (i₀ m) (n₂ m)) : ℝ) -
      2 ^ (pa + pr + pt) * (((b : ℝ) - a) ^ k * ((d : ℝ) - c) ^ l * mixedDeriv k l
        (cellField n L lv wt a b c d) (if e then (b : ℝ) else a) (if f then (d : ℝ) else c))| ≤
      (cellRowError w₁ α₁ εA εR εT L D R
        (fun m ↦ stageOne w₁ α₁ (lv m).rows (D m) (R m) (j₀ m) (n₁ m)) Tb i₀ n₂ j₀ n₁ : ℝ) := by
  -- notation
  set H : ℕ → ℕ := fun m ↦ stageOne w₁ α₁ (lv m).rows (D m) (R m) (j₀ m) (n₁ m) with hHdef
  set B : ℕ → ℕ := fun m ↦ stageTwo w₁ w₂ q₂ (coef m) (G m) (i₀ m) (n₂ m) with hBdef
  set r : ℕ → ℕ → ℝ := fun m j ↦ weightedJet n (lv m).yKnots ((lv m).yModes j) wt c d l f
  set τ : ℕ → ℕ → ℝ := fun m i ↦ (cornerJet n (lv m).xKnots ((lv m).xModes i) a b k e : ℝ)
  set h : ℕ → ℕ → ℝ := fun m i ↦ ∑ t ∈ range (n₁ m), r m (j₀ m + t) * (lv m).coeff i (j₀ m + t)
  -- the exact value as a sum over the windows
  have hexact : ((b : ℝ) - a) ^ k * ((d : ℝ) - c) ^ l * mixedDeriv k l
      (cellField n L lv wt a b c d) (if e then (b : ℝ) else a) (if f then (d : ℝ) else c) =
      ∑ m ∈ range L, ∑ u ∈ range (n₂ m), h m (i₀ m + u) * τ m (i₀ m + u) := by
    rw [mixedDeriv_cellField n L lv hwt a b c d k e f]
    refine sum_congr rfl fun m hm ↦ ?_
    have hm' := mem_range.mp hm
    have hτ0 : ∀ i < (lv m).rows, (i < i₀ m ∨ i₀ m + n₂ m ≤ i) → τ m i = 0 := by
      intro i hi' hout
      simp only [τ, cornerJet]
      rw [jet_eq_zero (hxK m hm') (hxw m hm' i hi' hout), mul_zero, Rat.cast_zero]
    have hr0 : ∀ j < (lv m).cols, (j < j₀ m ∨ j₀ m + n₁ m ≤ j) → r m j = 0 := by
      intro j hj' hout
      simp only [r, weightedJet]
      rw [piece_eq_zero (hyK m hm') (hyw m hm' j hj' hout)]
      simp
    rw [sum_range_eq_sum_window (fun i ↦ ∑ j ∈ range (lv m).cols,
      ((lv m).coeff i j : ℝ) * τ m i * r m j) (hi m hm') (fun i hi' hout ↦ by
        simp [hτ0 i hi' hout])]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [sum_range_eq_sum_window (fun j ↦ ((lv m).coeff (i₀ m + u) j : ℝ) * τ m (i₀ m + u) *
      r m j) (hj m hm') (fun j hj' hout ↦ by simp [hr0 j hj' hout]), sum_mul]
    exact sum_congr rfl fun t _ ↦ by ring
  -- stage one, slot by slot
  have hone : ∀ m < L, ∀ u < n₂ m,
      |(signedSlot w₁ (i₀ m + u) (H m) : ℝ) - 2 ^ (pr + pa) * h m (i₀ m + u)| ≤
        (stageOneError w₁ α₁ εA εR (D m) (R m) (j₀ m) (n₁ m) (i₀ m + u) : ℝ) := by
    intro m hm u hu
    have hiu : i₀ m + u < (lv m).rows := by have := hi m hm; omega
    have := abs_signedSlot_packedRowCombination_sub_le (fun t ht ↦ hD m hm t ht)
      (hfit₁ m hm) hiu (p₁ := pr) (p₂ := pa) (fun t ↦ r m (j₀ m + t))
      (fun t ↦ ((lv m).coeff (i₀ m + u) (j₀ m + t) : ℝ)) (fun _ ↦ (εR : ℝ)) (fun _ ↦ (εA : ℝ))
      (fun t ht ↦ hR m hm t ht) (fun t ht ↦ hDv m hm (i₀ m + u) hiu t ht)
    refine this.trans (le_of_eq ?_)
    unfold stageOneError
    rw [natSum_eq_sum]
    push_cast
    refine sum_congr rfl fun t _ ↦ ?_
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    ring
  -- stage two, level by level
  have htwo : ∀ m < L, |(signedSlot w₂ s (B m) : ℝ) -
      2 ^ (pr + pa + pt) * ∑ u ∈ range (n₂ m), h m (i₀ m + u) * τ m (i₀ m + u)| ≤
      ∑ u ∈ range (n₂ m), ((signedSlot w₁ (i₀ m + u) (H m)).natAbs * εT +
        stageOneError w₁ α₁ εA εR (D m) (R m) (j₀ m) (n₁ m) (i₀ m + u) *
          (Tb m (i₀ m + u) + εT) : ℕ) := by
    intro m hm
    have := abs_signedSlot_packedRowCombination_sub_le (fun u hu ↦ hG m hm u hu)
      (hfit₂ m hm) hs (p₁ := pr + pa) (p₂ := pt) (fun u ↦ h m (i₀ m + u))
      (fun u ↦ τ m (i₀ m + u))
      (fun u ↦ (stageOneError w₁ α₁ εA εR (D m) (R m) (j₀ m) (n₁ m) (i₀ m + u) : ℝ))
      (fun _ ↦ (εT : ℝ))
      (fun u hu ↦ by
        rw [hcoef m hm u hu]
        have h1 := hone m hm u hu
        simp only [signedSlot] at h1 ⊢
        push_cast at h1 ⊢
        exact h1)
      (fun u hu ↦ hGv m hm u hu)
    refine this.trans ?_
    push_cast
    refine sum_le_sum fun u hu ↦ ?_
    have hu' := mem_range.mp hu
    have hc : ((coef m (i₀ m + u) : ℝ) - (slotBias w₁ : ℝ)) =
        (signedSlot w₁ (i₀ m + u) (H m) : ℝ) := by
      rw [hcoef m hm u hu']
      simp [signedSlot, H]
    rw [hc]
    have hH : |(signedSlot w₁ (i₀ m + u) (H m) : ℝ)| =
        ((signedSlot w₁ (i₀ m + u) (H m)).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hT : (|(signedSlot w₂ s (G m (i₀ m + u)) : ℝ)|) ≤ (Tb m (i₀ m + u) : ℝ) := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hTb m hm u hu'
    have hE : (0 : ℝ) ≤ stageOneError w₁ α₁ εA εR (D m) (R m) (j₀ m) (n₁ m) (i₀ m + u) :=
      Nat.cast_nonneg _
    rw [hH]
    nlinarith
  -- merging the levels
  have hcast : ∀ m < L, (B m : ℤ) = ∑ s' ∈ range q₂,
      (signedSlot w₂ s' (B m) + slotBias w₂) * 2 ^ (w₂ * s') := by
    intro m hm
    have hc := cast_packedRowCombination (w := w₂) (q := q₂) (n := n₂ m) (α := slotBias w₁)
      (s := fun u ↦ coef m (i₀ m + u)) (rows := fun u ↦ G m (i₀ m + u))
      (fun u hu ↦ hG m hm u hu) (hfit₂ m hm)
    have hsig : ∀ s' < q₂, signedSlot w₂ s' (B m) = ∑ u ∈ range (n₂ m),
        ((coef m (i₀ m + u) : ℤ) - slotBias w₁) * signedSlot w₂ s' (G m (i₀ m + u)) :=
      fun s' hs' ↦ signedSlot_packedRowCombination (fun u hu ↦ hG m hm u hu) (hfit₂ m hm) hs'
    calc (B m : ℤ) = _ := hc
      _ = _ := sum_congr rfl fun s' hs' ↦ by rw [hsig s' (mem_range.mp hs')]
  have hmerge := signedSlot_mergeRows (w := w₂) (q := q₂) (L := L) (B := B)
    (c := fun m s' ↦ signedSlot w₂ s' (B m)) hL hcast hfit hs
  -- assembly
  rw [hmerge, hexact, mul_sum, show pa + pr + pt = pr + pa + pt by ring]
  push_cast
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  unfold cellRowError
  rw [natSum_eq_sum]
  push_cast
  refine sum_le_sum fun m hm ↦ ?_
  refine (htwo m (mem_range.mp hm)).trans (le_of_eq ?_)
  rw [natSum_eq_sum]

end CAS.Numerics.TensorSpline
