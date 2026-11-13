/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import PDE.Common.Euclidean
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# Faà di Bruno bounds with the top-order terms separated

By the Faà di Bruno formula, the `n`-th derivative of `g ∘ f` is the sum over the ordered
partitions `c` of `Fin n` of `D^{|c|} g(f x)` applied to the derivatives of `f` of the orders of the
blocks of `c` (`FormalMultilinearSeries.taylorComp`). Only two partitions involve a derivative of
order `n`: the partition into one block gives `D g(f x) ∘ D^n f(x)` and the partition into
singletons gives `D^n g(f x)[D f(x), …, D f(x)]`; every other partition has between `2` and `n - 1`
blocks, each of size at most `n - 1`. We isolate these two terms, so that bounds of the
`n`-th derivative of a composition, and of its differences at two points, are linear in the
derivatives of order `n` of `f` and `g`, with coefficients depending only on the derivatives of
lower order. This linearity is what Grönwall arguments for the regularity of transported
quantities need.

For a bounded bilinear map `B`, the Leibniz formula has the same structure: in
`Dⁿ B(f, g) = ∑ᵢ C(n, i) B(Dⁱf, Dⁿ⁻ⁱg)` only the terms `i = 0` and `i = n` contain derivatives of
order `n`; we add the bound of the difference at two points, which Mathlib does not
state, and isolate these two terms.

## Main results

* `taylorComp_eq_add`: the decomposition of `q.taylorComp p n`, `n ≥ 2`, into the one-block term,
  the singleton term and `taylorCompRemainder q p n`.
* `norm_taylorCompRemainder_le`, `norm_taylorCompRemainder_sub_le`, `norm_taylorComp_le`,
  `norm_taylorComp_sub_le`: bounds of the remainder, of the Taylor composition, and of the
  differences of two of them, with the top-order coefficients appearing linearly.
* `iteratedFDerivWithin_comp_eq_add`: `Dⁿ(g ∘ f)(x) = D g(f x) ∘ Dⁿf(x) +
  Dⁿg(f x)[Df(x), …, Df(x)] + R` for `n ≥ 2`.
* `norm_iteratedFDerivWithin_comp_le_add`, `norm_iteratedFDerivWithin_comp_sub_le_add`: the size
  and the difference at two points of `Dⁿ(g ∘ f)`, top-order terms separated.
* `norm_iteratedFDerivWithin_comp_sub_le_rpow`,
  `norm_iteratedFDerivWithin_comp_sub_le_rpow_of_closedUpper`: the `α`-Hölder constant of
  `Dⁿ(g ∘ f)`, linear in the top-order bounds and Hölder constants of `f` and `g`.
* `norm_iteratedFDerivWithin_bilinear_sub_le`: Leibniz bound of the difference at two points of
  `Dⁿ B(f, g)`; `norm_iteratedFDerivWithin_bilinear_le_add`,
  `norm_iteratedFDerivWithin_bilinear_sub_le_add`: the size and the difference with the two
  top-order terms separated.
-/

@[expose] public section

noncomputable section

open Set Finset

namespace PDE.Analysis

/-! ### Ordered partitions with one block and with singletons -/

section Partitions

variable {n : ℕ}

/-- The sizes of the blocks of an ordered partition of `Fin n` add up to `n`. -/
theorem sum_partSize (c : OrderedFinpartition n) : ∑ i, c.partSize i = n := by
  have h := c.sum_sigma_eq_sum (fun _ : Fin n ↦ (1 : ℕ))
  simpa using h

/-- The ordered partition of `Fin n`, `0 < n`, into a single block. -/
def singleFinpartition (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint _ _ _ _ h := absurd (Subsingleton.elim _ _) h
  cover x := ⟨0, x, rfl⟩

/-- An ordered partition with one block is the partition into a single block. -/
theorem eq_singleFinpartition (hn : 0 < n) (c : OrderedFinpartition n) (hc : c.length = 1) :
    c = singleFinpartition n hn := by
  have hsum := sum_partSize c
  rcases c with ⟨length, partSize, hpos, emb, hmono, hparts, hdisj, hcover⟩
  subst hc
  simp only [Fin.sum_univ_one] at hsum
  obtain rfl : partSize = fun _ ↦ n := funext fun i ↦ by rw [Subsingleton.elim i 0, hsum]
  obtain rfl : emb = fun _ ↦ id := funext fun m ↦ (hmono m).eq_id
  rfl

/-- An ordered partition of `Fin n` with `n` blocks has blocks of size one. -/
theorem partSize_eq_one_of_length_eq (c : OrderedFinpartition n) (hc : c.length = n)
    (i : Fin c.length) : c.partSize i = 1 := by
  have hsum := sum_partSize c
  have hsplit : ∑ j, c.partSize j = ∑ _j : Fin c.length, 1 + ∑ j, (c.partSize j - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by have := c.partSize_pos j; omega
  have hzero : ∑ j, (c.partSize j - 1) = 0 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      at hsplit
    omega
  have := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
  have := c.partSize_pos i
  omega

/-- An ordered partition of `Fin n` with `n` blocks is the partition into singletons. -/
theorem eq_atomic_of_length_eq (c : OrderedFinpartition n) (hc : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  have hsize := partSize_eq_one_of_length_eq c hc
  rcases c with ⟨length, partSize, hpos, emb, hmono, hparts, hdisj, hcover⟩
  obtain rfl : n = length := hc.symm
  obtain rfl : partSize = fun _ ↦ 1 := funext hsize
  have hid : (fun m ↦ emb m ⟨0, Nat.one_pos⟩) = id := hparts.eq_id
  obtain rfl : emb = fun m _ ↦ m := by
    funext m j
    rw [Subsingleton.elim j ⟨0, Nat.one_pos⟩]
    exact congrFun hid m
  rfl

/-- In an ordered partition with at least two blocks every block has size less than `n`. -/
theorem partSize_lt_of_two_le_length (c : OrderedFinpartition n) (hc : 2 ≤ c.length)
    (i : Fin c.length) : c.partSize i < n := by
  have hsum := sum_partSize c
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  have hcard : 1 ≤ ((Finset.univ : Finset (Fin c.length)).erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hle : ((Finset.univ : Finset (Fin c.length)).erase i).card ≤
      ∑ j ∈ (Finset.univ : Finset (Fin c.length)).erase i, c.partSize j := by
    have := Finset.card_nsmul_le_sum ((Finset.univ : Finset (Fin c.length)).erase i)
      c.partSize 1 fun j _ ↦ c.partSize_pos j
    simpa only [smul_eq_mul, mul_one] using this
  omega

end Partitions

/-! ### The decomposition of the Taylor composition -/

section Series

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The terms of the Faà di Bruno sum of order `n` of `q` and `p` other than the one-block term
and the singleton term: the sum over the ordered partitions with between `2` and `n - 1`
blocks. -/
def taylorCompRemainder (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F)
    (n : ℕ) : E [×n]→L[ℝ] G :=
  ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n ↦ 2 ≤ c.length ∧ c.length < n),
    q.compAlongOrderedFinpartition p c

/-- **The top-order terms of the Faà di Bruno sum.** For `n ≥ 2` the Taylor composition of order
`n` is the one-block term plus the singleton term plus `taylorCompRemainder`. -/
theorem taylorComp_eq_add {n : ℕ} (hn : 2 ≤ n) (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) :
    q.taylorComp p n =
      q.compAlongOrderedFinpartition p (singleFinpartition n (by omega)) +
        q.compAlongOrderedFinpartition p (OrderedFinpartition.atomic n) +
        taylorCompRemainder q p n := by
  set c₁ := singleFinpartition n (by omega)
  set cₙ := OrderedFinpartition.atomic n
  have hne : cₙ ≠ c₁ := fun h ↦ by
    have := congrArg OrderedFinpartition.length h
    simp only [cₙ, c₁, OrderedFinpartition.atomic_length, singleFinpartition] at this
    omega
  have h₁ : c₁ ∈ (Finset.univ : Finset (OrderedFinpartition n)) := Finset.mem_univ _
  have hₙ : cₙ ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase c₁ :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hrest : ((Finset.univ : Finset (OrderedFinpartition n)).erase c₁).erase cₙ =
      Finset.univ.filter (fun c : OrderedFinpartition n ↦ 2 ≤ c.length ∧ c.length < n) := by
    ext c
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and]
    have hpos : 1 ≤ c.length := c.length_pos (by omega)
    have hle : c.length ≤ n := c.length_le
    constructor
    · rintro ⟨hcn, hc1⟩
      have h1 : c.length ≠ 1 := fun h ↦ hc1 (eq_singleFinpartition (by omega) c h)
      have h2 : c.length ≠ n := fun h ↦ hcn (eq_atomic_of_length_eq c h)
      omega
    · rintro ⟨h2, hlt⟩
      exact ⟨fun h ↦ absurd (congrArg OrderedFinpartition.length h)
          (by simp only [cₙ, OrderedFinpartition.atomic_length]; omega),
        fun h ↦ absurd (congrArg OrderedFinpartition.length h)
          (by simp only [c₁, singleFinpartition]; omega)⟩
  rw [FormalMultilinearSeries.taylorComp, ← Finset.add_sum_erase _ _ h₁,
    ← Finset.add_sum_erase _ _ hₙ, hrest, taylorCompRemainder, add_assoc]


/-! ### Bounds of the remainder -/

variable {n : ℕ} {q q₁ q₂ : FormalMultilinearSeries ℝ F G} {p p₁ p₂ : FormalMultilinearSeries ℝ E F}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- A product of `k ≤ n` factors at most `max 1 M` is at most `max 1 M ^ n`. -/
theorem prod_le_max_one_pow {ι : Type*} [Fintype ι] {a : ι → ℝ} {M : ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha : ∀ i, a i ≤ M) (hcard : Fintype.card ι ≤ n) : ∏ i, a i ≤ max 1 M ^ n := by
  calc ∏ i, a i ≤ ∏ _i : ι, max 1 M :=
        Finset.prod_le_prod₀ (fun i _ ↦ ha0 i) fun i _ ↦ (ha i).trans (le_max_right _ _)
    _ = max 1 M ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
    _ ≤ max 1 M ^ n := pow_le_pow_right₀ (le_max_left _ _) hcard

/-- **Bound of the remainder.** If the coefficients of `q` of orders `2, …, n - 1` are at most
`Mq` and those of `p` of orders `1, …, n - 1` at most `Mp`, the remainder is at most
`(number of ordered partitions) · Mq · max 1 Mp ^ n`. -/
theorem norm_taylorCompRemainder_le {Mq Mp : ℝ} (hMq : 0 ≤ Mq)
    (hq : ∀ i, 2 ≤ i → i < n → ‖q i‖ ≤ Mq) (hp : ∀ j, 1 ≤ j → j < n → ‖p j‖ ≤ Mp) :
    ‖taylorCompRemainder q p n‖ ≤ Fintype.card (OrderedFinpartition n) * (Mq * max 1 Mp ^ n) := by
  have hterm (c : OrderedFinpartition n)
      (hc : c ∈ Finset.univ.filter (fun c : OrderedFinpartition n ↦ 2 ≤ c.length ∧ c.length < n)) :
      ‖q.compAlongOrderedFinpartition p c‖ ≤ Mq * max 1 Mp ^ n := by
    obtain ⟨h2, hlt⟩ := (Finset.mem_filter.mp hc).2
    refine (c.norm_compAlongOrderedFinpartition_le _ _).trans ?_
    refine mul_le_mul (hq _ h2 hlt) (prod_le_max_one_pow (fun i ↦ norm_nonneg _) (fun i ↦ ?_)
      (by rw [Fintype.card_fin]; exact c.length_le)) (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
      hMq
    exact hp _ (c.partSize_pos i) (partSize_lt_of_two_le_length c h2 i)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_)
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)

/-- **Difference of two remainders.** With the coefficients of `q₁` of orders `2, …, n - 1` at
most `Mq`, differing from those of `q₂` by at most `δq`, and the coefficients of `p₁, p₂` of orders
`1, …, n - 1` at most `Mp`, differing by at most `δp`, the remainders differ by at most
`(number of ordered partitions) · (Mq n δp + δq) · max 1 Mp ^ n`. -/
theorem norm_taylorCompRemainder_sub_le {Mq Mp δq δp : ℝ} (hMq : 0 ≤ Mq) (hMp : 0 ≤ Mp)
    (hδq : 0 ≤ δq) (hδp : 0 ≤ δp) (hq : ∀ i, 2 ≤ i → i < n → ‖q₁ i‖ ≤ Mq)
    (hdq : ∀ i, 2 ≤ i → i < n → ‖q₁ i - q₂ i‖ ≤ δq) (hp₁ : ∀ j, 1 ≤ j → j < n → ‖p₁ j‖ ≤ Mp)
    (hp₂ : ∀ j, 1 ≤ j → j < n → ‖p₂ j‖ ≤ Mp) (hdp : ∀ j, 1 ≤ j → j < n → ‖p₁ j - p₂ j‖ ≤ δp) :
    ‖taylorCompRemainder q₁ p₁ n - taylorCompRemainder q₂ p₂ n‖ ≤
      Fintype.card (OrderedFinpartition n) * ((Mq * n * δp + δq) * max 1 Mp ^ n) := by
  set S := Finset.univ.filter (fun c : OrderedFinpartition n ↦ 2 ≤ c.length ∧ c.length < n)
  have hterm (c : OrderedFinpartition n) (hc : c ∈ S) :
      ‖q₁.compAlongOrderedFinpartition p₁ c - q₂.compAlongOrderedFinpartition p₂ c‖ ≤
        (Mq * n * δp + δq) * max 1 Mp ^ n := by
    obtain ⟨h2, hlt⟩ := (Finset.mem_filter.mp hc).2
    have hsize (i : Fin c.length) : 1 ≤ c.partSize i ∧ c.partSize i < n :=
      ⟨c.partSize_pos i, partSize_lt_of_two_le_length c h2 i⟩
    set g₁ : ∀ i : Fin c.length, E [×c.partSize i]→L[ℝ] F := fun i ↦ p₁ (c.partSize i)
    set g₂ : ∀ i : Fin c.length, E [×c.partSize i]→L[ℝ] F := fun i ↦ p₂ (c.partSize i)
    have hg₁ : ‖g₁‖ ≤ Mp := (pi_norm_le_iff_of_nonneg hMp).mpr fun i ↦
      hp₁ _ (hsize i).1 (hsize i).2
    have hg₂ : ‖g₂‖ ≤ Mp := (pi_norm_le_iff_of_nonneg hMp).mpr fun i ↦
      hp₂ _ (hsize i).1 (hsize i).2
    have hdg : ‖g₁ - g₂‖ ≤ δp := (pi_norm_le_iff_of_nonneg hδp).mpr fun i ↦
      hdp _ (hsize i).1 (hsize i).2
    have hmax : max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) ≤ max 1 Mp ^ n :=
      calc max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) ≤ max 1 Mp ^ (c.length - 1) :=
            pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _))
              (max_le (hg₁.trans (le_max_right _ _)) (hg₂.trans (le_max_right _ _))) _
        _ ≤ max 1 Mp ^ n := pow_le_pow_right₀ (le_max_left _ _) (by have := c.length_le; omega)
    have hprod : ∏ i, ‖g₂ i‖ ≤ max 1 Mp ^ n :=
      prod_le_max_one_pow (fun i ↦ norm_nonneg _) (fun i ↦ hp₂ _ (hsize i).1 (hsize i).2)
        (by rw [Fintype.card_fin]; exact c.length_le)
    have hlen : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
    refine (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
      (q₁ c.length) (q₂ c.length) g₁ g₂).trans ?_
    calc ‖q₁ c.length‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ +
          ‖q₁ c.length - q₂ c.length‖ * ∏ i, ‖g₂ i‖
        ≤ Mq * n * max 1 Mp ^ n * δp + δq * max 1 Mp ^ n := by
          gcongr
          exacts [hq _ h2 hlt, hdq _ h2 hlt]
      _ = (Mq * n * δp + δq) * max 1 Mp ^ n := by ring
  rw [taylorCompRemainder, taylorCompRemainder, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_)
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)

/-! ### The one-block and the singleton terms -/

/-- The one-block term is at most `‖q 1‖ ‖p n‖`. -/
theorem norm_compAlongOrderedFinpartition_single_le (hn : 0 < n) :
    ‖q.compAlongOrderedFinpartition p (singleFinpartition n hn)‖ ≤ ‖q 1‖ * ‖p n‖ := by
  refine ((singleFinpartition n hn).norm_compAlongOrderedFinpartition_le _ _).trans_eq ?_
  change ‖q 1‖ * ∏ _i : Fin 1, ‖p n‖ = _
  rw [Fin.prod_univ_one]

/-- The singleton term is at most `‖q n‖ ‖p 1‖ ^ n`. -/
theorem norm_compAlongOrderedFinpartition_atomic_le :
    ‖q.compAlongOrderedFinpartition p (OrderedFinpartition.atomic n)‖ ≤ ‖q n‖ * ‖p 1‖ ^ n := by
  refine ((OrderedFinpartition.atomic n).norm_compAlongOrderedFinpartition_le _ _).trans_eq ?_
  change ‖q n‖ * ∏ _i : Fin n, ‖p 1‖ = _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Difference of two one-block terms. -/
theorem norm_compAlongOrderedFinpartition_single_sub_le (hn : 0 < n) :
    ‖q₁.compAlongOrderedFinpartition p₁ (singleFinpartition n hn) -
        q₂.compAlongOrderedFinpartition p₂ (singleFinpartition n hn)‖ ≤
      ‖q₁ 1‖ * ‖p₁ n - p₂ n‖ + ‖q₁ 1 - q₂ 1‖ * ‖p₂ n‖ := by
  set c := singleFinpartition n hn
  have h := c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (q₁ c.length) (q₂ c.length) (fun i ↦ p₁ (c.partSize i)) (fun i ↦ p₂ (c.partSize i))
  have hd : ‖(fun i ↦ p₁ (c.partSize i)) - fun i ↦ p₂ (c.partSize i)‖ = ‖p₁ n - p₂ n‖ :=
    pi_norm_const (ι := Fin 1) (p₁ n - p₂ n)
  rw [hd] at h
  refine h.trans_eq ?_
  change ‖q₁ 1‖ * ((1 : ℕ) : ℝ) * max ‖fun _i : Fin 1 ↦ p₁ n‖ ‖fun _i : Fin 1 ↦ p₂ n‖ ^ (1 - 1) *
      ‖p₁ n - p₂ n‖ + ‖q₁ 1 - q₂ 1‖ * ∏ _i : Fin 1, ‖p₂ n‖ = _
  rw [Fin.prod_univ_one, Nat.sub_self, pow_zero, Nat.cast_one, mul_one, mul_one]

/-- Difference of two singleton terms. -/
theorem norm_compAlongOrderedFinpartition_atomic_sub_le (hn : 0 < n) :
    ‖q₁.compAlongOrderedFinpartition p₁ (OrderedFinpartition.atomic n) -
        q₂.compAlongOrderedFinpartition p₂ (OrderedFinpartition.atomic n)‖ ≤
      ‖q₁ n‖ * n * max ‖p₁ 1‖ ‖p₂ 1‖ ^ (n - 1) * ‖p₁ 1 - p₂ 1‖ +
        ‖q₁ n - q₂ n‖ * ‖p₂ 1‖ ^ n := by
  set c := OrderedFinpartition.atomic n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (q₁ c.length) (q₂ c.length) (fun i ↦ p₁ (c.partSize i)) (fun i ↦ p₂ (c.partSize i))
  have hd : ‖(fun i ↦ p₁ (c.partSize i)) - fun i ↦ p₂ (c.partSize i)‖ = ‖p₁ 1 - p₂ 1‖ :=
    pi_norm_const (ι := Fin n) (p₁ 1 - p₂ 1)
  have h₁ : ‖fun i ↦ p₁ (c.partSize i)‖ = ‖p₁ 1‖ := pi_norm_const (ι := Fin n) (p₁ 1)
  have h₂ : ‖fun i ↦ p₂ (c.partSize i)‖ = ‖p₂ 1‖ := pi_norm_const (ι := Fin n) (p₂ 1)
  rw [hd, h₁, h₂] at h
  refine h.trans_eq ?_
  change ‖q₁ n‖ * (n : ℝ) * max ‖p₁ 1‖ ‖p₂ 1‖ ^ (n - 1) * ‖p₁ 1 - p₂ 1‖ +
      ‖q₁ n - q₂ n‖ * ∏ _i : Fin n, ‖p₂ 1‖ = _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Bounds of the Taylor composition -/

/-- **Size of the Taylor composition with the top-order terms separated**: for `n ≥ 2`,
`‖(q.taylorComp p) n‖ ≤ ‖q 1‖ ‖p n‖ + ‖q n‖ ‖p 1‖ ^ n + (number of ordered partitions) Mq
max 1 Mp ^ n`, with `Mq` bounding the coefficients of `q` of orders `2, …, n - 1` and `Mp` those of
`p` of orders `1, …, n - 1`. -/
theorem norm_taylorComp_le (hn : 2 ≤ n) {Mq Mp : ℝ} (hMq : 0 ≤ Mq)
    (hq : ∀ i, 2 ≤ i → i < n → ‖q i‖ ≤ Mq) (hp : ∀ j, 1 ≤ j → j < n → ‖p j‖ ≤ Mp) :
    ‖q.taylorComp p n‖ ≤ ‖q 1‖ * ‖p n‖ + ‖q n‖ * ‖p 1‖ ^ n +
      Fintype.card (OrderedFinpartition n) * (Mq * max 1 Mp ^ n) := by
  rw [taylorComp_eq_add hn]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact norm_compAlongOrderedFinpartition_single_le _
  · exact norm_compAlongOrderedFinpartition_atomic_le
  · exact norm_taylorCompRemainder_le hMq hq hp

/-- **Difference of two Taylor compositions with the top-order terms separated**: the
coefficients of order `n` of `p₁, p₂, q₁, q₂` enter only through the one-block and the singleton
terms, linearly. -/
theorem norm_taylorComp_sub_le (hn : 2 ≤ n) {Mq Mp δq δp : ℝ} (hMq : 0 ≤ Mq) (hMp : 0 ≤ Mp)
    (hδq : 0 ≤ δq) (hδp : 0 ≤ δp) (hq : ∀ i, 2 ≤ i → i < n → ‖q₁ i‖ ≤ Mq)
    (hdq : ∀ i, 2 ≤ i → i < n → ‖q₁ i - q₂ i‖ ≤ δq) (hp₁ : ∀ j, 1 ≤ j → j < n → ‖p₁ j‖ ≤ Mp)
    (hp₂ : ∀ j, 1 ≤ j → j < n → ‖p₂ j‖ ≤ Mp) (hdp : ∀ j, 1 ≤ j → j < n → ‖p₁ j - p₂ j‖ ≤ δp) :
    ‖q₁.taylorComp p₁ n - q₂.taylorComp p₂ n‖ ≤
      ‖q₁ 1‖ * ‖p₁ n - p₂ n‖ + ‖q₁ 1 - q₂ 1‖ * ‖p₂ n‖ +
        (‖q₁ n‖ * n * max ‖p₁ 1‖ ‖p₂ 1‖ ^ (n - 1) * ‖p₁ 1 - p₂ 1‖ +
          ‖q₁ n - q₂ n‖ * ‖p₂ 1‖ ^ n) +
        Fintype.card (OrderedFinpartition n) * ((Mq * n * δp + δq) * max 1 Mp ^ n) := by
  rw [taylorComp_eq_add hn, taylorComp_eq_add hn]
  have hsplit : q₁.compAlongOrderedFinpartition p₁ (singleFinpartition n (by omega)) +
        q₁.compAlongOrderedFinpartition p₁ (OrderedFinpartition.atomic n) +
        taylorCompRemainder q₁ p₁ n -
      (q₂.compAlongOrderedFinpartition p₂ (singleFinpartition n (by omega)) +
        q₂.compAlongOrderedFinpartition p₂ (OrderedFinpartition.atomic n) +
        taylorCompRemainder q₂ p₂ n) =
      (q₁.compAlongOrderedFinpartition p₁ (singleFinpartition n (by omega)) -
          q₂.compAlongOrderedFinpartition p₂ (singleFinpartition n (by omega))) +
        (q₁.compAlongOrderedFinpartition p₁ (OrderedFinpartition.atomic n) -
          q₂.compAlongOrderedFinpartition p₂ (OrderedFinpartition.atomic n)) +
        (taylorCompRemainder q₁ p₁ n - taylorCompRemainder q₂ p₂ n) := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact norm_compAlongOrderedFinpartition_single_sub_le _
  · exact norm_compAlongOrderedFinpartition_atomic_sub_le (by omega)
  · exact norm_taylorCompRemainder_sub_le hMq hMp hδq hδp hq hdq hp₁ hp₂ hdp

end Series

/-! ### Iterated derivatives of compositions -/

section Composition

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : E → F} {g : F → G} {s : Set E} {t : Set F} {x y : E} {n : ℕ}

/-- The first iterated derivative within a set is the derivative within it. -/
theorem iteratedFDerivWithin_one_eq (h : UniqueDiffWithinAt ℝ s x) :
    iteratedFDerivWithin ℝ 1 f s x =
      (continuousMultilinearCurryFin1 ℝ E F).symm (fderivWithin ℝ f s x) := by
  ext m
  rw [iteratedFDerivWithin_one_apply h]
  simp

/-- Differences of first iterated derivatives are differences of derivatives. -/
theorem norm_iteratedFDerivWithin_one_sub (hx : UniqueDiffWithinAt ℝ s x)
    (hy : UniqueDiffWithinAt ℝ s y) :
    ‖iteratedFDerivWithin ℝ 1 f s x - iteratedFDerivWithin ℝ 1 f s y‖ =
      ‖fderivWithin ℝ f s x - fderivWithin ℝ f s y‖ := by
  rw [iteratedFDerivWithin_one_eq hx, iteratedFDerivWithin_one_eq hy, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]

/-- **The `n`-th derivative of a composition with the top-order terms separated.** For `n ≥ 2`,
`D^n (g ∘ f)(x) = D g(f x) ∘ D^n f(x) + D^n g(f x)[D f(x), …, D f(x)] + R`, where the remainder
`R = taylorCompRemainder` involves only derivatives of `g` of orders `2, …, n - 1` and of `f` of
orders `1, …, n - 1`. -/
theorem iteratedFDerivWithin_comp_eq_add (hg : ContDiffOn ℝ n g t) (hf : ContDiffOn ℝ n f s)
    (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s) (hst : MapsTo f s t) (hx : x ∈ s)
    (hn : 2 ≤ n) :
    iteratedFDerivWithin ℝ n (g ∘ f) s x =
      (fderivWithin ℝ g t (f x)).compContinuousMultilinearMap (iteratedFDerivWithin ℝ n f s x) +
        (iteratedFDerivWithin ℝ n g t (f x)).compContinuousLinearMap
          (fun _ ↦ fderivWithin ℝ f s x) +
        taylorCompRemainder (ftaylorSeriesWithin ℝ g t (f x)) (ftaylorSeriesWithin ℝ f s x) n := by
  rw [iteratedFDerivWithin_comp (hg.contDiffWithinAt (hst hx)) (hf.contDiffWithinAt hx) ht hs
    hx hst le_rfl, taylorComp_eq_add hn]
  congr 2
  · ext v
    change iteratedFDerivWithin ℝ 1 g t (f x) (fun _ ↦ iteratedFDerivWithin ℝ n f s x v) =
      fderivWithin ℝ g t (f x) (iteratedFDerivWithin ℝ n f s x v)
    rw [iteratedFDerivWithin_one_apply (ht _ (hst hx))]
  · ext v
    change iteratedFDerivWithin ℝ n g t (f x)
        (fun i ↦ iteratedFDerivWithin ℝ 1 f s x (fun _ ↦ v i)) =
      iteratedFDerivWithin ℝ n g t (f x) (fun i ↦ fderivWithin ℝ f s x (v i))
    congr 1
    funext i
    rw [iteratedFDerivWithin_one_apply (hs _ hx)]

/-- **Size of the `n`-th derivative of a composition, top-order terms separated.** For `n ≥ 2`,
`‖D^n (g ∘ f)(x)‖ ≤ ‖D g(f x)‖ ‖D^n f(x)‖ + ‖D^n g(f x)‖ ‖D f(x)‖ ^ n + (number of ordered
partitions) Mg max 1 Mf ^ n`, where `Mg` bounds the derivatives of `g` of orders `2, …, n - 1` at
`f x` and `Mf` those of `f` of orders `1, …, n - 1` at `x`. -/
theorem norm_iteratedFDerivWithin_comp_le_add (hg : ContDiffOn ℝ n g t)
    (hf : ContDiffOn ℝ n f s) (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s)
    (hst : MapsTo f s t) (hx : x ∈ s) (hn : 2 ≤ n) {Mg Mf : ℝ} (hMg : 0 ≤ Mg)
    (hgb : ∀ i, 2 ≤ i → i < n → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ Mg)
    (hfb : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j f s x‖ ≤ Mf) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x‖ ≤
      ‖fderivWithin ℝ g t (f x)‖ * ‖iteratedFDerivWithin ℝ n f s x‖ +
        ‖iteratedFDerivWithin ℝ n g t (f x)‖ * ‖fderivWithin ℝ f s x‖ ^ n +
        Fintype.card (OrderedFinpartition n) * (Mg * max 1 Mf ^ n) := by
  rw [iteratedFDerivWithin_comp (hg.contDiffWithinAt (hst hx)) (hf.contDiffWithinAt hx) ht hs
    hx hst le_rfl]
  have h := norm_taylorComp_le (q := ftaylorSeriesWithin ℝ g t (f x))
    (p := ftaylorSeriesWithin ℝ f s x) hn hMg hgb hfb
  simp only [ftaylorSeriesWithin] at h
  rwa [norm_iteratedFDerivWithin_one _ (ht _ (hst hx)),
    norm_iteratedFDerivWithin_one _ (hs _ hx)] at h

/-- **Difference at two points of the `n`-th derivative of a composition, top-order terms
separated.** The derivatives of order `n` of `f` and `g` enter only linearly, through the one-block
and the singleton terms; the lower orders through bounds `Mg, Mf` and differences `δg, δf`. -/
theorem norm_iteratedFDerivWithin_comp_sub_le_add (hg : ContDiffOn ℝ n g t)
    (hf : ContDiffOn ℝ n f s) (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s)
    (hst : MapsTo f s t) (hx : x ∈ s) (hy : y ∈ s) (hn : 2 ≤ n) {Mg Mf δg δf : ℝ}
    (hMg : 0 ≤ Mg) (hMf : 0 ≤ Mf) (hδg : 0 ≤ δg) (hδf : 0 ≤ δf)
    (hgb : ∀ i, 2 ≤ i → i < n → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ Mg)
    (hgd : ∀ i, 2 ≤ i → i < n →
      ‖iteratedFDerivWithin ℝ i g t (f x) - iteratedFDerivWithin ℝ i g t (f y)‖ ≤ δg)
    (hfx : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j f s x‖ ≤ Mf)
    (hfy : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j f s y‖ ≤ Mf)
    (hfd : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDerivWithin ℝ j f s x - iteratedFDerivWithin ℝ j f s y‖ ≤ δf) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x - iteratedFDerivWithin ℝ n (g ∘ f) s y‖ ≤
      ‖fderivWithin ℝ g t (f x)‖ *
          ‖iteratedFDerivWithin ℝ n f s x - iteratedFDerivWithin ℝ n f s y‖ +
        ‖fderivWithin ℝ g t (f x) - fderivWithin ℝ g t (f y)‖ * ‖iteratedFDerivWithin ℝ n f s y‖ +
        (‖iteratedFDerivWithin ℝ n g t (f x)‖ * n *
            max ‖fderivWithin ℝ f s x‖ ‖fderivWithin ℝ f s y‖ ^ (n - 1) *
            ‖fderivWithin ℝ f s x - fderivWithin ℝ f s y‖ +
          ‖iteratedFDerivWithin ℝ n g t (f x) - iteratedFDerivWithin ℝ n g t (f y)‖ *
            ‖fderivWithin ℝ f s y‖ ^ n) +
        Fintype.card (OrderedFinpartition n) * ((Mg * n * δf + δg) * max 1 Mf ^ n) := by
  rw [iteratedFDerivWithin_comp (hg.contDiffWithinAt (hst hx)) (hf.contDiffWithinAt hx) ht hs
    hx hst le_rfl, iteratedFDerivWithin_comp (hg.contDiffWithinAt (hst hy))
    (hf.contDiffWithinAt hy) ht hs hy hst le_rfl]
  have h := norm_taylorComp_sub_le (q₁ := ftaylorSeriesWithin ℝ g t (f x))
    (q₂ := ftaylorSeriesWithin ℝ g t (f y)) (p₁ := ftaylorSeriesWithin ℝ f s x)
    (p₂ := ftaylorSeriesWithin ℝ f s y) hn hMg hMf hδg hδf hgb hgd hfx hfy hfd
  simp only [ftaylorSeriesWithin] at h
  rwa [norm_iteratedFDerivWithin_one _ (ht _ (hst hx)), norm_iteratedFDerivWithin_one _ (hs _ hx),
    norm_iteratedFDerivWithin_one _ (hs _ hy),
    norm_iteratedFDerivWithin_one_sub (ht _ (hst hx)) (ht _ (hst hy)),
    norm_iteratedFDerivWithin_one_sub (hs _ hx) (hs _ hy)] at h

/-- **Hölder bound of the `n`-th derivative of a composition, linear in the top order.** If the
derivatives of `g` of orders `1, …, n - 1` are bounded by `Mg` and `α`-Hölder with constant `Hg` on
`t`, its `n`-th derivative is bounded by `Ng` and `α`-Hölder with constant `Kg`, the derivatives of
`f` of orders `1, …, n - 1` are bounded by `Mf` and `α`-Hölder with constant `Hf` on `s`, its `n`-th
derivative bounded by `Nf` and `α`-Hölder with constant `Kf`, and `f` is `Lf`-Lipschitz on `s`,
then the `n`-th derivative of `g ∘ f` is `α`-Hölder on `s` with a constant linear in
`Kf, Nf, Ng, Kg` whose coefficients depend only on the lower-order constants. -/
theorem norm_iteratedFDerivWithin_comp_sub_le_rpow (hg : ContDiffOn ℝ n g t)
    (hf : ContDiffOn ℝ n f s) (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s)
    (hst : MapsTo f s t) (hn : 2 ≤ n) {α : ℝ} (hα : 0 ≤ α)
    {Mg Hg Ng Kg Mf Hf Nf Kf Lf : ℝ} (hMg : 0 ≤ Mg) (hHg : 0 ≤ Hg) (hNg : 0 ≤ Ng)
    (hKg : 0 ≤ Kg) (hMf : 0 ≤ Mf) (hHf : 0 ≤ Hf) (hLf : 0 ≤ Lf)
    (hgM : ∀ i, 1 ≤ i → i < n → ∀ z ∈ t, ‖iteratedFDerivWithin ℝ i g t z‖ ≤ Mg)
    (hgH : ∀ i, 1 ≤ i → i < n → ∀ z ∈ t, ∀ z' ∈ t,
      ‖iteratedFDerivWithin ℝ i g t z - iteratedFDerivWithin ℝ i g t z'‖ ≤ Hg * ‖z - z'‖ ^ α)
    (hgN : ∀ z ∈ t, ‖iteratedFDerivWithin ℝ n g t z‖ ≤ Ng)
    (hgK : ∀ z ∈ t, ∀ z' ∈ t,
      ‖iteratedFDerivWithin ℝ n g t z - iteratedFDerivWithin ℝ n g t z'‖ ≤ Kg * ‖z - z'‖ ^ α)
    (hfM : ∀ j, 1 ≤ j → j < n → ∀ z ∈ s, ‖iteratedFDerivWithin ℝ j f s z‖ ≤ Mf)
    (hfH : ∀ j, 1 ≤ j → j < n → ∀ z ∈ s, ∀ z' ∈ s,
      ‖iteratedFDerivWithin ℝ j f s z - iteratedFDerivWithin ℝ j f s z'‖ ≤ Hf * ‖z - z'‖ ^ α)
    (hfN : ∀ z ∈ s, ‖iteratedFDerivWithin ℝ n f s z‖ ≤ Nf)
    (hfK : ∀ z ∈ s, ∀ z' ∈ s,
      ‖iteratedFDerivWithin ℝ n f s z - iteratedFDerivWithin ℝ n f s z'‖ ≤ Kf * ‖z - z'‖ ^ α)
    (hfL : ∀ z ∈ s, ∀ z' ∈ s, ‖f z - f z'‖ ≤ Lf * ‖z - z'‖) (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x - iteratedFDerivWithin ℝ n (g ∘ f) s y‖ ≤
      (Mg * Kf + Hg * Lf ^ α * Nf + (Ng * n * Mf ^ (n - 1) * Hf + Kg * Lf ^ α * Mf ^ n) +
        Fintype.card (OrderedFinpartition n) * ((Mg * n * Hf + Hg * Lf ^ α) * max 1 Mf ^ n)) *
        ‖x - y‖ ^ α := by
  set d := ‖x - y‖ ^ α
  have hd : 0 ≤ d := Real.rpow_nonneg (norm_nonneg _) _
  have hfxy : ‖f x - f y‖ ^ α ≤ Lf ^ α * d := by
    rw [← Real.mul_rpow hLf (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hfL x hx y hy) hα
  have hδg : 0 ≤ Hg * Lf ^ α * d := mul_nonneg (mul_nonneg hHg (Real.rpow_nonneg hLf _)) hd
  have hgd (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
      ‖iteratedFDerivWithin ℝ i g t (f x) - iteratedFDerivWithin ℝ i g t (f y)‖ ≤
        Hg * Lf ^ α * d :=
    (hgH i hi hin _ (hst hx) _ (hst hy)).trans (by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfxy hHg)
  have h := norm_iteratedFDerivWithin_comp_sub_le_add hg hf ht hs hst hx hy hn hMg hMf hδg
    (mul_nonneg hHf hd) (fun i hi hin ↦ hgM i (by omega) hin _ (hst hx))
    (fun i hi hin ↦ hgd i (by omega) hin) (fun j hj hjn ↦ hfM j hj hjn x hx)
    (fun j hj hjn ↦ hfM j hj hjn y hy) (fun j hj hjn ↦ hfH j hj hjn x hx y hy)
  have hux : UniqueDiffWithinAt ℝ t (f x) := ht _ (hst hx)
  have h1 : ‖fderivWithin ℝ g t (f x)‖ ≤ Mg := by
    rw [← norm_iteratedFDerivWithin_one _ hux]; exact hgM 1 le_rfl (by omega) _ (hst hx)
  have h2 : ‖fderivWithin ℝ g t (f x) - fderivWithin ℝ g t (f y)‖ ≤ Hg * Lf ^ α * d := by
    rw [← norm_iteratedFDerivWithin_one_sub hux (ht _ (hst hy))]; exact hgd 1 le_rfl (by omega)
  have h3 (z : E) (hz : z ∈ s) : ‖fderivWithin ℝ f s z‖ ≤ Mf := by
    rw [← norm_iteratedFDerivWithin_one _ (hs _ hz)]; exact hfM 1 le_rfl (by omega) z hz
  have h4 : ‖fderivWithin ℝ f s x - fderivWithin ℝ f s y‖ ≤ Hf * d := by
    rw [← norm_iteratedFDerivWithin_one_sub (hs _ hx) (hs _ hy)]
    exact hfH 1 le_rfl (by omega) x hx y hy
  have h5 : ‖iteratedFDerivWithin ℝ n g t (f x) - iteratedFDerivWithin ℝ n g t (f y)‖ ≤
      Kg * Lf ^ α * d := by
    refine (hgK _ (hst hx) _ (hst hy)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hfxy hKg
  have hmax : max ‖fderivWithin ℝ f s x‖ ‖fderivWithin ℝ f s y‖ ≤ Mf := max_le (h3 x hx) (h3 y hy)
  have hcard : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition n) := Nat.cast_nonneg _
  refine h.trans ?_
  have t1 : ‖fderivWithin ℝ g t (f x)‖ *
      ‖iteratedFDerivWithin ℝ n f s x - iteratedFDerivWithin ℝ n f s y‖ ≤ Mg * (Kf * d) :=
    mul_le_mul h1 (hfK x hx y hy) (norm_nonneg _) hMg
  have t2 : ‖fderivWithin ℝ g t (f x) - fderivWithin ℝ g t (f y)‖ *
      ‖iteratedFDerivWithin ℝ n f s y‖ ≤ Hg * Lf ^ α * d * Nf :=
    mul_le_mul h2 (hfN y hy) (norm_nonneg _) hδg
  have t3 : ‖iteratedFDerivWithin ℝ n g t (f x)‖ * n *
        max ‖fderivWithin ℝ f s x‖ ‖fderivWithin ℝ f s y‖ ^ (n - 1) *
        ‖fderivWithin ℝ f s x - fderivWithin ℝ f s y‖ ≤ Ng * n * Mf ^ (n - 1) * (Hf * d) := by
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (hgN _ (hst hx))
      (Nat.cast_nonneg _)) (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hmax _)
      (pow_nonneg (le_max_of_le_left (norm_nonneg _)) _) (mul_nonneg hNg (Nat.cast_nonneg _)))
      h4 (norm_nonneg _) (mul_nonneg (mul_nonneg hNg (Nat.cast_nonneg _)) (pow_nonneg hMf _))
  have t4 : ‖iteratedFDerivWithin ℝ n g t (f x) - iteratedFDerivWithin ℝ n g t (f y)‖ *
      ‖fderivWithin ℝ f s y‖ ^ n ≤ Kg * Lf ^ α * d * Mf ^ n :=
    mul_le_mul h5 (pow_le_pow_left₀ (norm_nonneg _) (h3 y hy) _) (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (mul_nonneg hKg (Real.rpow_nonneg hLf _)) hd)
  calc _ ≤ Mg * (Kf * d) + Hg * Lf ^ α * d * Nf +
        (Ng * n * Mf ^ (n - 1) * (Hf * d) + Kg * Lf ^ α * d * Mf ^ n) +
        Fintype.card (OrderedFinpartition n) *
          ((Mg * n * (Hf * d) + Hg * Lf ^ α * d) * max 1 Mf ^ n) := by
        gcongr
    _ = _ := by ring

end Composition

/-! ### Leibniz differences for bilinear maps -/

section Bilinear

/-- Differences of iterated derivatives of order `0` are differences of values. -/
theorem norm_iteratedFDerivWithin_zero_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E) (x y : E) :
    ‖iteratedFDerivWithin ℝ 0 f s x - iteratedFDerivWithin ℝ 0 f s y‖ = ‖f x - f y‖ := by
  rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, Function.comp_apply,
    ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

/-- Differences of iterated derivatives of the derivative are differences of iterated
derivatives of one order more. -/
theorem norm_iteratedFDerivWithin_fderivWithin_sub {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} {x y : E}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hy : y ∈ s) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fderivWithin ℝ f s) s x -
        iteratedFDerivWithin ℝ n (fderivWithin ℝ f s) s y‖ =
      ‖iteratedFDerivWithin ℝ (n + 1) f s x - iteratedFDerivWithin ℝ (n + 1) f s y‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, iteratedFDerivWithin_succ_eq_comp_right hs hy,
    Function.comp_apply, Function.comp_apply, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]

/-- The derivatives within `s` of the derivatives of order `n` of two functions differ, at two
points, by as much as their derivatives of order `n + 1` within `s`. -/
theorem norm_fderivWithin_iteratedFDerivWithin_sub {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : E → F) (s : Set E) (n : ℕ)
    (x y : E) :
    ‖fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x -
        fderivWithin ℝ (iteratedFDerivWithin ℝ n g s) s y‖ =
      ‖iteratedFDerivWithin ℝ (n + 1) f s x - iteratedFDerivWithin ℝ (n + 1) g s y‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_succ_eq_comp_left,
    Function.comp_apply, Function.comp_apply, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]

universe u

variable {D E F G : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- **Leibniz differences.** For a bounded bilinear map `B`, the difference at two points of the
`n`-th derivative of `B (f ·) (g ·)` within `s` is at most
`‖B‖ ∑ᵢ C(n, i) (‖Dⁱf(x) - Dⁱf(y)‖ ‖Dⁿ⁻ⁱg(x)‖ + ‖Dⁱf(y)‖ ‖Dⁿ⁻ⁱg(x) - Dⁿ⁻ⁱg(y)‖)`. The terms
`i = 0` and `i = n` contain the derivatives of order `n` of `f` and `g`, linearly. The spaces
are in one universe, which is the case in the applications. -/
theorem norm_iteratedFDerivWithin_bilinear_sub_le (B : E →L[ℝ] F →L[ℝ] G) {f : D → E}
    {g : D → F} {n : ℕ} {s : Set D} {x y : D} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ n (fun z ↦ B (f z) (g z)) s x -
        iteratedFDerivWithin ℝ n (fun z ↦ B (f z) (g z)) s y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDerivWithin ℝ i f s x - iteratedFDerivWithin ℝ i f s y‖ *
            ‖iteratedFDerivWithin ℝ (n - i) g s x‖ +
          ‖iteratedFDerivWithin ℝ i f s y‖ *
            ‖iteratedFDerivWithin ℝ (n - i) g s x - iteratedFDerivWithin ℝ (n - i) g s y‖) := by
  induction n generalizing E F G with
  | zero =>
    simp only [norm_iteratedFDerivWithin_zero_sub, norm_iteratedFDerivWithin_zero, zero_add,
      Finset.range_one, Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.sub_zero]
    have hsplit : B (f x) (g x) - B (f y) (g y) = B (f x - f y) (g x) + B (f y) (g x - g y) := by
      simp only [map_sub, sub_apply]
      abel
    rw [hsplit, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
      (rw [← mul_assoc]; exact B.le_opNorm₂ _ _)
  | succ n IH =>
    have In : ((n : ℕ) : WithTop ℕ∞) + 1 ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
      simp only [Nat.cast_succ, le_refl]
    set F₁ : D → D →L[ℝ] G := fun z ↦ B.precompR D (f z) (fderivWithin ℝ g s z)
    set F₂ : D → D →L[ℝ] G := fun z ↦ B.precompL D (fderivWithin ℝ f s z) (g z)
    have hA : ContDiffOn ℝ n F₁ s :=
      (B.precompR D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
    have hA' : ContDiffOn ℝ n F₂ s :=
      (B.precompL D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
        (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
    have J (z : D) (hz : z ∈ s) : iteratedFDerivWithin ℝ n
        (fun y : D ↦ fderivWithin ℝ (fun y : D ↦ B (f y) (g y)) s y) s z =
          iteratedFDerivWithin ℝ n F₁ s z + iteratedFDerivWithin ℝ n F₂ s z := by
      rw [iteratedFDerivWithin_congr (fun y hy ↦ B.fderivWithin_of_bilinear
        (hf.differentiableOn (by positivity) y hy) (hg.differentiableOn (by positivity) y hy)
        (hs y hy)) hz]
      exact iteratedFDerivWithin_add_apply (hA.contDiffWithinAt hz) (hA'.contDiffWithinAt hz)
        hs hz
    rw [← norm_iteratedFDerivWithin_fderivWithin_sub hs hx hy, J x hx, J y hy]
    have hsub : iteratedFDerivWithin ℝ n F₁ s x + iteratedFDerivWithin ℝ n F₂ s x -
        (iteratedFDerivWithin ℝ n F₁ s y + iteratedFDerivWithin ℝ n F₂ s y) =
        (iteratedFDerivWithin ℝ n F₁ s x - iteratedFDerivWithin ℝ n F₁ s y) +
          (iteratedFDerivWithin ℝ n F₂ s x - iteratedFDerivWithin ℝ n F₂ s y) := by abel
    rw [hsub]
    have I1 := IH (B.precompR D) (hf.of_le (Nat.cast_le.2 (Nat.le_succ n)))
      (hg.fderivWithin hs In)
    have I2 := IH (B.precompL D) (hf.fderivWithin hs In)
      (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
    have e1 (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
        ‖iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ g s) s x‖ =
          ‖iteratedFDerivWithin ℝ (n + 1 - i) g s x‖ := by
      rw [norm_iteratedFDerivWithin_fderivWithin hs hx,
        Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
    have e2 (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
        ‖iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ g s) s x -
            iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ g s) s y‖ =
          ‖iteratedFDerivWithin ℝ (n + 1 - i) g s x -
            iteratedFDerivWithin ℝ (n + 1 - i) g s y‖ := by
      rw [norm_iteratedFDerivWithin_fderivWithin_sub hs hx hy,
        Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
    have e3 (i : ℕ) : ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f s) s y‖ =
        ‖iteratedFDerivWithin ℝ (i + 1) f s y‖ := norm_iteratedFDerivWithin_fderivWithin hs hy
    have e4 (i : ℕ) : ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f s) s x -
        iteratedFDerivWithin ℝ i (fderivWithin ℝ f s) s y‖ =
        ‖iteratedFDerivWithin ℝ (i + 1) f s x - iteratedFDerivWithin ℝ (i + 1) f s y‖ :=
      norm_iteratedFDerivWithin_fderivWithin_sub hs hx hy i
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [e1 i hi, e2 i hi]] at I1
    rw [Finset.sum_congr rfl fun i _ ↦ by rw [e3 i, e4 i]] at I2
    set Φ : ℕ → ℕ → ℝ := fun i j ↦
      ‖iteratedFDerivWithin ℝ i f s x - iteratedFDerivWithin ℝ i f s y‖ *
          ‖iteratedFDerivWithin ℝ j g s x‖ +
        ‖iteratedFDerivWithin ℝ i f s y‖ *
          ‖iteratedFDerivWithin ℝ j g s x - iteratedFDerivWithin ℝ j g s y‖ with hΦ
    have hΦ0 (i j : ℕ) : 0 ≤ Φ i j := by positivity
    have hP := Finset.sum_choose_succ_mul (R := ℝ) Φ n
    have hS1 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Φ i (n + 1 - i) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hΦ0 _ _)
    have hS2 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Φ (i + 1) (n - i) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hΦ0 _ _)
    calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add I1 I2)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Φ i (n + 1 - i) +
          ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Φ (i + 1) (n - i) :=
          add_le_add (mul_le_mul_of_nonneg_right (B.norm_precompR_le D) hS1)
            (mul_le_mul_of_nonneg_right (B.norm_precompL_le D) hS2)
      _ = ‖B‖ * ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * Φ i (n + 1 - i) := by
          rw [hP, mul_add]

omit [NormedSpace ℝ D] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- A binomial sum with its two extreme terms separated: if the terms of index `0 < i < n` are at
most `M ≥ 0`, then `∑ᵢ C(n, i) aᵢ ≤ a₀ + aₙ + 2ⁿ M`. -/
theorem sum_range_choose_mul_le {n : ℕ} (hn : 1 ≤ n) {a : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, 0 < i → i < n → a i ≤ M) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i ≤ a 0 + a n + 2 ^ n * M := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.choose_self, Nat.choose_zero_right]
  have hmid : ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1) : ℝ) * a (i + 1) ≤
      ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1) : ℝ) * M :=
    Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
      (ha _ (Nat.succ_pos i) (by have := Finset.mem_range.1 hi; omega)) (Nat.cast_nonneg _)
  have hchoose : ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1) : ℝ) ≤ 2 ^ (m + 1) := by
    have htot : ∑ i ∈ Finset.range (m + 1 + 1), ((m + 1).choose i : ℝ) = 2 ^ (m + 1) := by
      exact_mod_cast Nat.sum_range_choose (m + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.choose_self,
      Nat.choose_zero_right] at htot
    linarith
  rw [← Finset.sum_mul] at hmid
  have := mul_le_mul_of_nonneg_right hchoose hM
  push_cast
  linarith

/-- **Leibniz bound with the top-order terms separated.** For `n ≥ 1`, if the derivatives of
orders `1, …, n - 1` of `f` and `g` at `x` are at most `Mf` and `Mg`,
`‖Dⁿ B(f, g)(x)‖ ≤ ‖B‖ (‖f x‖ ‖Dⁿg(x)‖ + ‖Dⁿf(x)‖ ‖g x‖ + 2ⁿ Mf Mg)`. -/
theorem norm_iteratedFDerivWithin_bilinear_le_add (B : E →L[ℝ] F →L[ℝ] G) {f : D → E}
    {g : D → F} {n : ℕ} {s : Set D} {x : D} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hn : 1 ≤ n) {Mf Mg : ℝ} (hMf : 0 ≤ Mf)
    (hMg : 0 ≤ Mg) (hfb : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j f s x‖ ≤ Mf)
    (hgb : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j g s x‖ ≤ Mg) :
    ‖iteratedFDerivWithin ℝ n (fun z ↦ B (f z) (g z)) s x‖ ≤
      ‖B‖ * (‖f x‖ * ‖iteratedFDerivWithin ℝ n g s x‖ +
        ‖iteratedFDerivWithin ℝ n f s x‖ * ‖g x‖ + 2 ^ n * (Mf * Mg)) := by
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hs hx le_rfl).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg B)
  have h := sum_range_choose_mul_le (a := fun i ↦ ‖iteratedFDerivWithin ℝ i f s x‖ *
      ‖iteratedFDerivWithin ℝ (n - i) g s x‖) hn (mul_nonneg hMf hMg) fun i hi hin ↦
    mul_le_mul (hfb i hi hin) (hgb (n - i) (by omega) (by omega)) (norm_nonneg _) hMf
  simp only [norm_iteratedFDerivWithin_zero, Nat.sub_zero] at h
  rw [Nat.sub_self, norm_iteratedFDerivWithin_zero] at h
  refine le_of_eq_of_le ?_ h
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Leibniz differences with the top-order terms separated.** For `n ≥ 1`, with the derivatives
of orders `1, …, n - 1` bounded (`Mf` at `y`, `Mg` at `x`) and their differences bounded (`δf`,
`δg`), the difference at two points of `Dⁿ B(f, g)` is at most
`‖B‖ ((‖f x - f y‖ ‖Dⁿg(x)‖ + ‖f y‖ ‖Dⁿg(x) - Dⁿg(y)‖) +
(‖Dⁿf(x) - Dⁿf(y)‖ ‖g x‖ + ‖Dⁿf(y)‖ ‖g x - g y‖) + 2ⁿ (δf Mg + Mf δg))`. -/
theorem norm_iteratedFDerivWithin_bilinear_sub_le_add (B : E →L[ℝ] F →L[ℝ] G) {f : D → E}
    {g : D → F} {n : ℕ} {s : Set D} {x y : D} (hf : ContDiffOn ℝ n f s)
    (hg : ContDiffOn ℝ n g s) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hy : y ∈ s) (hn : 1 ≤ n)
    {Mf Mg δf δg : ℝ} (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg) (hδf : 0 ≤ δf) (hδg : 0 ≤ δg)
    (hfy : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j f s y‖ ≤ Mf)
    (hgx : ∀ j, 1 ≤ j → j < n → ‖iteratedFDerivWithin ℝ j g s x‖ ≤ Mg)
    (hfd : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDerivWithin ℝ j f s x - iteratedFDerivWithin ℝ j f s y‖ ≤ δf)
    (hgd : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDerivWithin ℝ j g s x - iteratedFDerivWithin ℝ j g s y‖ ≤ δg) :
    ‖iteratedFDerivWithin ℝ n (fun z ↦ B (f z) (g z)) s x -
        iteratedFDerivWithin ℝ n (fun z ↦ B (f z) (g z)) s y‖ ≤
      ‖B‖ * ((‖f x - f y‖ * ‖iteratedFDerivWithin ℝ n g s x‖ +
          ‖f y‖ * ‖iteratedFDerivWithin ℝ n g s x - iteratedFDerivWithin ℝ n g s y‖) +
        (‖iteratedFDerivWithin ℝ n f s x - iteratedFDerivWithin ℝ n f s y‖ * ‖g x‖ +
          ‖iteratedFDerivWithin ℝ n f s y‖ * ‖g x - g y‖) +
        2 ^ n * (δf * Mg + Mf * δg)) := by
  refine (norm_iteratedFDerivWithin_bilinear_sub_le B hf hg hs hx hy).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg B)
  have h := sum_range_choose_mul_le (a := fun i ↦
      ‖iteratedFDerivWithin ℝ i f s x - iteratedFDerivWithin ℝ i f s y‖ *
          ‖iteratedFDerivWithin ℝ (n - i) g s x‖ +
        ‖iteratedFDerivWithin ℝ i f s y‖ *
          ‖iteratedFDerivWithin ℝ (n - i) g s x - iteratedFDerivWithin ℝ (n - i) g s y‖) hn
    (by positivity) fun i hi hin ↦
    add_le_add (mul_le_mul (hfd i hi hin) (hgx (n - i) (by omega) (by omega)) (norm_nonneg _)
      hδf) (mul_le_mul (hfy i hi hin) (hgd (n - i) (by omega) (by omega)) (norm_nonneg _) hMf)
  simp only [norm_iteratedFDerivWithin_zero, norm_iteratedFDerivWithin_zero_sub, Nat.sub_zero] at h
  rwa [Nat.sub_self, norm_iteratedFDerivWithin_zero, norm_iteratedFDerivWithin_zero_sub] at h

end Bilinear

/-! ### On the closed upper half-plane -/

section HalfPlane

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ^2 → F} {f : ℝ^2 → ℝ^2}
  {n : ℕ} {x y : ℝ^2}

/-- **Hölder bound of the `n`-th derivative of a composition on the closed upper half-plane**,
linear in the top-order constants: the case `s = t = {y | 0 ≤ y 1}` of
`norm_iteratedFDerivWithin_comp_sub_le_rpow`, for a map `f` of the closed half-plane into
itself. -/
theorem norm_iteratedFDerivWithin_comp_sub_le_rpow_of_closedUpper
    (hg : ContDiffOn ℝ n g {y | 0 ≤ y 1}) (hf : ContDiffOn ℝ n f {y | 0 ≤ y 1})
    (hmaps : MapsTo f {y | 0 ≤ y 1} {y | 0 ≤ y 1}) (hn : 2 ≤ n) {α : ℝ} (hα : 0 ≤ α)
    {Mg Hg Ng Kg Mf Hf Nf Kf Lf : ℝ} (hMg : 0 ≤ Mg) (hHg : 0 ≤ Hg) (hNg : 0 ≤ Ng)
    (hKg : 0 ≤ Kg) (hMf : 0 ≤ Mf) (hHf : 0 ≤ Hf) (hLf : 0 ≤ Lf)
    (hgM : ∀ i, 1 ≤ i → i < n → ∀ z : ℝ^2, 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ i g {y | 0 ≤ y 1} z‖ ≤ Mg)
    (hgH : ∀ i, 1 ≤ i → i < n → ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDerivWithin ℝ i g {y | 0 ≤ y 1} z - iteratedFDerivWithin ℝ i g {y | 0 ≤ y 1} z'‖ ≤
        Hg * ‖z - z'‖ ^ α)
    (hgN : ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDerivWithin ℝ n g {y | 0 ≤ y 1} z‖ ≤ Ng)
    (hgK : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDerivWithin ℝ n g {y | 0 ≤ y 1} z - iteratedFDerivWithin ℝ n g {y | 0 ≤ y 1} z'‖ ≤
        Kg * ‖z - z'‖ ^ α)
    (hfM : ∀ j, 1 ≤ j → j < n → ∀ z : ℝ^2, 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ j f {y | 0 ≤ y 1} z‖ ≤ Mf)
    (hfH : ∀ j, 1 ≤ j → j < n → ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDerivWithin ℝ j f {y | 0 ≤ y 1} z - iteratedFDerivWithin ℝ j f {y | 0 ≤ y 1} z'‖ ≤
        Hf * ‖z - z'‖ ^ α)
    (hfN : ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDerivWithin ℝ n f {y | 0 ≤ y 1} z‖ ≤ Nf)
    (hfK : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDerivWithin ℝ n f {y | 0 ≤ y 1} z - iteratedFDerivWithin ℝ n f {y | 0 ≤ y 1} z'‖ ≤
        Kf * ‖z - z'‖ ^ α)
    (hfL : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 → ‖f z - f z'‖ ≤ Lf * ‖z - z'‖)
    (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) {y | 0 ≤ y 1} x -
        iteratedFDerivWithin ℝ n (g ∘ f) {y | 0 ≤ y 1} y‖ ≤
      (Mg * Kf + Hg * Lf ^ α * Nf + (Ng * n * Mf ^ (n - 1) * Hf + Kg * Lf ^ α * Mf ^ n) +
        Fintype.card (OrderedFinpartition n) * ((Mg * n * Hf + Hg * Lf ^ α) * max 1 Mf ^ n)) *
        ‖x - y‖ ^ α :=
  norm_iteratedFDerivWithin_comp_sub_le_rpow hg hf (uniqueDiffOn_coordinateHalfSpace 1)
    (uniqueDiffOn_coordinateHalfSpace 1) hmaps hn hα hMg hHg hNg hKg hMf hHf hLf
    (fun i hi hin z hz ↦ hgM i hi hin z hz) (fun i hi hin z hz z' hz' ↦ hgH i hi hin z z' hz hz')
    (fun z hz ↦ hgN z hz) (fun z hz z' hz' ↦ hgK z z' hz hz')
    (fun j hj hjn z hz ↦ hfM j hj hjn z hz) (fun j hj hjn z hz z' hz' ↦ hfH j hj hjn z z' hz hz')
    (fun z hz ↦ hfN z hz) (fun z hz z' hz' ↦ hfK z z' hz hz') (fun z hz z' hz' ↦ hfL z z' hz hz')
    hx hy

end HalfPlane

end PDE.Analysis
