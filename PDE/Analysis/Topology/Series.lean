/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import PDE.Analysis.ENNReal.Basic
public import PDE.Analysis.Order.MinMax
public import PDE.Analysis.Scalar.Powers

set_option linter.style.header false

/-!
# Summable families and infinite sums

The lemmas state summability by comparison, exchange an infinite sum with a finite sum or a constant
factor, and bound an infinite sum term by term. The proofs use `Summable.of_nonneg_of_le`,
`tsum_le_tsum` and `HasSum` with the lemmas of Mathlib on `tsum`.

## Main results

* `PDE.Analysis.tsum_ofReal_mul_sum_shift_le`: For `p g : ℤ × ℤ → ℝ` and a finite set `s` of shifts,
  `∑' ι, ofReal (p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α))) ≤ s.card * (∑' ι, ofReal (p ι ^ 2) + 2 * ∑'
  ι, ofReal (g ι ^ 2))` in `ℝ≥0∞`.
* `PDE.Analysis.summable_mul_sq_of_abs_le`: If `|f ι| ≤ K` for all `ι : ℤ × ℤ` and `ι ↦ p ι ^ 2` is
  summable, then `ι ↦ f ι * p ι ^ 2` is summable.
* `PDE.Analysis.tsum_ofReal_abs_ite_sub_ite_eq`: For real `a` and `b`, `∑' ι : ℤ × ℤ, ENNReal.ofReal
  |(if ι = 0 then a else 0) - (if ι = 0 then b else 0)| = ENNReal.ofReal |a - b|`: only the index
  `0` contributes to the sum.
* `PDE.Analysis.le_tsum_ite_of_add_sum_le`: Let `f : ℕ × ℕ → ℝ` be nonnegative with sum `S`, and let
  `A` be a decidable predicate. If `X + ∑ u ∈ U, f u ≤ S` for every finite set `U` of indices that
  do not satisfy `A`, then `X ≤ ∑' i, if A i then f i else 0`.
* `PDE.Analysis.summable_ite_lt_max_of_summable`: If `T : ℕ → ℕ → ℝ` is such that `jl ↦ T jl.1 jl.2`
  is summable over `ℕ × ℕ`, then for every `d : ℕ` the family
  `jl ↦ if d < max jl.1 jl.2 then T jl.1 jl.2 else 0` is summable.
* `PDE.Analysis.summable_of_abs_le_mul_add_finite`: Let `F g l : ℤ → ℝ` with `g` summable and
  `l n = 0` for all `n` outside a finite set `T`. If `|F n| ≤ A * (g n + l n)` for all `n`, with `A`
  a real constant, then `F` is summable.
* `PDE.Analysis.tendsto_tsum_of_tsum_abs_sub_le`: Convergence in `ℓ¹` gives convergence of the sums:
  let `a n : ℤ × ℤ → ℝ` and `c` be summable, and let each `ι ↦ |a n ι - c ι|` be summable with
  `∑' ι, |a n ι - c ι| ≤ g n`. If `g n → 0`, then `∑' ι, a n ι → ∑' ι, c ι`.
* `PDE.Analysis.tsum_eq_toReal_ofReal`: For a nonnegative `f : ℤ × ℤ → ℝ`, the real sum is the
  `toReal` of the sum computed in `ℝ≥0∞`: `∑' ι, f ι = (∑' ι, ENNReal.ofReal (f ι)).toReal`.
  Summability of `f` is not assumed.

There are 41 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Filter Topology Real
open scoped ENNReal

namespace PDE.Analysis

/-- Reverse triangle inequality for the `ℓ²` norm on `ℤ × ℤ`: if `i ↦ f i ^ 2` and `i ↦ g i ^ 2` are
summable, then `|√(∑' i, f i ^ 2) - √(∑' i, g i ^ 2)| ≤ √(∑' i, (f i - g i) ^ 2)`. The proof regards
`f` and `g` as elements of `lp (fun _ ↦ ℝ) 2` and applies `abs_norm_sub_norm_le`. -/
theorem abs_sqrt_tsum_sq_sub_le {f g : ℤ × ℤ → ℝ} (hf : Summable fun i ↦ f i ^ 2)
    (hg : Summable fun i ↦ g i ^ 2) :
    |Real.sqrt (∑' i, f i ^ 2) - Real.sqrt (∑' i, g i ^ 2)| ≤ Real.sqrt (∑' i, (f i - g i) ^ 2) :=
        by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have mem : ∀ {a : ℤ × ℤ → ℝ}, Summable (fun i ↦ a i ^ 2) → Memℓp a 2 := fun {a} ha ↦ by
    refine (memℓp_gen_iff hp).2 ?_
    simpa [Real.norm_eq_abs, sq_abs] using ha
  have nrm : ∀ (a : ℤ × ℤ → ℝ) (ha : Summable (fun i ↦ a i ^ 2)),
      ‖(⟨a, mem ha⟩ : lp (fun _ : ℤ × ℤ ↦ ℝ) 2)‖ = Real.sqrt (∑' i, a i ^ 2) := fun a ha ↦ by
    rw [lp.norm_eq_tsum_rpow hp, Real.sqrt_eq_rpow]
    simp [Real.norm_eq_abs, sq_abs]
  have hfg : Summable (fun i ↦ (f i - g i) ^ 2) := by
    have := (mem hf).sub (mem hg)
    have h2 := (memℓp_gen_iff hp).1 this
    simpa [Real.norm_eq_abs, sq_abs] using h2
  have e := abs_norm_sub_norm_le (⟨f, mem hf⟩ : lp (fun _ : ℤ × ℤ ↦ ℝ) 2) ⟨g, mem hg⟩
  rw [nrm f hf, nrm g hg] at e
  have e2 : (⟨f, mem hf⟩ : lp (fun _ : ℤ × ℤ ↦ ℝ) 2) - ⟨g, mem hg⟩ =
      ⟨fun i ↦ f i - g i, mem hfg⟩ := by
    ext i
    simp
    rfl
  rw [e2, nrm _ hfg] at e
  exact e

/-- For a finite set `s` of integers and `f : ℤ → ℝ`,
`∑ n ∈ s, f n = ∑' n, (if n ∈ s then f n else 0)`. -/
theorem finset_sum_eq_tsum_ite_mem (s : Finset ℤ) (f : ℤ → ℝ) :
    ∑ n ∈ s, f n = ∑' n, (if n ∈ s then f n else 0) := by
  classical
  rw [tsum_eq_sum (s := s) (fun n hn ↦ by simp [hn])]
  exact Finset.sum_congr rfl (fun n hn ↦ by simp [hn])

/-- If for all indices `i l x y z : Fin 3` the family `f i l x y z : ℤ → ℂ` has sum `a i l x y z`,
then `n ↦ ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, f i l x y z n` has sum `∑ i, ∑ l, ∑ x, ∑ y, ∑ z, a i l x y z`. -/
theorem hasSum_fivefold_sum_fin_three {f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℤ → ℂ}
    {a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ}
    (h : ∀ i l x y z, HasSum (f i l x y z) (a i l x y z)) :
    HasSum (fun n ↦ ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, f i l x y z n)
        (∑ i, ∑ l, ∑ x, ∑ y, ∑ z, a i l x y z) :=
  hasSum_sum fun i _ ↦ hasSum_sum fun l _ ↦ hasSum_sum fun x _ ↦ hasSum_sum fun y _ ↦
    hasSum_sum fun z _ ↦ h i l x y z

/-- If `a : ℤ × ℤ → ℝ` is nonnegative, `0 ≤ c` and `∑' ι, ENNReal.ofReal (a ι) = ENNReal.ofReal c`,
then `a` has sum `c`. The sum in `ℝ≥0∞` is finite, so `a` is summable, and `ofReal` of its sum
equals `ofReal c`. -/
theorem hasSum_of_tsum_ofReal_eq_ofReal {a : ℤ × ℤ → ℝ} {c : ℝ} (ha : ∀ ι, 0 ≤ a ι) (hc : 0 ≤ c)
    (h : ∑' ι, ENNReal.ofReal (a ι) = ENNReal.ofReal c) : HasSum a c := by
  have hne : ∑' ι, ENNReal.ofReal (a ι) ≠ ⊤ := by
    rw [h]
    exact ENNReal.ofReal_ne_top
  have hs : Summable a :=
    (ENNReal.summable_toReal hne).congr (fun ι ↦ ENNReal.toReal_ofReal (ha ι))
  have hv : ∑' ι, a ι = c := by
    have e := ENNReal.ofReal_tsum_of_nonneg ha hs
    rw [h] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha) hc).1 e
  rw [← hv]
  exact hs.hasSum

/-- Let `f : ℕ × ℕ → ℝ` be nonnegative with sum `S`, and let `A` be a decidable predicate. If
`X + ∑ u ∈ U, f u ≤ S` for every finite set `U` of indices that do not satisfy `A`, then
`X ≤ ∑' i, if A i then f i else 0`. Proof idea: `S` is the sum of the series over `A` and of the
series over its complement, and the latter is at most `S - X`. -/
theorem le_tsum_ite_of_add_sum_le (f : ℕ × ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (S : ℝ) (hS : HasSum f S)
    (A : ℕ × ℕ → Prop)
    [DecidablePred A] (X : ℝ) (h : ∀ U : Finset (ℕ × ℕ), (∀ u ∈ U, ¬ A u) → X + ∑ u ∈ U, f u ≤ S) :
    X ≤ ∑' i, if A i then f i else 0 := by
  have hs1 : Summable (fun i ↦ if A i then f i else 0) :=
    Summable.of_nonneg_of_le (fun i ↦ by split_ifs; exacts [hf0 i, le_rfl])
      (fun i ↦ by split_ifs; exacts [le_rfl, hf0 i]) hS.summable
  have hs2 : Summable (fun i ↦ if A i then 0 else f i) :=
    Summable.of_nonneg_of_le (fun i ↦ by split_ifs; exacts [le_rfl, hf0 i])
      (fun i ↦ by split_ifs; exacts [hf0 i, le_rfl]) hS.summable
  have hsum : (∑' i, if A i then f i else 0) + (∑' i, if A i then 0 else f i) = S := by
    rw [← hs1.tsum_add hs2, ← hS.tsum_eq]
    congr 1; funext i; split_ifs <;> simp
  have hle : (∑' i, if A i then 0 else f i) ≤ S - X := by
    refine hs2.tsum_le_of_sum_le fun U ↦ ?_
    have h1 := h (U.filter fun u ↦ ¬ A u) (fun u hu ↦ (Finset.mem_filter.1 hu).2)
    rw [Finset.sum_filter] at h1
    have e : ∑ i ∈ U, (if A i then 0 else f i) = ∑ i ∈ U, (if ¬ A i then f i else 0) :=
      Finset.sum_congr rfl fun i _ ↦ by by_cases hA : A i <;> simp [hA]
    linarith
  linarith

/-- If `Q : ℤ × ℤ → ℝ` is summable, `X ≤ 2 * π * ∑' ι, Q ι` and `Q ι ≤ c ι` for all `ι`, then
`ENNReal.ofReal X ≤ ENNReal.ofReal (2 * π) * ∑' ι, ENNReal.ofReal (c ι)`. The proof bounds
`ofReal (∑' ι, Q ι)` by the sum of `ofReal (max (Q ι) 0)` and compares it term by term with
`ofReal (c ι)`. -/
theorem ofReal_le_of_tsum_le {X : ℝ} {Q c : ℤ × ℤ → ℝ} (hQ : Summable Q)
    (hX : X ≤ 2 * Real.pi * ∑' ι, Q ι) (hle : ∀ ι, Q ι ≤ c ι) :
    ENNReal.ofReal X ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι, ENNReal.ofReal (c ι) := by
  have hQp : Summable (fun ι ↦ max (Q ι) 0) :=
    hQ.abs.of_nonneg_of_le (fun _ ↦ le_max_right _ _) (fun ι ↦
        max_le (le_abs_self _) (abs_nonneg _))
  have hs : ENNReal.ofReal (∑' ι, Q ι) ≤ ∑' ι, ENNReal.ofReal (c ι) := by
    calc ENNReal.ofReal (∑' ι, Q ι) ≤ ENNReal.ofReal (∑' ι, max (Q ι) 0) :=
          ENNReal.ofReal_le_ofReal (Summable.tsum_le_tsum (fun ι ↦ le_max_left _ _) hQ hQp)
      _ = ∑' ι, ENNReal.ofReal (max (Q ι) 0) :=
          ENNReal.ofReal_tsum_of_nonneg (fun ι ↦ le_max_right _ _) hQp
      _ ≤ ∑' ι, ENNReal.ofReal (c ι) := by
          refine tsum_le_tsum (fun ι ↦ ?_)
          rcases le_total (Q ι) 0 with h | h
          · rw [max_eq_right h, ENNReal.ofReal_zero]
            exact bot_le
          · rw [max_eq_left h]
            exact ENNReal.ofReal_le_ofReal (hle ι)
  calc ENNReal.ofReal X ≤ ENNReal.ofReal (2 * Real.pi * ∑' ι, Q ι) := ENNReal.ofReal_le_ofReal hX
    _ = ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (∑' ι, Q ι) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι, ENNReal.ofReal (c ι) := by gcongr

/-- Let `f` and `charge` be summable real families on `ℤ × ℤ`, `res` a finite set of indices and `r`
a real number. If `r * f ι ≤ leaf ι` for `ι ∈ res`, `(if ι ∈ res then 0 else r * f ι) ≤ charge ι`
for all `ι`, and `-(r * ∑' ι, f ι) ≤ ∑' ι, st ι`, then
`0 ≤ ∑ ι ∈ res, leaf ι + ∑' ι, charge ι + ∑' ι, st ι`. The proof splits `∑' ι, f ι` into the finite
sum over `res` and the sum over the complement, and adds the three bounds. -/
theorem sum_add_tsum_add_tsum_nonneg (res : Finset (ℤ × ℤ)) (f leaf charge st : ℤ × ℤ → ℝ) (r : ℝ)
    (hf : Summable f)
    (hcs : Summable charge) (hleaf : ∀ ι ∈ res, r * f ι ≤ leaf ι)
    (hcharge : ∀ ι, (if ι ∈ res then 0 else r * f ι) ≤ charge ι)
        (hst : -(r * ∑' ι, f ι) ≤ ∑' ι, st ι) :
    0 ≤ ∑ ι ∈ res, leaf ι + ∑' ι, charge ι + ∑' ι, st ι := by
  classical
  have habs : Summable fun ι ↦ |f ι| := summable_abs_iff.mpr hf
  have hin : Summable fun ι ↦ if ι ∈ res then f ι else 0 :=
    Summable.of_norm_bounded habs fun ι ↦ by split_ifs <;> simp
  have hout : Summable fun ι ↦ if ι ∈ res then 0 else f ι :=
    Summable.of_norm_bounded habs fun ι ↦ by split_ifs <;> simp
  have hsplit : ∑' ι, f ι = ∑ ι ∈ res, f ι + ∑' ι, (if ι ∈ res then 0 else f ι) := by
    have e : ∀ ι, f ι = (if ι ∈ res then f ι else 0) + (if ι ∈ res then 0 else f ι) := by
      intro ι; split_ifs <;> simp
    rw [tsum_congr e, hin.tsum_add hout, tsum_eq_sum (s := res)]
    · refine congrArg (· + _) (Finset.sum_congr rfl fun ι hι ↦ ?_)
      simp [hι]
    · intro ι hι; simp [hι]
  have h1 : r * ∑ ι ∈ res, f ι ≤ ∑ ι ∈ res, leaf ι := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hleaf
  have h2 : r * ∑' ι, (if ι ∈ res then 0 else f ι) ≤ ∑' ι, charge ι := by
    rw [← tsum_mul_left]
    refine (hout.mul_left r).tsum_le_tsum (fun ι ↦ ?_) hcs
    have := hcharge ι
    split_ifs at this ⊢ with h
    · simpa using this
    · exact this
  have h3 := hst
  rw [hsplit] at h3
  nlinarith [h1, h2, h3]

/-- Let `O` be a finite type, `N o` finite sets of integers, `a o ≥ 0` real weights and
`f o n x ≥ 0` reals indexed by `x : ℕ × ℕ`. If `∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x ≤ c` for
every finite set `F`, then `∑ o, a o * ∑ n ∈ N o, ∑' x, f o n x ≤ c`. Proof idea: each family
`x ↦ a o * f o n x` with `n ∈ N o` is summable, so the finite sums move inside one series, whose
partial sums are bounded by `c`. -/
theorem sum_mul_tsum_le_of_sum_le {O : Type} [Fintype O] (N : O → Finset ℤ) (a : O → ℝ)
    (ha : ∀ o, 0 ≤ a o)
    (f : O → ℤ → ℕ × ℕ → ℝ) (hf : ∀ o n x, 0 ≤ f o n x) (c : ℝ)
    (h : ∀ F : Finset (ℕ × ℕ), ∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x ≤ c) :
    ∑ o, a o * ∑ n ∈ N o, ∑' x, f o n x ≤ c := by
  have hs : ∀ o, ∀ n ∈ N o, Summable (fun x ↦ a o * f o n x) := by
    intro o n hn
    refine summable_of_sum_le (c := c) (fun x ↦ mul_nonneg (ha o) (hf o n x)) (fun F ↦ ?_)
    calc ∑ x ∈ F, a o * f o n x = a o * ∑ x ∈ F, f o n x := by rw [Finset.mul_sum]
      _ ≤ a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x :=
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun n ↦ ∑ x ∈ F, f o n x)
            (fun n _ ↦ Finset.sum_nonneg fun x _ ↦ hf o n x) hn) (ha o)
      _ ≤ ∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x :=
          Finset.single_le_sum (f := fun o ↦ a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x)
            (fun o _ ↦ mul_nonneg (ha o) (Finset.sum_nonneg fun n _ ↦
                Finset.sum_nonneg fun x _ ↦ hf o n x))
            (Finset.mem_univ o)
      _ ≤ c := h F
  have key : ∑ o, a o * ∑ n ∈ N o, ∑' x, f o n x = ∑' x, ∑ o, ∑ n ∈ N o, a o * f o n x := by
    rw [Summable.tsum_finsetSum (fun o _ ↦ summable_sum (fun n hn ↦ hs o n hn))]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [Summable.tsum_finsetSum (fun n hn ↦ hs o n hn), Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ tsum_mul_left.symm
  rw [key]
  refine Real.tsum_le_of_sum_le (fun x ↦ Finset.sum_nonneg fun o _ ↦ Finset.sum_nonneg fun n _ ↦
    mul_nonneg (ha o) (hf o n x)) (fun F ↦ ?_)
  calc ∑ x ∈ F, ∑ o, ∑ n ∈ N o, a o * f o n x = ∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun o _ ↦ ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [Finset.mul_sum]
    _ ≤ c := h F

/-- For `c > 0`, the family `n ↦ Real.exp (-(c * (n : ℝ) ^ 2))` is summable over the integers. Proof
idea: since `n ≤ n ^ 2` for natural `n`, the terms are bounded by the geometric series of ratio
`Real.exp (-c)`, on the nonnegative and on the negative integers. -/
theorem summable_int_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) : Summable fun n : ℤ ↦ Real.exp
    (-(c * (n : ℝ) ^ 2)) := by
  have hr : Summable fun n : ℕ ↦ Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le ((Real.exp_lt_exp.mpr
        (neg_neg_of_pos hc)).trans_eq Real.exp_zero)
  have hb : ∀ n : ℕ, Real.exp (-(c * (((n : ℤ) : ℝ)) ^ 2)) ≤ Real.exp (-c) ^ n := fun n ↦ by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
    nlinarith
  refine Summable.of_nat_of_neg ?_ ?_
  · exact Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le) hb hr
  · refine Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le) (fun n ↦ ?_) hr
    simpa using hb n

/-- The family `n ↦ (1 + 4 * π ^ 2 * (n : ℝ) ^ 2)⁻¹` is summable over the integers. Proof idea:
compare with `1 / n ^ 2` plus the indicator of `n = 0`, using `1 ≤ 4 * π ^ 2`. -/
theorem summable_int_inv_one_add_mul_sq : Summable (fun n : ℤ ↦ (1 + 4 * π ^ 2 * (n : ℝ) ^ 2)⁻¹) :=
    by
  have hs : Summable (fun n : ℤ ↦ 1 / (n : ℝ) ^ 2 + if n = 0 then 1 else 0) :=
    (Real.summable_one_div_int_pow.mpr one_lt_two).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine hs.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
  by_cases h : n = 0
  · subst h
    simp
  · have hn : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    simp only [h, ite_false, add_zero, one_div]
    apply inv_anti₀ hn
    have h4 : 1 ≤ 4 * π ^ 2 := by nlinarith [pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right h4 hn.le]

/-- The family `n ↦ (1 + (n : ℝ) ^ 2)⁻¹` is summable over the integers. -/
theorem summable_int_inv_one_add_sq : Summable fun n : ℤ ↦ (1 + (n : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ (by positivity) (by linarith)

/-- If `T : ℕ → ℕ → ℝ` is such that `jl ↦ T jl.1 jl.2` is summable over `ℕ × ℕ`, then for every
`d : ℕ` the family `jl ↦ if d < max jl.1 jl.2 then T jl.1 jl.2 else 0` is summable. -/
theorem summable_ite_lt_max_of_summable (d : ℕ) (T : ℕ → ℕ → ℝ)
    (hT : Summable (fun jl : ℕ × ℕ ↦ T jl.1 jl.2)) :
    Summable (fun jl : ℕ × ℕ ↦ if d < max jl.1 jl.2 then T jl.1 jl.2 else 0) := by
  refine (hT.indicator {jl : ℕ × ℕ | d < max jl.1 jl.2}).congr fun jl ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- For a finite set `s` of integers and `f : ℤ → ℝ`, the family `n ↦ if n ∈ s then f n else 0` is
summable. -/
theorem summable_ite_mem_finset (s : Finset ℤ) (f : ℤ → ℝ) : Summable
    (fun n ↦ if n ∈ s then f n else 0) :=
  summable_of_ne_finset_zero (s := s) (fun n hn ↦ by simp [hn])

/-- If `f : ℤ × ℤ → ℝ` is summable, then so is its positive part `ι ↦ max (f ι) 0`. -/
theorem summable_max_zero {f : ℤ × ℤ → ℝ} (hf : Summable f) : Summable fun ι ↦ max (f ι) 0 :=
  Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _) (fun _ ↦
      max_le (le_abs_self _) (abs_nonneg _)) hf.abs

/-- If `|f ι| ≤ K` for all `ι : ℤ × ℤ` and `ι ↦ p ι ^ 2` is summable, then `ι ↦ f ι * p ι ^ 2` is
summable. -/
theorem summable_mul_sq_of_abs_le {f p : ℤ × ℤ → ℝ} {K : ℝ} (hf : ∀ ι, |f ι| ≤ K)
    (hp : Summable fun ι ↦ p ι ^ 2) :
    Summable fun ι ↦ f ι * p ι ^ 2 := by
  refine Summable.of_norm_bounded (g := fun ι ↦ K * p ι ^ 2) (hp.mul_left K) fun ι ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (p ι))]
  exact mul_le_mul_of_nonneg_right (hf ι) (sq_nonneg _)

/-- Let `F g l : ℤ → ℝ` with `g` summable and `l n = 0` for all `n` outside a finite set `T`. If
`|F n| ≤ A * (g n + l n)` for all `n`, with `A` a real constant, then `F` is summable. Proof idea:
compare with the summable majorant `|A| * |g n| + |A| * |l n|`. -/
theorem summable_of_abs_le_mul_add_finite {F g l : ℤ → ℝ} (A : ℝ) (T : Finset ℤ) (hg : Summable g)
    (hl : ∀ n ∉ T, l n = 0)
    (h : ∀ n, |F n| ≤ A * (g n + l n)) : Summable F := by
  have hl' : Summable (fun n ↦ |A| * |l n|) :=
    summable_of_ne_finset_zero (s := T) fun n hn ↦ by simp [hl n hn]
  refine Summable.of_norm_bounded ((hg.abs.mul_left |A|).add hl') fun n ↦ ?_
  rw [Real.norm_eq_abs]
  refine (h n).trans ?_
  calc A * (g n + l n) ≤ |A * (g n + l n)| := le_abs_self _
    _ = |A| * |g n + l n| := abs_mul _ _
    _ ≤ |A| * (|g n| + |l n|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |A| * |g n| + |A| * |l n| := by ring

/-- If `f : ℤ × ℤ → ℝ` is nonnegative and `∑' κ, ENNReal.ofReal (f κ) ≠ ⊤`, then `f` is summable. -/
theorem summable_of_tsum_ofReal_ne_top {f : ℤ × ℤ → ℝ} (hf0 : ∀ κ, 0 ≤ f κ)
    (hf : ∑' κ, ENNReal.ofReal (f κ) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal hf
  simpa [ENNReal.toReal_ofReal (hf0 _)] using this

/-- If `g : ℤ → ℝ` is nonnegative and summable, then for every `n` the family `k ↦ ∏ i, g (k i)` is
summable over `k : Fin n → ℤ`. Proof idea: induction on `n`, using that the product of two
nonnegative summable families is summable on the product type and that `Fin (n + 1) → ℤ` is
equivalent to `ℤ × (Fin n → ℤ)`. -/
theorem summable_pi_fin_prod_of_nonneg (g : ℤ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    ∀ n : ℕ, Summable fun k : Fin n → ℤ ↦ ∏ i, g (k i)
  | 0 => Summable.of_finite
  | n + 1 => by
    have h := hg.mul_of_nonneg (summable_pi_fin_prod_of_nonneg g hg0 hg n) (fun m ↦ hg0 m)
      (fun k ↦ Finset.prod_nonneg fun i _ ↦ hg0 _)
    exact (Fin.consEquiv fun _ ↦ ℤ).summable_iff.mp
      (h.congr fun x ↦ by simp [Fin.consEquiv, Fin.prod_univ_succ])

/-- If `ι ↦ q ι ^ 2` is summable over `ℤ × ℤ`, then so is the shifted family `ι ↦ q (ι + α) ^ 2`,
for every `α : ℤ × ℤ`. -/
theorem summable_sq_comp_add_right {q : ℤ × ℤ → ℝ} (hq : Summable fun ι ↦ q ι ^ 2) (α : ℤ × ℤ) :
    Summable fun ι ↦ q (ι + α) ^ 2 :=
  hq.comp_injective (add_left_injective α)

/-- If `ι ↦ q ι ^ 2` is summable over `ℤ × ℤ`, then so is the shifted family `ι ↦ q (ι - α) ^ 2`,
for every `α : ℤ × ℤ`. -/
theorem summable_sq_comp_sub_right {q : ℤ × ℤ → ℝ} (hq : Summable fun ι ↦ q ι ^ 2) (α : ℤ × ℤ) :
    Summable fun ι ↦ q (ι - α) ^ 2 :=
  hq.comp_injective (sub_left_injective (b := α))

/-- Let `f T1 T2 T3 : ℤ → ℝ` with `f` nonnegative, `T1`, `T2`, `T3` summable and
`f l ≤ c1 * T1 l + c2 * T2 l + c3 * T3 l` for all `l`, with real constants `c1`, `c2`, `c3`. Then
`f` is summable and `∑' l, f l ≤ c1 * ∑' l, T1 l + c2 * ∑' l, T2 l + c3 * ∑' l, T3 l`. -/
theorem summable_tsum_le_of_le_linear_combination (f T1 T2 T3 : ℤ → ℝ) (c1 c2 c3 : ℝ)
    (hf : ∀ l, 0 ≤ f l)
    (hfg : ∀ l, f l ≤ c1 * T1 l + c2 * T2 l + c3 * T3 l)
    (s1 : Summable T1) (s2 : Summable T2) (s3 : Summable T3) :
    Summable f ∧ ∑' l, f l ≤ c1 * ∑' l, T1 l + c2 * ∑' l, T2 l + c3 * ∑' l, T3 l := by
  have hg : Summable (fun l ↦ c1 * T1 l + c2 * T2 l + c3 * T3 l) :=
    ((s1.mul_left c1).add (s2.mul_left c2)).add (s3.mul_left c3)
  have hs : Summable f := Summable.of_nonneg_of_le hf hfg hg
  refine ⟨hs, (Summable.tsum_le_tsum hfg hs hg).trans (le_of_eq ?_)⟩
  rw [Summable.tsum_add ((s1.mul_left c1).add (s2.mul_left c2)) (s3.mul_left c3),
    Summable.tsum_add (s1.mul_left c1) (s2.mul_left c2), tsum_mul_left, tsum_mul_left,
    tsum_mul_left]

/-- Convergence in `ℓ¹` gives convergence of the sums: let `a n : ℤ × ℤ → ℝ` and `c` be summable,
and let each `ι ↦ |a n ι - c ι|` be summable with `∑' ι, |a n ι - c ι| ≤ g n`. If `g n → 0`, then
`∑' ι, a n ι → ∑' ι, c ι`. -/
theorem tendsto_tsum_of_tsum_abs_sub_le {a : ℕ → ℤ × ℤ → ℝ} {c : ℤ × ℤ → ℝ} {g : ℕ → ℝ}
    (ha : ∀ n, Summable (a n)) (hc : Summable c) (hd : ∀ n, Summable (fun ι ↦ |a n ι - c ι|))
    (hb : ∀ n, ∑' ι, |a n ι - c ι| ≤ g n) (hg : Filter.Tendsto g Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ∑' ι, a n ι) Filter.atTop (nhds (∑' ι, c ι)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hg
  rw [← (ha n).tsum_sub hc]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simpa only [Real.norm_eq_abs] using hd n
  · simpa only [Real.norm_eq_abs] using hb n

/-- Let `a b c d : β → ℝ≥0∞` have sums different from `⊤`, let `F i = (a i).toReal - (b i).toReal`
for all `i`, and let `O : β → ℝ` satisfy `O i = 0` and `(c i).toReal - (d i).toReal = 0` for `i` in
a finite set `s`, and `O i = F i - ((c i).toReal - (d i).toReal)` for `i ∉ s`. Then
`(∑' i, a i).toReal - (∑' i, b i).toReal - (∑' i, c i).toReal + (∑' i, d i).toReal = ∑ i ∈ s, F i +
∑' i, O i`. The proof writes `O i = F i - ((c i).toReal - (d i).toReal) - (if i ∈ s then F i else
0)` and sums the three summable families. -/
theorem toReal_tsum_sub_eq_sum_add_tsum {β : Type*} (s : Finset β) (a b c d : β → ℝ≥0∞)
    (F O : β → ℝ)
    (ha : ∑' i, a i ≠ ⊤) (hb : ∑' i, b i ≠ ⊤) (hc : ∑' i, c i ≠ ⊤) (hd : ∑' i, d i ≠ ⊤)
    (hF : ∀ i, F i = (a i).toReal - (b i).toReal)
    (hin : ∀ i ∈ s, (c i).toReal - (d i).toReal = 0 ∧ O i = 0)
    (hout : ∀ i ∉ s, O i = F i - ((c i).toReal - (d i).toReal)) :
    (∑' i, a i).toReal - (∑' i, b i).toReal - (∑' i, c i).toReal + (∑' i, d i).toReal
      = ∑ i ∈ s, F i + ∑' i, O i := by
  classical
  have sa := ENNReal.summable_toReal ha
  have sb := ENNReal.summable_toReal hb
  have sc := ENNReal.summable_toReal hc
  have sd := ENNReal.summable_toReal hd
  have hFs : Summable F := (sa.sub sb).congr fun i ↦ (hF i).symm
  have hYs := sc.sub sd
  have hIs : Summable (fun i ↦ if i ∈ s then F i else 0) :=
    summable_of_ne_finset_zero (s := s) fun i hi ↦ ite_eq_right hi
  have hO : ∀ i, O i = F i - ((c i).toReal - (d i).toReal) - (if i ∈ s then F i else 0) := by
    intro i
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi, (hin i hi).2, (hin i hi).1]
      ring
    · rw [ite_eq_right hi, hout i hi]
      ring
  have e1 : ∑' i, O i = ∑' i, F i - ∑' i, ((c i).toReal - (d i).toReal)
      - ∑' i, (if i ∈ s then F i else 0) := by
    rw [tsum_congr hO, (hFs.sub hYs).tsum_sub hIs, hFs.tsum_sub hYs]
  have e2 : ∑' i, (if i ∈ s then F i else 0) = ∑ i ∈ s, F i := by
    rw [tsum_eq_sum (s := s) fun i hi ↦ ite_eq_right hi]
    exact Finset.sum_congr rfl fun i hi ↦ ite_eq_left hi
  have e3 : ∑' i, F i = ∑' i, (a i).toReal - ∑' i, (b i).toReal := by
    rw [tsum_congr hF, sa.tsum_sub sb]
  have e4 : ∑' i, ((c i).toReal - (d i).toReal) = ∑' i, (c i).toReal - ∑' i, (d i).toReal :=
    sc.tsum_sub sd
  rw [ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top ha),
    ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hb),
    ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hc),
    ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hd)]
  linarith

/-- For nonnegative `f g : ℕ × ℕ → ℝ`, `∑' i, (f i + g i) ≤ ∑' i, f i + ∑' i, g i`, with no
summability assumption. Proof idea: if both are summable this is an equality; otherwise `f + g` is
not summable, so the left side is `0` and the right side is nonnegative. -/
theorem tsum_add_le_add_tsum_of_nonneg {f g : ℕ × ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑' i, (f i + g i) ≤ ∑' i, f i + ∑' i, g i := by
  by_cases h1 : Summable f
  · by_cases h2 : Summable g
    · rw [Summable.tsum_add h1 h2]
    · have hn : ¬ Summable (fun i ↦ f i + g i) := by
        intro hs
        exact h2 (Summable.of_nonneg_of_le hg (fun i ↦ by linarith [hf i]) hs)
      rw [tsum_eq_zero_of_not_summable hn]
      exact add_nonneg (tsum_nonneg hf) (tsum_nonneg hg)
  · have hn : ¬ Summable (fun i ↦ f i + g i) := by
      intro hs
      exact h1 (Summable.of_nonneg_of_le hf (fun i ↦ by linarith [hg i]) hs)
    rw [tsum_eq_zero_of_not_summable hn]
    exact add_nonneg (tsum_nonneg hf) (tsum_nonneg hg)

/-- Fatou's lemma for series over `ℤ × ℤ` in `ℝ≥0∞`, with an extra convergent term: if
`x n ι → x₀ ι` for every `ι` and `K n → K₀`, then
`(∑' ι, x₀ ι) + K₀ ≤ liminf (fun n ↦ (∑' ι, x n ι) + K n) atTop`. -/
theorem tsum_add_le_liminf {x : ℕ → ℤ × ℤ → ℝ≥0∞} {x₀ : ℤ × ℤ → ℝ≥0∞} {K : ℕ → ℝ≥0∞} {K₀ : ℝ≥0∞}
    (h : ∀ ι, Tendsto (fun n ↦ x n ι) atTop (𝓝 (x₀ ι))) (hK : Tendsto K atTop (𝓝 K₀)) :
    (∑' ι, x₀ ι) + K₀ ≤ liminf (fun n ↦ (∑' ι, x n ι) + K n) atTop := by
  rw [tsum_eq_iSup_sum, ENNReal.iSup_add]
  refine iSup_le fun s ↦ ?_
  have ht : Tendsto (fun n ↦ (∑ ι ∈ s, x n ι) + K n) atTop (𝓝 ((∑ ι ∈ s, x₀ ι) + K₀)) :=
    (tendsto_finsetSum s fun ι _ ↦ h ι).add hK
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n ↦ add_le_add (sum_le_tsum s) le_rfl)

/-- Let `a b a' b' : ℤ × ℤ → ℝ≥0∞` and `SN SP : ℝ≥0∞`. Assume that `a ι + b' ι ≤ b ι + a' ι` for all
`ι` whenever `∑' ι, b ι ≠ ⊤`, that `(∑' ι, a' ι) + SN < ⊤`, and that
`(∑' ι, a' ι) + SN ≤ (∑' ι, b' ι) + SP`; then `(∑' ι, a ι) + SN ≤ (∑' ι, b ι) + SP`. The proof sums
the termwise bound, adds the last hypothesis and cancels the finite sum `∑' ι, b' ι`. -/
theorem tsum_add_le_tsum_add_of_le {a b a' b' : ℤ × ℤ → ℝ≥0∞} {SN SP : ℝ≥0∞}
    (hstep : (∑' ι, b ι) ≠ ⊤ → ∀ ι, a ι + b' ι ≤ b ι + a' ι)
    (hfin : (∑' ι, a' ι) + SN < ⊤) (hle : (∑' ι, a' ι) + SN ≤ (∑' ι, b' ι) + SP) :
    (∑' ι, a ι) + SN ≤ (∑' ι, b ι) + SP := by
  by_cases hb : (∑' ι, b ι) = ⊤
  · rw [hb, top_add]
    exact le_top
  have hsum : (∑' ι, a ι) + ∑' ι, b' ι ≤ (∑' ι, b ι) + ∑' ι, a' ι := by
    rw [← tsum_add, ← tsum_add]
    exact tsum_le_tsum (hstep hb)
  have ha' : (∑' ι, a' ι) ≠ ⊤ := (ENNReal.add_lt_top.1 hfin).1.ne
  have hb' : (∑' ι, b' ι) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hb, ha'⟩) (le_trans le_add_self hsum)
  refine (ENNReal.add_le_add_iff_right hb').1 ?_
  calc (∑' ι, a ι) + SN + ∑' ι, b' ι = ((∑' ι, a ι) + ∑' ι, b' ι) + SN := by ring
    _ ≤ ((∑' ι, b ι) + ∑' ι, a' ι) + SN := add_le_add hsum le_rfl
    _ = (∑' ι, b ι) + ((∑' ι, a' ι) + SN) := add_assoc _ _ _
    _ ≤ (∑' ι, b ι) + ((∑' ι, b' ι) + SP) := add_le_add le_rfl hle
    _ = (∑' ι, b ι) + SP + ∑' ι, b' ι := by ring

/-- For a nonnegative `f : ℤ → ℝ`, `∑' n, f n = (∑' n, ENNReal.ofReal (f n)).toReal`. No summability
is assumed: if `f` is not summable, both sides are `0`. -/
theorem tsum_eq_toReal {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ∑' n, f n = (∑' n, ENNReal.ofReal (f n)).toReal := by
  by_cases hs : Summable f
  · rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf)]
  · rw [tsum_eq_zero_of_not_summable hs]
    have h : ∑' n, ENNReal.ofReal (f n) = ⊤ := by
      by_contra h
      exact hs ((ENNReal.summable_toReal h).congr fun n ↦ ENNReal.toReal_ofReal (hf n))
    rw [h, ENNReal.toReal_top]

/-- For a nonnegative `f : ℤ × ℤ → ℝ`, the real sum is the `toReal` of the sum computed in `ℝ≥0∞`:
`∑' ι, f ι = (∑' ι, ENNReal.ofReal (f ι)).toReal`. Summability of `f` is not assumed. -/
theorem tsum_eq_toReal_ofReal {f : ℤ × ℤ → ℝ} (hf : ∀ ι, 0 ≤ f ι) :
    ∑' ι, f ι = (∑' ι, ENNReal.ofReal (f ι)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  exact tsum_congr fun ι ↦ (ENNReal.toReal_ofReal (hf ι)).symm

/-- For a summable `f : ℤ × ℤ → ℝ`, the sum is the difference of the sums of the positive and
negative parts computed in `ℝ≥0∞`:
`∑' ι, f ι = (∑' ι, ENNReal.ofReal (f ι)).toReal - (∑' ι, ENNReal.ofReal (-f ι)).toReal`. The proof
rewrites the two terms as the real sums of `max (f ι) 0` and `max (-f ι) 0`, which are summable. -/
theorem tsum_eq_toReal_tsum_ofReal_sub {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' ι, f ι = (∑' ι, ENNReal.ofReal (f ι)).toReal - (∑' ι, ENNReal.ofReal (-f ι)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top),
    ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal']
  have h1 : Summable (fun ι ↦ max (f ι) 0) :=
    Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _)
        (fun ι ↦ max_le (le_abs_self _) (abs_nonneg _)) hf.abs
  have h2 : Summable (fun ι ↦ max (-f ι) 0) :=
    Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _)
        (fun ι ↦ max_le (neg_le_abs _) (abs_nonneg _)) hf.abs
  rw [← h1.tsum_sub h2]
  exact tsum_congr fun ι ↦ (max_zero_sub_max_neg_zero_eq_self (f ι)).symm

/-- Let `f : ℕ × ℕ → ℝ` be nonnegative and summable, `s` a finite set and `A`, `C` decidable
predicates such that every `i` with `A i` lies in `s` or satisfies `C i`. Then
`∑' i, (if A i then f i else 0) ≤ ∑ i ∈ s, f i + ∑' i, (if C i then f i else 0)`. Proof idea: write
the finite sum as the series of `if i ∈ s then f i else 0` and compare term by term. -/
theorem tsum_ite_le_sum_add_tsum_ite (f : ℕ × ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f)
    (A C : ℕ × ℕ → Prop)
    [DecidablePred A] [DecidablePred C] (s : Finset (ℕ × ℕ)) (h : ∀ i, A i → i ∈ s ∨ C i) :
    (∑' i, if A i then f i else 0) ≤ ∑ i ∈ s, f i + ∑' i, if C i then f i else 0 := by
  have hs1 : Summable (fun i ↦ if i ∈ s then f i else 0) :=
    Summable.of_nonneg_of_le (fun i ↦ by split_ifs; exacts [hf0 i, le_rfl])
      (fun i ↦ by split_ifs; exacts [le_rfl, hf0 i]) hf
  have hs2 : Summable (fun i ↦ if C i then f i else 0) :=
    Summable.of_nonneg_of_le (fun i ↦ by split_ifs; exacts [hf0 i, le_rfl])
      (fun i ↦ by split_ifs; exacts [le_rfl, hf0 i]) hf
  have hs0 : Summable (fun i ↦ if A i then f i else 0) :=
    Summable.of_nonneg_of_le (fun i ↦ by split_ifs; exacts [hf0 i, le_rfl])
      (fun i ↦ by split_ifs; exacts [le_rfl, hf0 i]) hf
  have e : (∑' i, if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
    rw [tsum_eq_sum (s := s) (fun i hi ↦ ite_eq_right hi)]
    exact Finset.sum_congr rfl fun i hi ↦ ite_eq_left hi
  rw [← e, ← hs1.tsum_add hs2]
  refine hs0.tsum_le_tsum (fun i ↦ ?_) (hs1.add hs2)
  by_cases hA : A i
  · rw [ite_eq_left hA]
    rcases h i hA with h1 | h1
    · rw [ite_eq_left h1]; split_ifs <;> linarith [hf0 i]
    · rw [ite_eq_left h1]; split_ifs <;> linarith [hf0 i]
  · rw [ite_eq_right hA]
    split_ifs <;> linarith [hf0 i]

/-- For `f D A : ℤ × ℤ → ℝ≥0∞` and `a b : ℝ≥0∞`, the pointwise bound `f ι ≤ a * D ι + b * A ι` for
all `ι` gives `∑' ι, f ι ≤ a * ∑' ι, D ι + b * ∑' ι, A ι`. -/
theorem tsum_le_mul_tsum_add_mul_tsum {f D A : ℤ × ℤ → ℝ≥0∞} {a b : ℝ≥0∞}
    (h : ∀ ι, f ι ≤ a * D ι + b * A ι) :
    ∑' ι, f ι ≤ a * ∑' ι, D ι + b * ∑' ι, A ι := by
  calc ∑' ι, f ι ≤ ∑' ι, (a * D ι + b * A ι) := tsum_le_tsum h
    _ = a * ∑' ι, D ι + b * ∑' ι, A ι := by
      rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

/-- For `f g : ℕ × ℕ → ℝ` with `g` summable, `0 ≤ g x` and `f x ≤ g x` for all `x`, one has
`∑' x, f x ≤ ∑' x, g x`. No summability of `f` is assumed: the sum of a family that is not summable
is `0` by convention. -/
theorem tsum_le_tsum_of_le_of_nonneg {f g : ℕ × ℕ → ℝ} (hg : Summable g) (hg0 : ∀ x, 0 ≤ g x)
    (h : ∀ x, f x ≤ g x) :
    ∑' x, f x ≤ ∑' x, g x := by
  by_cases hf : Summable f
  · exact hf.tsum_le_tsum h hg
  · rw [tsum_eq_zero_of_not_summable hf]
    exact tsum_nonneg hg0

/-- For `f : ℤ × ℤ → ℝ≥0∞`, shifts `s s' : ℤ × ℤ` and `a : ℝ≥0∞`,
`∑' ι, a * (f (ι - s) + f (ι - s')) = (2 * a) * ∑' ι, f ι`, because a sum over `ℤ × ℤ` does not
change under a shift of the index. -/
theorem tsum_mul_add_shift_eq_two_mul (f : ℤ × ℤ → ℝ≥0∞) (s s' : ℤ × ℤ) (a : ℝ≥0∞) :
    ∑' ι, a * (f (ι - s) + f (ι - s')) = (2 * a) * ∑' ι, f ι := by
  have h1 : ∑' ι, f (ι - s) = ∑' ι, f ι := (Equiv.subRight s).tsum_eq f
  have h2 : ∑' ι, f (ι - s') = ∑' ι, f ι := (Equiv.subRight s').tsum_eq f
  rw [ENNReal.tsum_mul_left, tsum_add, h1, h2]
  ring

/-- For a real `a`, the family on `ℤ × ℤ` that is `a` at `0` and `0` elsewhere satisfies
`∑' ι : ℤ × ℤ, ENNReal.ofReal |if ι = 0 then a else 0| = ENNReal.ofReal |a|`. -/
theorem tsum_ofReal_abs_ite_eq (a : ℝ) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (|if ι = 0 then a else 0|) = ENNReal.ofReal |a| := by
  have e : ∀ ι : ℤ × ℤ, ENNReal.ofReal (|if ι = 0 then a else 0|) = if ι = 0 then
      ENNReal.ofReal |a| else 0 :=
    fun ι ↦ by
      by_cases h0 : ι = 0
      · simp only [ite_eq_left h0]
      · simp only [ite_eq_right h0, abs_zero, ENNReal.ofReal_zero]
  simp only [e]
  exact tsum_ite_eq 0 _

/-- For real `a` and `b`,
`∑' ι : ℤ × ℤ, ENNReal.ofReal |(if ι = 0 then a else 0) - (if ι = 0 then b else 0)| = ENNReal.ofReal
|a - b|`: only the index `0` contributes to the sum. -/
theorem tsum_ofReal_abs_ite_sub_ite_eq (a b : ℝ) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (|(if ι = 0 then a else 0) - (if ι = 0 then b else 0)|) =
      ENNReal.ofReal |a - b| := by
  have e : ∀ ι : ℤ × ℤ, ENNReal.ofReal (|(if ι = 0 then a else 0) - (if ι = 0 then b else 0)|) =
      if ι = 0 then ENNReal.ofReal |a - b| else 0 := fun ι ↦ by
    by_cases h0 : ι = 0
    · simp only [ite_eq_left h0]
    · simp only [ite_eq_right h0, sub_zero, abs_zero, ENNReal.ofReal_zero]
  simp only [e]
  exact tsum_ite_eq 0 _

/-- If `f : ℤ × ℤ → ℝ` is nonnegative and not summable, then `∑' ι, ENNReal.ofReal (f ι) = ⊤`. -/
theorem tsum_ofReal_eq_top_of_not_summable {f : ℤ × ℤ → ℝ} (hf0 : ∀ ι, 0 ≤ f ι)
    (hf : ¬ Summable f) :
    ∑' ι, ENNReal.ofReal (f ι) = ⊤ := by
  by_contra hne
  apply hf
  have := ENNReal.summable_toReal hne
  simpa [ENNReal.toReal_ofReal (hf0 _)] using this

/-- For `p g : ℤ × ℤ → ℝ` and a finite set `s` of shifts,
`∑' ι, ofReal (p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α))) ≤ s.card * (∑' ι, ofReal (p ι ^ 2) + 2 * ∑'
ι, ofReal (g ι ^ 2))` in `ℝ≥0∞`. The proof uses `p ι * (g (ι - α) + g (ι + α)) ≤ p ι ^ 2 + g (ι - α)
^ 2 + g (ι + α) ^ 2` for each `α` and the fact that a sum over `ℤ ×
ℤ` does not change under a shift of the index. -/
theorem tsum_ofReal_mul_sum_shift_le (s : Finset (ℤ × ℤ)) (p g : ℤ × ℤ → ℝ) :
    ∑' ι, ENNReal.ofReal (p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α))) ≤
      (s.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (p ι ^ 2) + 2 * ∑' ι, ENNReal.ofReal (g ι ^ 2)) := by
  have hpt : ∀ ι, ENNReal.ofReal (p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α))) ≤
      ∑ α ∈ s, (ENNReal.ofReal (p ι ^ 2) + ENNReal.ofReal (g (ι - α) ^ 2) +
          ENNReal.ofReal (g (ι + α) ^ 2)) := by
    intro ι
    have hr : p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α)) ≤
        ∑ α ∈ s, (p ι ^ 2 + g (ι - α) ^ 2 + g (ι + α) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun α _ ↦ ?_
      nlinarith [sq_nonneg (p ι - g (ι - α)), sq_nonneg (p ι - g (ι + α))]
    refine le_trans (ENNReal.ofReal_le_ofReal hr) (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun α _ ↦ by positivity)]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [ENNReal.ofReal_add (by
      positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_trans (tsum_le_tsum hpt) (le_of_eq ?_)
  rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
  have e1 : ∀ α ∈ s, ∑' ι, (ENNReal.ofReal (p ι ^ 2) + ENNReal.ofReal (g (ι - α) ^ 2)
      + ENNReal.ofReal (g (ι + α) ^ 2)) =
      ∑' ι, ENNReal.ofReal (p ι ^ 2) + 2 * ∑' ι, ENNReal.ofReal (g ι ^ 2) := by
    intro α _
    rw [tsum_add, tsum_add]
    have s1 : ∑' ι, ENNReal.ofReal (g (ι - α) ^ 2) = ∑' ι, ENNReal.ofReal (g ι ^ 2) :=
      (Equiv.subRight α).tsum_eq (fun ι ↦ ENNReal.ofReal (g ι ^ 2))
    have s2 : ∑' ι, ENNReal.ofReal (g (ι + α) ^ 2) = ∑' ι, ENNReal.ofReal (g ι ^ 2) :=
      (Equiv.addRight α).tsum_eq (fun ι ↦ ENNReal.ofReal (g ι ^ 2))
    rw [s1, s2, two_mul, add_assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul]

/-- If `T : ℕ → ℕ → ℝ` is such that `jl ↦ T jl.1 jl.2` is summable over `ℕ × ℕ`, then
`∑' jl, T jl.1 jl.2 = (∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1), T j l) + ∑' jl, (if d
< max jl.1 jl.2 then T jl.1 jl.2 else
0)`. Proof idea: split the series over the finite square `Finset.range (d + 1) ×ˢ Finset.range (d +
1)` and its complement, which is the set where `d < max jl.1 jl.2`. -/
theorem tsum_prod_eq_sum_range_add_tsum (d : ℕ) (T : ℕ → ℕ → ℝ)
    (hT : Summable (fun jl : ℕ × ℕ ↦ T jl.1 jl.2)) :
    ∑' jl : ℕ × ℕ, T jl.1 jl.2 = (∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1), T j l)
      + ∑' jl : ℕ × ℕ, (if d < max jl.1 jl.2 then T jl.1 jl.2 else 0) := by
  have hs := tsum_subtype ((↑(Finset.range (d + 1) ×ˢ Finset.range (d + 1)) : Set (ℕ × ℕ))ᶜ)
    (fun jl : ℕ × ℕ ↦ T jl.1 jl.2)
  rw [← hT.sum_add_tsum_compl (s := Finset.range (d + 1) ×ˢ Finset.range (d + 1)), hs,
    Finset.sum_product]
  congr 1
  congr 1
  funext jl
  simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.coe_product, Set.mem_prod,
      Finset.coe_range,
    Set.mem_Iio, not_and_or, not_lt, Nat.succ_le_iff, lt_max_iff]

/-- Cauchy-Schwarz inequality for series over `ℤ × ℤ`, in square-root form: if `f` and `h` are
nonnegative and summable, then `i ↦ √(f i) * √(h i)` is summable and
`∑' i, √(f i) * √(h i) ≤ √(∑' i, f i) * √(∑' i, h i)`. The proof sums the bound
`√(f i) * √(h i) ≤ (t * f i + h i / t) / 2`, valid for every `t > 0`, and then uses that the
resulting bound holds for all `t > 0`. -/
theorem tsum_sqrt_mul_sqrt_le {f h : ℤ × ℤ → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hh0 : ∀ i, 0 ≤ h i)
    (hf : Summable f) (hh : Summable h) :
    Summable (fun i ↦ Real.sqrt (f i) * Real.sqrt (h i)) ∧
      ∑' i, Real.sqrt (f i) * Real.sqrt (h i) ≤ Real.sqrt (∑' i, f i) * Real.sqrt (∑' i, h i) := by
  have amgm : ∀ i, ∀ t : ℝ, 0 < t → Real.sqrt (f i) * Real.sqrt (h i) ≤ (t * f i + h i / t) / 2 :=
    fun i t ht ↦ sqrt_mul_sqrt_le_of_pos (hf0 i) (hh0 i) ht
  have hs : Summable (fun i ↦ Real.sqrt (f i) * Real.sqrt (h i)) := by
    refine Summable.of_nonneg_of_le (fun i ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun i ↦ ?_) ((hf.add hh).div_const 2)
    have := amgm i 1 one_pos
    rw [one_mul, div_one] at this
    exact this
  refine ⟨hs, sq_sqrt_bound (tsum_nonneg hf0) (tsum_nonneg hh0) (fun t ht ↦ ?_)⟩
  calc ∑' i, Real.sqrt (f i) * Real.sqrt (h i) ≤ ∑' i, (t * f i + h i / t) / 2 :=
        Summable.tsum_le_tsum (fun i ↦ amgm i t ht) hs
            (((hf.mul_left t).add (hh.div_const t)).div_const 2)
    _ = (t * ∑' i, f i + (∑' i, h i) / t) / 2 := by
        rw [tsum_div_const, (hf.mul_left t).tsum_add (hh.div_const t), tsum_mul_left,
            tsum_div_const]

/-- For `a : ι → Fin n → ℝ≥0∞`, `e : ι → ℝ≥0∞`, `b : Fin n → ℝ≥0∞` and `e' : ℝ≥0∞`,
`(∑' i, ((∑ K, a i K) + e i)) + ((∑ K, b K) + e') = (∑ K, ((∑' i, a i K) + b K)) + ((∑' i, e i) +
e')`. It exchanges the infinite sum with the finite sum and regroups the terms. -/
theorem tsum_sum_add_eq_sum_tsum_add {ι : Type} {n : ℕ} (a : ι → Fin n → ℝ≥0∞) (e : ι → ℝ≥0∞)
    (b : Fin n → ℝ≥0∞) (e' : ℝ≥0∞) :
    (∑' i, ((∑ K, a i K) + e i)) + ((∑ K, b K) + e') = (∑ K, ((∑' i, a i K) + b K)) +
        ((∑' i, e i) + e') := by
  rw [tsum_add, Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable),
      Finset.sum_add_distrib,
    add_add_add_comm]

/-- For a finite set `s` and families `f n : ℕ × ℕ → ℝ` that are nonnegative for `n ∈ s`,
`∑' i, ∑ n ∈ s, f n i ≤ ∑ n ∈ s, ∑' i, f n i`, with no summability assumption. Proof idea: if every
`f n` with `n ∈ s` is summable this is an equality; otherwise the sum over `s` is not summable, so
the left side is `0` and the right side is nonnegative. -/
theorem tsum_sum_le_sum_tsum_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℕ × ℕ → ℝ)
    (hf : ∀ n ∈ s, ∀ i, 0 ≤ f n i) :
    ∑' i, ∑ n ∈ s, f n i ≤ ∑ n ∈ s, ∑' i, f n i := by
  classical
  by_cases h : ∀ n ∈ s, Summable (f n)
  · rw [Summable.tsum_finsetSum h]
  · simp only [not_forall] at h
    obtain ⟨n, hn, hns⟩ := h
    have hnot : ¬ Summable (fun i ↦ ∑ m ∈ s, f m i) := by
      intro hs
      refine hns (Summable.of_nonneg_of_le (hf n hn) (fun i ↦ ?_) hs)
      exact Finset.single_le_sum (f := fun m ↦ f m i) (fun m hm ↦ hf m hm i) hn
    rw [tsum_eq_zero_of_not_summable hnot]
    exact Finset.sum_nonneg (fun m hm ↦ tsum_nonneg (hf m hm))

/-- For a finite set `s` of shifts in `ℤ × ℤ` and `g : ℤ × ℤ → ℝ`,
`∑' ι, ∑ α ∈ s, ENNReal.ofReal (g (ι - α) ^ 2) = s.card * ∑' ι, ENNReal.ofReal (g ι ^
2)` in `ℝ≥0∞`. -/
theorem tsum_sum_shift_eq_card_mul_tsum (s : Finset (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) :
    ∑' ι, ∑ α ∈ s, ENNReal.ofReal (g (ι - α) ^ 2) = (s.card : ℝ≥0∞) * ∑' ι,
        ENNReal.ofReal (g ι ^ 2) := by
  rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
  have e : ∀ α ∈ s, ∑' ι, ENNReal.ofReal (g (ι - α) ^ 2) = ∑' ι, ENNReal.ofReal (g ι ^ 2) :=
      fun α _ ↦
    (Equiv.subRight α).tsum_eq (fun ι ↦ ENNReal.ofReal (g ι ^ 2))
  rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]

/-- For a summable `f : ℤ × ℤ → ℝ`, the sum of the positive parts minus the sum of the negative
parts is the sum of `f`: `∑' ι, max (f ι) 0 - ∑' ι, max (-f ι) 0 = ∑' ι, f ι`. -/
theorem tsum_max_zero_sub_tsum_max_neg {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' ι, max (f ι) 0 - ∑' ι, max (-f ι) 0 = ∑' ι, f ι := by
  rw [← (summable_max_zero hf).tsum_sub (summable_max_zero hf.neg)]
  refine tsum_congr fun ι ↦ ?_
  rcases le_total (f ι) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    ring

/-- For a summable `T : ℤ × ℤ → ℝ` and `a b : ℝ≥0∞`, the inequality
`a + ∑' ι, ofReal (-T ι) ≤ ∑' ι, ofReal (T ι) + b` between the sums of the negative and positive
parts of the terms implies the same inequality for the parts of the total sum:
`a + ofReal (-∑' ι, T ι) ≤ ofReal (∑' ι, T ι) + b`. The proof writes `∑' ι, T ι = p - n`, with `p`
and `n` the real sums of the positive and negative parts, and cancels `ofReal` of the smaller of `p`
and `n` on both sides. -/
theorem add_ofReal_neg_tsum_le_of_termwise {a b : ℝ≥0∞} {T : ℤ × ℤ → ℝ} (hT : Summable T)
    (h : a + ∑' ι, ENNReal.ofReal (-T ι) ≤ (∑' ι, ENNReal.ofReal (T ι)) + b) :
    a + ENNReal.ofReal (-∑' ι, T ι) ≤ ENNReal.ofReal (∑' ι, T ι) + b := by
  have hA : Summable fun ι ↦ |T ι| := hT.abs
  have hp : Summable fun ι ↦ max (T ι) 0 :=
    Summable.of_nonneg_of_le (fun ι ↦ le_max_right _ _)
        (fun ι ↦ max_le (le_abs_self _) (abs_nonneg _)) hA
  have hn : Summable fun ι ↦ max (-T ι) 0 :=
    Summable.of_nonneg_of_le (fun ι ↦ le_max_right _ _)
        (fun ι ↦ max_le (neg_le_abs _) (abs_nonneg _)) hA
  have ep : (∑' ι, ENNReal.ofReal (T ι)) = ENNReal.ofReal (∑' ι, max (T ι) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun ι ↦ le_max_right _ _) hp]
    exact tsum_congr fun ι ↦ ofReal_eq_ofReal_max_zero _
  have en : (∑' ι, ENNReal.ofReal (-T ι)) = ENNReal.ofReal (∑' ι, max (-T ι) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun ι ↦ le_max_right _ _) hn]
    exact tsum_congr fun ι ↦ ofReal_eq_ofReal_max_zero _
  have eX : (∑' ι, T ι) = (∑' ι, max (T ι) 0) - ∑' ι, max (-T ι) 0 := by
    rw [← hp.tsum_sub hn]
    exact tsum_congr fun ι ↦ (max_zero_sub_eq_self (T ι)).symm
  set p := ∑' ι, max (T ι) 0
  set n := ∑' ι, max (-T ι) 0
  have p0 : 0 ≤ p := tsum_nonneg fun ι ↦ le_max_right _ _
  have n0 : 0 ≤ n := tsum_nonneg fun ι ↦ le_max_right _ _
  rw [ep, en] at h
  rw [eX]
  rcases le_total n p with hnp | hpn
  · have e1 : ENNReal.ofReal (-(p - n)) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    have e2 : ENNReal.ofReal p = ENNReal.ofReal (p - n) + ENNReal.ofReal n := by
      rw [← ENNReal.ofReal_add (by linarith) n0]; congr 1; ring
    rw [e1, add_zero]
    rw [e2, add_right_comm] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h
  · have e1 : ENNReal.ofReal (p - n) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    have e2 : ENNReal.ofReal n = ENNReal.ofReal (-(p - n)) + ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_add (by linarith) p0]; congr 1; ring
    rw [e1, zero_add]
    rw [e2, ← add_assoc, add_comm (ENNReal.ofReal p) b] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h

/-- Let `d : ℤ × ℤ → ℝ` be summable, `r > 0`, and `sp sn : ℝ≥0∞` with `sn ≠ ⊤`. If
`sn.toReal - sp.toReal ≤ ∑' ι, d ι` holds whenever `sp ≠ ⊤`, then
`sn * ofReal r + ∑' ι, ofReal (-(d ι * r)) ≤ sp * ofReal r + ∑' ι, ofReal (d ι * r)` in `ℝ≥0∞`. For
`sp = ⊤` the right side is `⊤`; otherwise both sides are `ofReal` of real numbers and the claim
follows from `∑' ι, max (d ι * r) 0 - ∑' ι, max (-(d ι * r)) 0 = (∑' ι, d ι) * r`. -/
theorem mul_ofReal_add_tsum_ofReal_neg_le {d : ℤ × ℤ → ℝ} (hd : Summable d) {sp sn : ℝ≥0∞} {r : ℝ}
    (hr : 0 < r)
    (hsn : sn ≠ ⊤) (hkey : sp ≠ ⊤ → sn.toReal - sp.toReal ≤ ∑' ι, d ι) :
    sn * ENNReal.ofReal r + ∑' ι, ENNReal.ofReal (-(d ι * r))
      ≤ sp * ENNReal.ofReal r + ∑' ι, ENNReal.ofReal (d ι * r) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr
  by_cases hsp : sp = ⊤
  · rw [hsp, ENNReal.top_mul hr0, top_add]; exact le_top
  have hdr : Summable fun ι ↦ d ι * r := hd.mul_right r
  have hs1 : Summable fun ι ↦ max (d ι * r) 0 :=
    Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _)
      (fun ι ↦ max_le (le_abs_self _) (abs_nonneg _)) hdr.abs
  have hs2 : Summable fun ι ↦ max (-(d ι * r)) 0 :=
    Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _)
      (fun ι ↦ max_le (neg_le_abs _) (abs_nonneg _)) hdr.abs
  have e1 : ∑' ι, ENNReal.ofReal (d ι * r) = ENNReal.ofReal (∑' ι, max (d ι * r) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ le_max_right _ _) hs1]
    simp only [ofReal_max_zero]
  have e2 : ∑' ι, ENNReal.ofReal (-(d ι * r)) = ENNReal.ofReal (∑' ι, max (-(d ι * r)) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ le_max_right _ _) hs2]
    simp only [ofReal_max_zero]
  have e3 : sn * ENNReal.ofReal r = ENNReal.ofReal (sn.toReal * r) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hsn]
  have e4 : sp * ENNReal.ofReal r = ENNReal.ofReal (sp.toReal * r) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hsp]
  have hP0 : 0 ≤ ∑' ι, max (d ι * r) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  have hN0 : 0 ≤ ∑' ι, max (-(d ι * r)) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  rw [e1, e2, e3, e4, ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hr.le) hN0,
    ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hr.le) hP0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdiff : ∑' ι, max (d ι * r) 0 - ∑' ι, max (-(d ι * r)) 0 = (∑' ι, d ι) * r := by
    rw [← hs1.tsum_sub hs2, ← tsum_mul_right]
    congr 1
    funext ι
    exact max_zero_sub_max_neg_zero_eq_self _
  have hk := hkey hsp
  have hk' : (sn.toReal - sp.toReal) * r ≤ (∑' ι, d ι) * r := mul_le_mul_of_nonneg_right hk hr.le
  nlinarith

/-- The geometric series `∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k` is not `⊤`. -/
theorem tsum_inv_two_pow_ne_top : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k ≠ ⊤ := by
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

/-- For a summable `f : ℤ × ℤ → ℝ`, the sum of `ENNReal.ofReal (f ι)` in `ℝ≥0∞` is `ENNReal.ofReal`
of the real sum of the positive parts:
`∑' ι, ENNReal.ofReal (f ι) = ENNReal.ofReal (∑' ι, max (f ι) 0)`. -/
theorem tsum_ofReal_eq_ofReal_tsum_max_zero {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' ι, ENNReal.ofReal (f ι) = ENNReal.ofReal (∑' ι, max (f ι) 0) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ le_max_right _ _) (summable_max_zero hf)]
  exact tsum_congr fun ι ↦ ofReal_eq_ofReal_max_zero (f ι)

/-- Summation over `ℤ × ℤ` of a pointwise inequality in which a shifted term cancels. If `P`, `D`
and `E` are nonnegative, `mT ι + D ι ≤ P ι + R ι + ∑ α ∈ s, E α ι` and `∑ α ∈ s, E α (ι + α) ≤ D ι`
for all `ι`, and `∑' ι, ENNReal.ofReal (D ι) ≠ ⊤`, then
`∑' ι, ofReal (mT ι) + ∑' ι, ofReal (-R ι) ≤ ∑' ι, ofReal (P ι) + ∑' ι, ofReal (R ι) + ∑' ι, ofReal
(-mT ι)` in `ℝ≥0∞`. The proof sums the pointwise inequality written with positive and negative
parts, bounds `∑' ι, ∑ α ∈ s, ofReal (E α ι)` by `∑' ι, ofReal (D ι)` after the shifts `ι ↦ ι + α`,
and cancels the finite sum of `D`. -/
theorem tsum_ofReal_le_of_sum_shift_le {s : Finset (ℤ × ℤ)} {mT P R D : ℤ × ℤ → ℝ}
    {E : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hP : ∀ ι, 0 ≤ P ι) (hD : ∀ ι, 0 ≤ D ι) (hE : ∀ α ι, 0 ≤ E α ι)
    (hA : ∀ ι, mT ι + D ι ≤ P ι + R ι + ∑ α ∈ s, E α ι)
    (hB : ∀ ι, ∑ α ∈ s, E α (ι + α) ≤ D ι)
    (hfin : ∑' ι, ENNReal.ofReal (D ι) ≠ ⊤) :
    (∑' ι, ENNReal.ofReal (mT ι)) + ∑' ι, ENNReal.ofReal (-R ι) ≤
      (∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (R ι)) + ∑' ι, ENNReal.ofReal (-mT ι) :=
          by
  have per : ∀ ι, ENNReal.ofReal (mT ι) + ENNReal.ofReal (-R ι) + ENNReal.ofReal (D ι) ≤
      ENNReal.ofReal (P ι) + ENNReal.ofReal (R ι) + ∑ α ∈ s, ENNReal.ofReal (E α ι)
        + ENNReal.ofReal (-mT ι) := by
    intro ι
    rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ ↦ hE α ι), ofReal_eq_ofReal_max_zero (mT ι),
        ofReal_eq_ofReal_max_zero (-R ι),
      ofReal_eq_ofReal_max_zero (R ι), ofReal_eq_ofReal_max_zero (-mT ι),
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (add_nonneg (le_max_right _ _) (le_max_right _ _)) (hD ι),
      ← ENNReal.ofReal_add (hP ι) (le_max_right _ _),
      ← ENNReal.ofReal_add (add_nonneg (hP ι) (le_max_right _ _))
        (Finset.sum_nonneg fun α _ ↦ hE α ι),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hP ι) (le_max_right _ _))
        (Finset.sum_nonneg fun α _ ↦ hE α ι)) (le_max_right _ _)]
    apply ENNReal.ofReal_le_ofReal
    have a1 := max_zero_eq_add_max_neg_zero (mT ι)
    have a2 := max_zero_eq_add_max_neg_zero (R ι)
    have := hA ι
    linarith
  have hsum := tsum_le_tsum per
  simp only [tsum_add] at hsum
  have hsw : ∑' ι, ∑ α ∈ s, ENNReal.ofReal (E α ι) ≤ ∑' ι, ENNReal.ofReal (D ι) := by
    rw [Summable.tsum_finsetSum (fun α _ ↦ CompleteLattice.summable)]
    have e : ∀ α ∈ s, ∑' ι, ENNReal.ofReal (E α ι) = ∑' ι, ENNReal.ofReal (E α (ι + α)) := by
      intro α _
      exact ((Equiv.addRight α).tsum_eq (fun ι ↦ ENNReal.ofReal (E α ι))).symm
    rw [Finset.sum_congr rfl e, ← Summable.tsum_finsetSum (fun α _ ↦ CompleteLattice.summable)]
    refine tsum_le_tsum fun ι ↦ ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ ↦ hE α _)]
    exact ENNReal.ofReal_le_ofReal (hB ι)
  have key : (∑' ι, ENNReal.ofReal (mT ι)) + (∑' ι, ENNReal.ofReal (-R ι)) + ∑' ι,
      ENNReal.ofReal (D ι) ≤
      (∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (R ι)) + ∑' ι, ENNReal.ofReal (-mT ι)
        + ∑' ι, ENNReal.ofReal (D ι) := by
    calc _ ≤ _ := hsum
      _ ≤ (∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (R ι)) + (∑' ι, ENNReal.ofReal (D ι))
            + ∑' ι, ENNReal.ofReal (-mT ι) := by gcongr
      _ = _ := by ring
  exact ENNReal.le_of_add_le_add_right hfin key

/-- Passage from a real inequality between sums over `ℤ × ℤ` to an inequality in `ℝ≥0∞` between
positive and negative parts. If `P` is nonnegative, `ι ↦ d ι - P ι` and `r` are summable, and
`∑' ι, (d ι - P ι) ≤ ∑' ι, r ι + b`, then
`∑' ι, ofReal (d ι) + (∑' ι, ofReal (-r ι) + ofReal (-b)) ≤
(∑' ι, ofReal (P ι) + ∑' ι, ofReal (r ι) + ofReal b) + ∑' ι, ofReal (-d
ι)`. When `P` is not summable the right side is `⊤`; otherwise each sum of `ofReal` is `ofReal` of
the sum of the positive parts, and the claim reduces to the real inequality. -/
theorem tsum_ofReal_le_of_tsum_sub_le {d P r : ℤ × ℤ → ℝ} {b : ℝ} (hP : ∀ ι, 0 ≤ P ι)
    (he : Summable fun ι ↦ d ι - P ι) (hr : Summable r)
    (hle : ∑' ι, (d ι - P ι) ≤ ∑' ι, r ι + b) :
    (∑' ι, ENNReal.ofReal (d ι)) + ((∑' ι, ENNReal.ofReal (-r ι)) + ENNReal.ofReal (-b))
      ≤ ((∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (r ι)) + ENNReal.ofReal b)
        + ∑' ι, ENNReal.ofReal (-d ι) := by
  by_cases hPs : Summable P
  swap
  · rw [tsum_ofReal_eq_top_of_not_summable hP hPs]
    simp
  have hd : Summable d := by
    have := he.add hPs
    simpa using this
  rw [tsum_ofReal_eq_ofReal_tsum_max_zero hd, tsum_ofReal_eq_ofReal_tsum_max_zero hr.neg,
      tsum_ofReal_eq_ofReal_tsum_max_zero hPs, tsum_ofReal_eq_ofReal_tsum_max_zero hr,
    tsum_ofReal_eq_ofReal_tsum_max_zero hd.neg, ofReal_eq_ofReal_max_zero (-b),
        ofReal_eq_ofReal_max_zero b]
  have h1 := tsum_max_zero_sub_tsum_max_neg hd
  have h2 := tsum_max_zero_sub_tsum_max_neg hr
  have h3 : ∑' ι, max (P ι) 0 = ∑' ι, P ι := tsum_congr fun ι ↦ max_eq_left (hP ι)
  have h4 : ∑' ι, d ι = ∑' ι, (d ι - P ι) + ∑' ι, P ι := by
    rw [← he.tsum_add hPs]
    exact tsum_congr fun ι ↦ by ring
  have h5 : max b 0 - max (-b) 0 = b := by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb, max_eq_left (neg_nonneg.2 hb)]
      ring
    · rw [max_eq_left hb, max_eq_right (neg_nonpos.2 hb)]
      ring
  have n1 : 0 ≤ ∑' ι, max (d ι) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  have n2 : 0 ≤ ∑' ι, max (-r ι) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  have n3 : 0 ≤ ∑' ι, max (P ι) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  have n4 : 0 ≤ ∑' ι, max (r ι) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  have n5 : 0 ≤ ∑' ι, max (-d ι) 0 := tsum_nonneg fun _ ↦ le_max_right _ _
  have n6 : 0 ≤ max (-b) 0 := le_max_right _ _
  have n7 : 0 ≤ max b 0 := le_max_right _ _
  rw [← ENNReal.ofReal_add n2 n6, ← ENNReal.ofReal_add n1 (add_nonneg n2 n6),
      ← ENNReal.ofReal_add n3 n4,
    ← ENNReal.ofReal_add (add_nonneg n3 n4) n7, ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg n3 n4) n7) n5]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end PDE.Analysis
