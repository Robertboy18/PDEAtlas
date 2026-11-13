/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolarTables
public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.FiniteSum
public import CAS.Continuum.Interval.Rational.RelativeHull

/-!
# Interval evaluation of polar expansions

The coefficient tables of the polar expansion (Chen and Hou, (C.15)) are lists of terms
`c cos(f β)`, `c sin(f β)`. From intervals of `cos β` and `sin β` the Chebyshev recurrences
`cos((f + 2) β) = 2 cos β cos((f + 1) β) - cos(f β)` and the same for the sine give intervals of
all multiple angles, hence of every table entry, and with intervals of the radial factors
`r^{k - n} A_k(r)` and the angular factors `B_l(β)` an interval of the whole expansion of a stored
table. Every product and sum is rounded outward to a relative precision
(`RationalInterval.relativeHull`), so that the denominators stay bounded.

## Main definitions

* `chebyshevPair`: intervals of `cos(f β)`, `sin(f β)`, `cos((f + 1) β)` and `sin((f + 1) β)`
  from intervals of `cos β` and `sin β`.
* `trigVector`: intervals of `cos(f β)` and `sin(f β)` for `f ≤ 6`.
* `trigTermsInterval`, `trigTermsVectorInterval`: the interval of a list of trigonometric terms.
* `tableInterval`: the interval of the expansion `∑_{k, l < 7} C_{k,l}(β) r^{k - n} A_k(r) B_l(β)`
  of a stored table.

## Main results

* `chebyshevPair_sound`: `chebyshevPair` holds intervals of the multiple angles.
* `trigVector_sound`: `trigVector` holds intervals of `cos(f β)` and `sin(f β)` for `f ≤ 6`.
* `trigTermsInterval_sound`: the interval of a list contains its value.
* `trigTermsVectorInterval_sound`: the interval of a list computed from the vector contains its
  value.
* `tableInterval_sound`: the interval of a stored table contains the polar expansion of order
  `n` with the box `N = 7`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.3.1, (C.15).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open Finset Real
open CAS.Continuum (RationalInterval)

/-- The working precision of the interval evaluation, in significant bits. -/
def polarIntervalBits : ℕ := 96

/-- Rounded interval product. -/
def roundedMul (I J : RationalInterval) : RationalInterval :=
  RationalInterval.relativeHull polarIntervalBits (I.mul J)

/-- Rounded interval sum. -/
def roundedAdd (I J : RationalInterval) : RationalInterval :=
  RationalInterval.relativeHull polarIntervalBits (I.add J)

/-- `roundedMul I J` contains `x * y` when `I` contains `x` and `J` contains `y`. -/
theorem roundedMul_sound {I J : RationalInterval} {x y : ℝ} (hx : I.MemReal x)
    (hy : J.MemReal y) : (roundedMul I J).MemReal (x * y) :=
  RationalInterval.relativeHull_sound _ (RationalInterval.mul_sound hx hy)

/-- `roundedAdd I J` contains `x + y` when `I` contains `x` and `J` contains `y`. -/
theorem roundedAdd_sound {I J : RationalInterval} {x y : ℝ} (hx : I.MemReal x)
    (hy : J.MemReal y) : (roundedAdd I J).MemReal (x + y) :=
  RationalInterval.relativeHull_sound _ (RationalInterval.add_sound hx hy)

/-- Intervals of `(cos (f β), sin (f β))` and `(cos ((f + 1) β), sin ((f + 1) β))` from intervals
`c` of `cos β` and `s` of `sin β`. -/
def chebyshevPair (c s : RationalInterval) :
    ℕ → (RationalInterval × RationalInterval) × (RationalInterval × RationalInterval)
  | 0 => ((RationalInterval.const 1, RationalInterval.const 0), (c, s))
  | f + 1 =>
    let P := chebyshevPair c s f
    (P.2, (RationalInterval.relativeHull polarIntervalBits
        ((roundedMul (RationalInterval.const 2) (roundedMul c P.2.1)).sub P.1.1),
      RationalInterval.relativeHull polarIntervalBits
        ((roundedMul (RationalInterval.const 2) (roundedMul c P.2.2)).sub P.1.2)))

/-- The Chebyshev recurrence `cos((f + 2) β) = 2 cos β cos((f + 1) β) - cos(f β)`. -/
theorem cos_succ_succ_mul (f : ℕ) (β : ℝ) :
    Real.cos (((f + 2 : ℕ) : ℝ) * β) =
      2 * (Real.cos β * Real.cos (((f + 1 : ℕ) : ℝ) * β)) - Real.cos ((f : ℝ) * β) := by
  have h1 : (((f + 2 : ℕ) : ℝ) * β) = ((f + 1 : ℕ) : ℝ) * β + β := by push_cast; ring
  have h2 : ((f : ℝ) * β) = ((f + 1 : ℕ) : ℝ) * β - β := by push_cast; ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

/-- The Chebyshev recurrence `sin((f + 2) β) = 2 cos β sin((f + 1) β) - sin(f β)`. -/
theorem sin_succ_succ_mul (f : ℕ) (β : ℝ) :
    Real.sin (((f + 2 : ℕ) : ℝ) * β) =
      2 * (Real.cos β * Real.sin (((f + 1 : ℕ) : ℝ) * β)) - Real.sin ((f : ℝ) * β) := by
  have h1 : (((f + 2 : ℕ) : ℝ) * β) = ((f + 1 : ℕ) : ℝ) * β + β := by push_cast; ring
  have h2 : ((f : ℝ) * β) = ((f + 1 : ℕ) : ℝ) * β - β := by push_cast; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- If `c` contains `cos β` and `s` contains `sin β`, then `chebyshevPair c s f` holds intervals of
`cos(f β)`, `sin(f β)`, `cos((f + 1) β)` and `sin((f + 1) β)`. -/
theorem chebyshevPair_sound {c s : RationalInterval} {β : ℝ} (hc : c.MemReal (Real.cos β))
    (hs : s.MemReal (Real.sin β)) (f : ℕ) :
    (chebyshevPair c s f).1.1.MemReal (Real.cos ((f : ℝ) * β)) ∧
      (chebyshevPair c s f).1.2.MemReal (Real.sin ((f : ℝ) * β)) ∧
      (chebyshevPair c s f).2.1.MemReal (Real.cos (((f + 1 : ℕ) : ℝ) * β)) ∧
      (chebyshevPair c s f).2.2.MemReal (Real.sin (((f + 1 : ℕ) : ℝ) * β)) := by
  induction f with
  | zero =>
    simp only [chebyshevPair]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using RationalInterval.memReal_const (1 : ℚ)
    · simpa using RationalInterval.memReal_const (0 : ℚ)
    · simpa using hc
    · simpa using hs
  | succ f ih =>
    obtain ⟨h1, h2', h3, h4⟩ := ih
    simp only [chebyshevPair]
    refine ⟨h3, h4, ?_, ?_⟩
    · have h2 := RationalInterval.memReal_const (2 : ℚ)
      push_cast at h2
      have := RationalInterval.relativeHull_sound polarIntervalBits
        (RationalInterval.sub_sound (roundedMul_sound h2 (roundedMul_sound hc h3)) h1)
      rw [show f + 1 + 1 = f + 2 by ring, cos_succ_succ_mul]
      exact this
    · have h2 := RationalInterval.memReal_const (2 : ℚ)
      push_cast at h2
      have := RationalInterval.relativeHull_sound polarIntervalBits
        (RationalInterval.sub_sound (roundedMul_sound h2 (roundedMul_sound hc h4)) h2')
      rw [show f + 1 + 1 = f + 2 by ring, sin_succ_succ_mul]
      exact this

/-- The interval of one term `c cos(f β)` or `c sin(f β)`. -/
def trigTermInterval (c s : RationalInterval) (t : TrigTerm) : RationalInterval :=
  let P := (chebyshevPair c s t.freq.natAbs).1
  roundedMul (RationalInterval.const t.coeff)
    (if t.isSin then (if t.freq < 0 then P.2.neg else P.2) else P.1)

/-- If `c` contains `cos β` and `s` contains `sin β`, then `trigTermInterval c s t` contains the
value `t.eval β` of the term `t`. -/
theorem trigTermInterval_sound {c s : RationalInterval} {β : ℝ} (hc : c.MemReal (Real.cos β))
    (hs : s.MemReal (Real.sin β)) (t : TrigTerm) :
    (trigTermInterval c s t).MemReal (t.eval β) := by
  rcases t with ⟨a, f, b⟩
  obtain ⟨hC, hS, -, -⟩ := chebyshevPair_sound hc hs f.natAbs
  unfold trigTermInterval TrigTerm.eval
  simp only
  refine roundedMul_sound (RationalInterval.memReal_const a) ?_
  by_cases hf : 0 ≤ f
  · have hcast : ((f.natAbs : ℕ) : ℝ) = (f : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg hf]
    rw [hcast] at hC hS
    have hnn : ¬f < 0 := by omega
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hnn] <;> assumption
  · have hcast : ((f.natAbs : ℕ) : ℝ) = -(f : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg (by omega), Int.cast_neg]
    rw [hcast, neg_mul, Real.cos_neg] at hC
    rw [hcast, neg_mul, Real.sin_neg] at hS
    have hneg : f < 0 := by omega
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte] using hC
    · simp only [↓reduceIte, hneg]
      simpa using RationalInterval.neg_sound hS

/-- The interval of a list of terms. -/
def trigTermsInterval (c s : RationalInterval) (l : List TrigTerm) : RationalInterval :=
  l.foldr (fun t acc ↦ roundedAdd (trigTermInterval c s t) acc) (RationalInterval.const 0)

/-- If `c` contains `cos β` and `s` contains `sin β`, then `trigTermsInterval c s l` contains the
value `trigTermsEval l β` of the list `l`. -/
theorem trigTermsInterval_sound {c s : RationalInterval} {β : ℝ} (hc : c.MemReal (Real.cos β))
    (hs : s.MemReal (Real.sin β)) (l : List TrigTerm) :
    (trigTermsInterval c s l).MemReal (trigTermsEval l β) := by
  induction l with
  | nil => simpa [trigTermsInterval] using RationalInterval.memReal_const (0 : ℚ)
  | cons t l ih =>
    rw [trigTermsEval_cons]
    exact roundedAdd_sound (trigTermInterval_sound hc hs t) ih

/-- The sum of `f k` over `k ∈ range N` is the sum of the list `(List.range N).map f`. -/
theorem sum_range_eq_list_sum (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range N, f k = ((List.range N).map f).sum := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp

/-- If `F a` contains `g a` for every `a ∈ L`, then the rounded sum of the intervals `F a` over `L`
contains `∑_{a ∈ L} g a`. -/
theorem foldr_roundedAdd_sound {α : Type*} (L : List α) (F : α → RationalInterval)
    (g : α → ℝ) (h : ∀ a ∈ L, (F a).MemReal (g a)) :
    (L.foldr (fun a acc ↦ roundedAdd (F a) acc) (RationalInterval.const 0)).MemReal
      (L.map g).sum := by
  induction L with
  | nil => simpa using RationalInterval.memReal_const (0 : ℚ)
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact roundedAdd_sound (h a (by simp)) (ih fun b hb ↦ h b (by simp [hb]))

/-! ### Expansions of stored tables -/

/-- Intervals of `(cos (f β), sin (f β))` for `f ≤ 6`. -/
def trigVector (c s : RationalInterval) : Array (RationalInterval × RationalInterval) :=
  Array.ofFn (n := 7) fun f ↦ (chebyshevPair c s f).1

/-- The vector holds intervals of `cos (f β)` and `sin (f β)`. -/
def TrigVectorSound (V : Array (RationalInterval × RationalInterval)) (β : ℝ) : Prop :=
  ∀ f (h : f < V.size), V[f].1.MemReal (Real.cos ((f : ℝ) * β)) ∧
    V[f].2.MemReal (Real.sin ((f : ℝ) * β))

/-- If `c` contains `cos β` and `s` contains `sin β`, then `trigVector c s` holds intervals of
`cos(f β)` and `sin(f β)` for `f ≤ 6`. -/
theorem trigVector_sound {c s : RationalInterval} {β : ℝ} (hc : c.MemReal (Real.cos β))
    (hs : s.MemReal (Real.sin β)) : TrigVectorSound (trigVector c s) β := by
  intro f hf
  simp only [trigVector, Array.getElem_ofFn]
  exact ⟨(chebyshevPair_sound hc hs f).1, (chebyshevPair_sound hc hs f).2.1⟩

/-- The interval of one term from the vector, by the recurrence beyond it. -/
def trigTermVectorInterval (V : Array (RationalInterval × RationalInterval))
    (c s : RationalInterval) (t : TrigTerm) : RationalInterval :=
  let P := if h : t.freq.natAbs < V.size then V[t.freq.natAbs] else
    (chebyshevPair c s t.freq.natAbs).1
  roundedMul (RationalInterval.const t.coeff)
    (if t.isSin then (if t.freq < 0 then P.2.neg else P.2) else P.1)

/-- For a vector `V` of intervals of `cos(f β)`, `sin(f β)` and intervals `c ∋ cos β`, `s ∋ sin β`,
`trigTermVectorInterval V c s t` contains the value `t.eval β` of the term `t`. -/
theorem trigTermVectorInterval_sound {V : Array (RationalInterval × RationalInterval)}
    {c s : RationalInterval} {β : ℝ} (hV : TrigVectorSound V β) (hc : c.MemReal (Real.cos β))
    (hs : s.MemReal (Real.sin β)) (t : TrigTerm) :
    (trigTermVectorInterval V c s t).MemReal (t.eval β) := by
  rcases t with ⟨a, f, b⟩
  have hP : (if h : f.natAbs < V.size then V[f.natAbs] else
      (chebyshevPair c s f.natAbs).1).1.MemReal (Real.cos ((f.natAbs : ℝ) * β)) ∧
      (if h : f.natAbs < V.size then V[f.natAbs] else
      (chebyshevPair c s f.natAbs).1).2.MemReal (Real.sin ((f.natAbs : ℝ) * β)) := by
    split_ifs with h
    · exact hV _ h
    · exact ⟨(chebyshevPair_sound hc hs _).1, (chebyshevPair_sound hc hs _).2.1⟩
  obtain ⟨hC, hS⟩ := hP
  unfold trigTermVectorInterval TrigTerm.eval
  simp only
  refine roundedMul_sound (RationalInterval.memReal_const a) ?_
  by_cases hf : 0 ≤ f
  · have hcast : ((f.natAbs : ℕ) : ℝ) = (f : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg hf]
    rw [hcast] at hC hS
    have hnn : ¬f < 0 := by omega
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hnn] <;> assumption
  · have hcast : ((f.natAbs : ℕ) : ℝ) = -(f : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg (by omega), Int.cast_neg]
    rw [hcast, neg_mul, Real.cos_neg] at hC
    rw [hcast, neg_mul, Real.sin_neg] at hS
    have hneg : f < 0 := by omega
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte] using hC
    · simp only [↓reduceIte, hneg]
      simpa using RationalInterval.neg_sound hS

/-- The interval of a list of terms from the vector. -/
def trigTermsVectorInterval (V : Array (RationalInterval × RationalInterval))
    (c s : RationalInterval) (l : List TrigTerm) : RationalInterval :=
  l.foldr (fun t acc ↦ roundedAdd (trigTermVectorInterval V c s t) acc) (RationalInterval.const 0)

/-- For a vector `V` of intervals of `cos(f β)`, `sin(f β)` and intervals `c ∋ cos β`, `s ∋ sin β`,
`trigTermsVectorInterval V c s l` contains the value `trigTermsEval l β` of the list `l`. -/
theorem trigTermsVectorInterval_sound {V : Array (RationalInterval × RationalInterval)}
    {c s : RationalInterval} {β : ℝ} (hV : TrigVectorSound V β) (hc : c.MemReal (Real.cos β))
    (hs : s.MemReal (Real.sin β)) (l : List TrigTerm) :
    (trigTermsVectorInterval V c s l).MemReal (trigTermsEval l β) := by
  induction l with
  | nil => simpa [trigTermsVectorInterval] using RationalInterval.memReal_const (0 : ℚ)
  | cons t l ih =>
    rw [trigTermsEval_cons]
    exact roundedAdd_sound (trigTermVectorInterval_sound hV hc hs t) ih

/-- The interval of `∑_{l < 7} C_{k,l}(β) B_l(β)` for a stored table, skipping empty entries. -/
def tableRowInterval (T : PolarTable) (V : Array (RationalInterval × RationalInterval))
    (c s : RationalInterval) (BI : Array RationalInterval) (k : ℕ) : RationalInterval :=
  (List.range 7).foldr (fun l acc ↦ if (T.get k l).isEmpty then acc else
    roundedAdd (roundedMul (trigTermsVectorInterval V c s (T.get k l))
      (BI.getD l (RationalInterval.const 0))) acc) (RationalInterval.const 0)

/-- The interval of the expansion `∑_{k, l < 7} C_{k,l}(β) r^{k - n} A_k(r) B_l(β)` of a stored
table, from intervals `RA k` of `r^{k - n} A_k(r)` and `BI l` of `B_l(β)`. -/
def tableInterval (T : PolarTable) (V : Array (RationalInterval × RationalInterval))
    (c s : RationalInterval) (RA BI : Array RationalInterval) : RationalInterval :=
  (List.range 7).foldr (fun k acc ↦ roundedAdd (roundedMul (tableRowInterval T V c s BI k)
    (RA.getD k (RationalInterval.const 0))) acc) (RationalInterval.const 0)

/-- For a vector `V` of intervals of `cos(f β)`, `sin(f β)`, intervals `c ∋ cos β`, `s ∋ sin β` and
`BI l ∋ B_l(β)` for `l < 7`, `tableRowInterval T V c s BI k` contains the row sum
`∑_{l < 7} C_{k,l}(β) B_l(β)` of the stored table `T`. -/
theorem tableRowInterval_sound {T : PolarTable} {V : Array (RationalInterval × RationalInterval)}
    {c s : RationalInterval} {BI : Array RationalInterval} {B : ℕ → ℝ → ℝ} {β : ℝ}
    (hV : TrigVectorSound V β) (hc : c.MemReal (Real.cos β)) (hs : s.MemReal (Real.sin β))
    (hBI : ∀ l < 7, (BI.getD l (RationalInterval.const 0)).MemReal (B l β)) (k : ℕ) :
    (tableRowInterval T V c s BI k).MemReal
      (∑ l ∈ range 7, trigTermsEval (T.get k l) β * B l β) := by
  unfold tableRowInterval
  rw [sum_range_eq_list_sum]
  have key : ∀ L : List ℕ, (∀ l ∈ L, l < 7) →
      (L.foldr (fun l acc ↦ if (T.get k l).isEmpty then acc else
        roundedAdd (roundedMul (trigTermsVectorInterval V c s (T.get k l))
          (BI.getD l (RationalInterval.const 0))) acc) (RationalInterval.const 0)).MemReal
        (L.map fun l ↦ trigTermsEval (T.get k l) β * B l β).sum := by
    intro L hL
    induction L with
    | nil => simpa using RationalInterval.memReal_const (0 : ℚ)
    | cons l L ih =>
      have ih' := ih fun l' hl' ↦ hL l' (by simp [hl'])
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      split_ifs with he
      · rw [List.isEmpty_iff.mp he, trigTermsEval_nil, zero_mul, zero_add]
        exact ih'
      · exact roundedAdd_sound (roundedMul_sound (trigTermsVectorInterval_sound hV hc hs _)
          (hBI l (hL l (by simp)))) ih'
  exact key _ fun l hl ↦ List.mem_range.mp hl

/-- **Expansion intervals.** For a stored table with the values of `C`, the interval of the
table contains the polar expansion of order `n` with the box `N = 7`. -/
theorem tableInterval_sound {T : PolarTable} {C : ℕ → ℕ → List TrigTerm} (hT : TableEq T.get C)
    {V : Array (RationalInterval × RationalInterval)} {c s : RationalInterval}
    {RA BI : Array RationalInterval} {A B : ℕ → ℝ → ℝ} {n : ℕ} {r β : ℝ}
    (hV : TrigVectorSound V β) (hc : c.MemReal (Real.cos β)) (hs : s.MemReal (Real.sin β))
    (hRA : ∀ k < 7, (RA.getD k (RationalInterval.const 0)).MemReal (r ^ ((k : ℤ) - n) * A k r))
    (hBI : ∀ l < 7, (BI.getD l (RationalInterval.const 0)).MemReal (B l β)) :
    (tableInterval T V c s RA BI).MemReal (polarExpansion 7 n C A B r β) := by
  rw [← polarExpansion_congr hT]
  have hsum : polarExpansion 7 n T.get A B r β = ∑ k ∈ range 7,
      (∑ l ∈ range 7, trigTermsEval (T.get k l) β * B l β) * (r ^ ((k : ℤ) - n) * A k r) := by
    unfold polarExpansion
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_mul]
    refine sum_congr rfl fun l _ ↦ ?_
    ring
  rw [hsum, sum_range_eq_list_sum]
  unfold tableInterval
  refine foldr_roundedAdd_sound _ _ _ fun k hk ↦ ?_
  exact roundedMul_sound (tableRowInterval_sound hV hc hs hBI k) (hRA k (List.mem_range.mp hk))

end PDE.Analysis
