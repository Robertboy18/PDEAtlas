/-
Authors: Levent Alpöge, Tristan Buckmaster

The definitions of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where each was written in several modules. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option linter.style.header false

/-!
# General definitions and their first lemmas: polynomials in a triangular table, steps and counts

Each definition is a formula in objects of Mathlib: a finite sum, a predicate on functions, a
maximum and a minimum, an `if`, the length of a filtered list. The lemmas that follow are the first
facts on them, each proved by unfolding the definition: the clamp lands in `[-1, 1]` and fixes that
interval, the step is monotone and bounded by one, the count obeys a rule for a list with one more
entry, the polynomials are continuous, and `weightPolyDeriv` is the derivative that its name says.

## Main results

* `PDE.Analysis.triPoly`: the polynomial `∑ i ≤ j, cf j i * r ^ i` of the row `j` of a triangular
  table `cf`.
* `PDE.Analysis.IsPolyFun`: `f : ℝ → ℝ` is given by a real polynomial.
* `PDE.Analysis.weightPolyDeriv`: the derivative of `s ^ a * (1 - s) ^ b`, written out.
* `PDE.Analysis.clampUnit`: `max (-1) (min 1 x)`.
* `PDE.Analysis.unitStep`: `1` for `0 < y`, else `0`.
* `PDE.Analysis.belowCount`: the number of entries of a list of reals that are at most `u`.
* `PDE.Analysis.clampUnit_mem_Icc`, `PDE.Analysis.clampUnit_eq_self`: the clamp takes values in
  `[-1, 1]` and is the identity there.
* `PDE.Analysis.abs_unitStep_le_one`, `PDE.Analysis.monotone_unitStep`: the step is bounded by one
  and monotone.
* `PDE.Analysis.belowCount_cons`, `PDE.Analysis.belowCount_le_length`,
  `PDE.Analysis.belowCount_eq_zero_of_lt`: the count of a strictly increasing list with one more
  entry in front, its bound by the length, and its value zero below all entries.
* `PDE.Analysis.continuous_triPoly`: For every table of coefficients `co` and every `j`, the
  function `triPoly co j` is continuous.
* `PDE.Analysis.hasDerivAt_pow_mul_one_sub_pow`, `PDE.Analysis.norm_weightPolyDeriv_le`:
  `weightPolyDeriv a b` is the derivative of `s ^ a * (1 - s) ^ b`, and on `[0, 1]` it is at most
  `(a + b) * (1 - s) ^ (b - 1)` in absolute value.

## Implementation notes

`PDE.Analysis.unitStep` and `PDE.Analysis.clampUnit` are close to functions that Mathlib has in
other forms (an indicator, `max` and `min`); they are not replaced by them.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the definitions and lemmas of this module and their proofs, adapted to this
  library. See `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- The polynomial of degree at most `j` whose coefficients are the row `j` of the triangular table
`cf`: `triPoly cf j r = ∑ i ∈ range (j + 1), cf j i * r ^ i`. -/
def triPoly (cf : ℕ → ℕ → ℝ) (j : ℕ) (r : ℝ) : ℝ := ∑ i ∈ Finset.range (j + 1), cf j i * r ^ i

/-- `f : ℝ → ℝ` is a polynomial function: there is a real polynomial `P` with `f s = P.eval s` for
every `s`. -/
def IsPolyFun (f : ℝ → ℝ) : Prop := ∃ P : Polynomial ℝ, ∀ s, f s = P.eval s

/-- The derivative in `s` of `s ^ a * (1 - s) ^ b`, written out by the product rule:
`a * s ^ (a - 1) * (1 - s) ^ b + s ^ a * (b * (1 - s) ^ (b - 1) * (-1))`. -/
def weightPolyDeriv (a b : ℕ) (s : ℝ) : ℝ := a * s ^ (a - 1) * (1 - s) ^ b + s ^ a *
    (b * (1 - s) ^ (b - 1) * (-1))

/-- The real number `x` clamped to the interval `[-1, 1]`: `clampUnit x = max (-1) (min 1 x)`. -/
def clampUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- The unit step function: `unitStep y = 1` for `0 < y` and `unitStep y = 0` otherwise. -/
def unitStep (y : ℝ) : ℝ := if 0 < y then 1 else 0

/-- The number of entries of the list `l` that are at most `u`. -/
def belowCount (l : List ℝ) (u : ℝ) : ℕ := (l.filter (fun b ↦ decide (b ≤ u))).length

/-- `clampUnit x` lies in `[-1, 1]` for every real `x`. -/
theorem clampUnit_mem_Icc (x : ℝ) : clampUnit x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- `clampUnit x = x` for every `x` in `[-1, 1]`. -/
theorem clampUnit_eq_self {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : clampUnit x = x := by
  unfold clampUnit
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- `|unitStep y| ≤ 1` for every real `y`. -/
theorem abs_unitStep_le_one (y : ℝ) : |unitStep y| ≤ 1 := by
  unfold unitStep
  split_ifs <;> simp

/-- The function `unitStep` is monotone. -/
theorem monotone_unitStep : Monotone unitStep := by
  intro u v huv
  unfold unitStep
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 huv) h2
  · exact zero_le_one
  · exact le_rfl

/-- If `u` is below every entry of the list `l`, then `belowCount l u = 0`. -/
theorem belowCount_eq_zero_of_lt (l : List ℝ) {u : ℝ} (h : ∀ b ∈ l, u < b) : belowCount l u = 0 :=
    by
  unfold belowCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro b hb
  simpa using h b hb

/-- For a strictly increasing list `b :: bs` and a real `u`, `belowCount (b :: bs) u` is
`belowCount bs u + 1` if `b ≤ u`, and `0` otherwise. -/
theorem belowCount_cons (b : ℝ) (bs : List ℝ) (h : (b :: bs).Pairwise (· < ·)) (u : ℝ) :
    belowCount (b :: bs) u = if b ≤ u then belowCount bs u + 1 else 0 := by
  unfold belowCount
  by_cases hb : b ≤ u
  · rw [ite_eq_left hb, List.filter_cons_of_pos (by simpa using hb), List.length_cons]
  · rw [ite_eq_right hb, List.filter_cons_of_neg (by
      simpa using hb), List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := List.rel_of_pairwise_cons h hc
    simp only [decide_eq_true_eq, not_le]
    linarith [not_le.1 hb]

/-- `belowCount l u` is at most the length of the list `l`. -/
theorem belowCount_le_length (l : List ℝ) (u : ℝ) : belowCount l u ≤ l.length :=
    List.length_filter_le _ _

/-- For every table of coefficients `co` and every `j`, the function `triPoly co j` is continuous.
-/
theorem continuous_triPoly (co : ℕ → ℕ → ℝ) (j : ℕ) : Continuous (triPoly co j) := by
  unfold triPoly; fun_prop

/-- The derivative of `s ↦ s ^ a * (1 - s) ^ b` at `s` is `weightPolyDeriv a b s`. -/
theorem hasDerivAt_pow_mul_one_sub_pow (a b : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ s ^ a * (1 - s) ^ b) (weightPolyDeriv a b s) s :=
  (hasDerivAt_pow a s).mul (((hasDerivAt_id' s).const_sub 1).pow b)

/-- For `0 ≤ s ≤ 1`, the derivative `weightPolyDeriv a b s` of `s ^ a * (1 - s) ^ b` is at most
`(a + b) * (1 - s) ^ (b - 1)` in absolute value (stated for its value as a complex number). -/
theorem norm_weightPolyDeriv_le (a b : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖((weightPolyDeriv a b s : ℝ) : ℂ)‖ ≤ (a + b) * (1 - s) ^ (b - 1) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold weightPolyDeriv
  have hu : 0 ≤ 1 - s := by linarith
  have p1 : s ^ (a - 1) ≤ 1 := pow_le_one₀ h0 h1
  have p2 : s ^ a ≤ 1 := pow_le_one₀ h0 h1
  have p3 : (1 - s) ^ b ≤ (1 - s) ^ (b - 1) := pow_le_pow_of_le_one hu (by
    linarith) (Nat.sub_le b 1)
  have q1 : 0 ≤ s ^ (a - 1) := by positivity
  have q2 : 0 ≤ s ^ a := by positivity
  have q3 : 0 ≤ (1 - s) ^ b := by positivity
  have q4 : 0 ≤ (1 - s) ^ (b - 1) := by positivity
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have X1 : 0 ≤ s ^ (a - 1) * (1 - s) ^ b := mul_nonneg q1 q3
  have X1' : s ^ (a - 1) * (1 - s) ^ b ≤ (1 - s) ^ (b - 1) := by
    calc s ^ (a - 1) * (1 - s) ^ b ≤ 1 * (1 - s) ^ (b - 1) := mul_le_mul p1 p3 q3 zero_le_one
      _ = (1 - s) ^ (b - 1) := one_mul _
  have X2 : 0 ≤ s ^ a * (1 - s) ^ (b - 1) := mul_nonneg q2 q4
  have X2' : s ^ a * (1 - s) ^ (b - 1) ≤ (1 - s) ^ (b - 1) := by
    calc s ^ a * (1 - s) ^ (b - 1) ≤ 1 * (1 - s) ^ (b - 1) := mul_le_mul_of_nonneg_right p2 q4
      _ = (1 - s) ^ (b - 1) := one_mul _
  have e : (a : ℝ) * s ^ (a - 1) * (1 - s) ^ b + s ^ a * (b * (1 - s) ^ (b - 1) * (-1)) =
      a * (s ^ (a - 1) * (1 - s) ^ b) - b * (s ^ a * (1 - s) ^ (b - 1)) := by ring
  rw [e, abs_le]
  have m1 := mul_le_mul_of_nonneg_left X1' ha
  have m2 := mul_le_mul_of_nonneg_left X2' hb
  have m3 := mul_nonneg ha X1
  have m4 := mul_nonneg hb X2
  constructor <;> nlinarith

end PDE.Analysis
