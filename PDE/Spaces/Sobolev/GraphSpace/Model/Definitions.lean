/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import PDE.DistributionTheory.TestFunction.SmoothMultiplier
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Normed Sobolev graph spaces

An element of `W^{k,p}(Ω)` is stored as the family of its weak derivatives of order at
most `k`, one `Lᵖ(Ω)` class for each symmetric multi-index, in a finite `PiLp p` product; a
submodule imposes the weak-derivative identities. For finite `p` the norm is
`(∑ₐ ‖D^a u‖ₚᵖ)^{1/p}`, the norm of Evans §5.2.2; for `p = ∞` it is the maximum over the
coordinates, which is equivalent to Evans's sum `∑ₐ ‖D^a u‖_∞`.

## Main definitions

* `DerivIndex n k`: symmetric multi-indices of order at most `k`, with the list representative
  `DerivIndex.toList` and the indices `baseIndex`, `firstDerivIndex`, `singleDerivIndex`,
  `secondDerivIndex`, `pairDerivIndex` and `pureDerivIndex`.
* `DerivLp n p Ω`: real `Lᵖ` for Lebesgue measure restricted to `Ω`.
* `WkpAmbientOn`, `IsWkpOn`, `wkpSubmoduleOn`, `WkpSpaceOn`: the ambient product, the
  weak-derivative constraints, and the graph space; `WkpSpace`, `HkSpaceOn` and `HkSpace` are
  the whole-space and `p = 2` cases.
* `TestFunctionOn n Ω`: smooth compactly supported functions with support in `Ω`.
* `mulLpLeft`, `testFunctionLpTop`, `partialTestFunctionLpTop`, `cutoffDerivativeLp`: bounded
  `L^∞` multipliers and the coordinates of cutoff multiplication.

Closedness and completeness are proved in `GraphSpace.Topology.Completeness`, restriction in
`GraphSpace.Operators.Restriction`, and bounded cutoff multiplication in
`GraphSpace.Operators.Cutoff`.

## Implementation notes

Mathlib's Sobolev spaces (`BesselPotentialSpace`) live on a whole vector space and are defined
through the Fourier transform. On a domain, the graph space instead bundles a function with its
indexed weak derivatives, built from Mathlib's `Lp`, `PiLp` and continuous linear maps. Weak
derivatives are read off the coordinates rather than recomputed from a representative. The
integrability, trace, domain and regularity assumptions of a single theorem stay explicit
hypotheses or predicates, not fields of new structures.

The Sobolev library uses the namespace `SobolevSpace` and its subnamespaces, such as
`SobolevSpace.GraphSpace` and `SobolevSpace.VectorValued`. The namespace does not follow the
file path: the path records topic and dependency level.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, p. 256; §5.2.2, pp. 258-259; and §5.2.3,
  Theorem 1(iv), (7), p. 261.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace GraphSpace

/-- A canonical multi-index of total order at most `k`.

The symmetric power `Sym (Fin n) m` is an unordered `m`-tuple, so mixed derivatives differing
only by a permutation have one coordinate in the Sobolev product. -/
abbrev DerivIndex (n k : ℕ) : Type :=
  Σ m : Fin (k + 1), Sym (Fin n) m.1

/-- The finite collection of symmetric derivative indices of order at most `k`. -/
instance {n k : ℕ} : Fintype (DerivIndex n k) := inferInstance

/-- Symmetric derivative indices have decidable equality. -/
instance {n k : ℕ} : DecidableEq (DerivIndex n k) := inferInstance

/-- Choose a list representative of a symmetric derivative index. -/
noncomputable def DerivIndex.toList {n k : ℕ} (a : DerivIndex n k) : List (Fin n) :=
  a.2.1.toList

/-- The list representative of an index of order `m` has length `m`. -/
@[simp] theorem DerivIndex.toList_length {n k : ℕ} (a : DerivIndex n k) :
    a.toList.length = a.1.1 := by
  simp [DerivIndex.toList]

/-- The derivative word represented by an order-`k` index has length at most `k`. -/
theorem DerivIndex.toList_length_le {n k : ℕ} (a : DerivIndex n k) :
    a.toList.length ≤ k := by
  rw [DerivIndex.toList_length]
  exact Nat.le_of_lt_succ a.1.2

/-- The index corresponding to the empty multi-index `α = []`. -/
def baseIndex (n k : ℕ) : DerivIndex n k :=
  ⟨⟨0, Nat.succ_pos _⟩, ⟨(0 : Multiset (Fin n)), by simp⟩⟩

/-- The base index is represented by the empty word. -/
@[simp] theorem baseIndex_toList {n k : ℕ} :
    (baseIndex n k).toList = [] := by
  simp [baseIndex, DerivIndex.toList]

/-- A derivative index represented by the empty word is the base-function index. -/
theorem DerivIndex.eq_baseIndex {n k : ℕ} (a : DerivIndex n k)
    (ha : a.toList = []) : a = baseIndex n k := by
  rcases a with ⟨m, v⟩
  have hm0 : m.1 = 0 := by
    rw [← DerivIndex.toList_length (a := (⟨m, v⟩ : DerivIndex n k)), ha]
    rfl
  have hm : m = (0 : Fin (k + 1)) := by
    apply Fin.ext
    simpa using hm0
  apply Sigma.ext hm
  cases hm
  apply heq_of_eq
  apply Sym.ext
  exact Multiset.card_eq_zero.mp v.2

/-- An order-zero derivative index is necessarily the base-function index. -/
theorem DerivIndex.eq_baseIndex_of_order_zero {n : ℕ}
    (a : DerivIndex n 0) :
    a = baseIndex n 0 := by
  apply a.eq_baseIndex
  apply (List.length_eq_zero_iff).1
  have hlen := a.toList_length_le
  omega

/-- The canonical `DerivIndex` represented by a derivative word `α` with `α.length ≤ k`. -/
def derivIndexOfList {n k : ℕ} (α : List (Fin n)) (hα : α.length ≤ k) : DerivIndex n k :=
  ⟨⟨α.length, Nat.lt_succ_of_le hα⟩, ⟨(α : Multiset (Fin n)), rfl⟩⟩

/-- Choosing a list representative of the canonical multi-index recovers the input up to
permutation, which is the mathematically correct equality notion for mixed partials. -/
theorem derivIndexOfList_toList_perm {n k : ℕ} (α : List (Fin n)) (hα : α.length ≤ k) :
    (derivIndexOfList (n := n) (k := k) α hα).toList.Perm α := by
  rw [← Multiset.coe_eq_coe]
  simp [derivIndexOfList, DerivIndex.toList]

/--
Canonical derivative indices depend only on the underlying symmetric
multi-index, not on the chosen ordering of a derivative word.
-/
theorem derivIndexOfList_eq_of_perm
    {n k : ℕ} {α β : List (Fin n)}
    (hα : α.length ≤ k) (hβ : β.length ≤ k)
    (hperm : α.Perm β) :
    derivIndexOfList (n := n) (k := k) α hα =
      derivIndexOfList (n := n) (k := k) β hβ := by
  apply Sigma.ext (Fin.ext hperm.length_eq)
  have hpq : ∀ s : Multiset (Fin n),
      Multiset.card s = α.length ↔ Multiset.card s = β.length := by
    intro s
    rw [hperm.length_eq]
  exact (Subtype.heq_iff_coe_eq hpq).2
    (Multiset.coe_eq_coe.mpr hperm)

/-- Canonicalizing the chosen list representative of an index recovers that
index. -/
@[simp] theorem derivIndexOfList_toList {n k : ℕ} (a : DerivIndex n k)
    (h : a.toList.length ≤ k) :
    derivIndexOfList (n := n) (k := k) a.toList h = a := by
  apply Sigma.ext (Fin.ext (DerivIndex.toList_length a))
  have hpq : ∀ s : Multiset (Fin n),
      Multiset.card s = a.toList.length ↔
        Multiset.card s = a.1.1 := by
    intro s
    rw [DerivIndex.toList_length]
  exact (Subtype.heq_iff_coe_eq hpq).2 (by
    change (a.2.1.toList : Multiset (Fin n)) = a.2.1
    exact Multiset.coe_toList a.2.1)

/-- Derivative indices are determined by their chosen list representatives. -/
@[ext] theorem DerivIndex.ext {n k : ℕ} {a b : DerivIndex n k}
    (h : a.toList = b.toList) : a = b := by
  have hp : a.toList.Perm b.toList := by
    simp [h]
  calc
    a = derivIndexOfList (n := n) (k := k) a.toList a.toList_length_le :=
      (derivIndexOfList_toList a a.toList_length_le).symm
    _ = derivIndexOfList (n := n) (k := k) b.toList b.toList_length_le :=
      derivIndexOfList_eq_of_perm a.toList_length_le b.toList_length_le hp
    _ = b := derivIndexOfList_toList b b.toList_length_le

/-- The canonical index of the empty derivative word is the base-function coordinate. -/
@[simp] theorem derivIndexOfList_nil {n k : ℕ} (h : 0 ≤ k) :
    derivIndexOfList (n := n) (k := k) [] h = baseIndex n k := by
  apply DerivIndex.eq_baseIndex
  simpa using derivIndexOfList_toList_perm (n := n) (k := k) [] h

/-- Multiplicity of one coordinate direction in a symmetric derivative
multi-index.  Reflection parity is determined by this number for the normal
coordinate. -/
def DerivIndex.multiplicity {n k : ℕ} (a : DerivIndex n k) (i : Fin n) : ℕ :=
  Multiset.count i a.2.1

/-- The chosen list representative has the same coordinate multiplicities as
the underlying symmetric multi-index. -/
@[simp] theorem DerivIndex.toList_count {n k : ℕ} (a : DerivIndex n k)
    (i : Fin n) :
    a.toList.count i = a.multiplicity i := by
  simpa [DerivIndex.toList, DerivIndex.multiplicity] using
    (Multiset.coe_count i a.2.1.toList).symm

/-- The base coordinate contains no derivative direction. -/
@[simp] theorem baseIndex_multiplicity (n k : ℕ) (i : Fin n) :
    (baseIndex n k).multiplicity i = 0 := by
  rw [← DerivIndex.toList_count]
  simp

/-- Canonicalizing a derivative word preserves the multiplicity of every
coordinate direction. -/
@[simp] theorem derivIndexOfList_multiplicity {n k : ℕ}
    (α : List (Fin n)) (hα : α.length ≤ k) (i : Fin n) :
    (derivIndexOfList (n := n) (k := k) α hα).multiplicity i =
      α.count i := by
  simp [derivIndexOfList, DerivIndex.multiplicity]

/-- The canonical index of the `m`-fold pure derivative in direction `i`
inside an order-`k` Sobolev bundle. -/
def pureDerivIndex (n k m : ℕ) (hm : m ≤ k) (i : Fin n) : DerivIndex n k :=
  derivIndexOfList (n := n) (k := k) (List.replicate m i) (by simpa using hm)

/-- The chosen representative of a pure derivative index is its repeated
coordinate word. -/
@[simp] theorem pureDerivIndex_toList {n k m : ℕ} (hm : m ≤ k) (i : Fin n) :
    (pureDerivIndex n k m hm i).toList = List.replicate m i :=
  List.perm_replicate.mp
    (derivIndexOfList_toList_perm
      (n := n) (k := k) (List.replicate m i) (by simpa using hm))

/-- The canonical top-order pure derivative index in direction `i`. -/
def topPureDerivIndex (n k : ℕ) (i : Fin n) : DerivIndex n k :=
  pureDerivIndex n k k (Nat.le_refl k) i

/-- The chosen representative of a top-order pure derivative index consists
of `k` repetitions of its coordinate direction. -/
@[simp] theorem topPureDerivIndex_toList {n k : ℕ} (i : Fin n) :
    (topPureDerivIndex n k i).toList = List.replicate k i := by
  simp [topPureDerivIndex]

/-- The canonical first-derivative coordinate in a positive-order Sobolev
bundle. -/
def firstDerivIndex (n k : ℕ) (hk : 0 < k) (i : Fin n) : DerivIndex n k :=
  derivIndexOfList (n := n) (k := k) [i] (by
    simpa only [List.length_singleton] using (Nat.succ_le_iff.mpr hk))

/-- A singleton derivative word is the canonical first-derivative
coordinate. -/
theorem derivIndexOfList_singleton {n k : ℕ} (i : Fin n)
    (h : [i].length ≤ k) :
    derivIndexOfList (n := n) (k := k) [i] h =
      firstDerivIndex n k (by
        apply Nat.succ_le_iff.mp
        simpa only [List.length_singleton] using h) i :=
  rfl

/-- The first-derivative index in direction `i` is represented by the word `[i]`. -/
@[simp] theorem firstDerivIndex_toList {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (firstDerivIndex n k hk i).toList = [i] := by
  have hp := derivIndexOfList_toList_perm
    (n := n) (k := k) [i] (by
      simpa only [List.length_singleton] using (Nat.succ_le_iff.mpr hk))
  simpa only [firstDerivIndex, List.perm_singleton] using hp

/-- The `DerivIndex` corresponding to the singleton list `[i]` (first partial derivative). -/
def singleDerivIndex (n : ℕ) (i : Fin n) : DerivIndex n 1 :=
  derivIndexOfList (n := n) (k := 1) [i] (by simp)

/-- At order one, the general first-derivative coordinate is the standard
singleton coordinate. -/
theorem firstDerivIndex_one {n : ℕ} (i : Fin n) :
    firstDerivIndex n 1 (by norm_num) i = singleDerivIndex n i :=
  rfl

/-- The order-one derivative index in direction `i` is represented by the word `[i]`. -/
@[simp] theorem singleDerivIndex_toList {n : ℕ} (i : Fin n) :
    (singleDerivIndex (n := n) i).toList = [i] := by
  have hp := derivIndexOfList_toList_perm (n := n) (k := 1) [i] (by simp)
  simpa only [singleDerivIndex, List.perm_singleton] using hp

/-- A first-order index represented by `[i]` is the canonical derivative
coordinate in direction `i`. -/
theorem DerivIndex.eq_singleDerivIndex {n : ℕ}
    (a : DerivIndex n 1) (i : Fin n) (ha : a.toList = [i]) :
    a = singleDerivIndex n i :=
  DerivIndex.ext (by simpa using ha)

/-- Every first-order derivative index is either the base coordinate or one
coordinate derivative. -/
theorem DerivIndex.eq_baseIndex_or_eq_singleDerivIndex {n : ℕ}
    (a : DerivIndex n 1) :
    a = baseIndex n 1 ∨ ∃ i : Fin n, a = singleDerivIndex n i := by
  cases ha : a.toList with
  | nil =>
      exact Or.inl (a.eq_baseIndex ha)
  | cons i tail =>
      cases tail with
      | nil =>
          exact Or.inr ⟨i, a.eq_singleDerivIndex i ha⟩
      | cons j tail =>
          have hlt : a.toList.length < 2 :=
            Nat.lt_succ_of_le a.toList_length_le
          simp [ha] at hlt

/-- Assemble an order-one derivative-coordinate family from its base value
and its values in the coordinate directions.

The remaining list branch is impossible for `DerivIndex n 1`; handling it
here means later constructions need no unreachable fallback. -/
noncomputable def firstOrderRows {n : ℕ} {α : Type*}
    (base : α) (deriv : Fin n → α) : DerivIndex n 1 → α := fun a ↦
  match a.toList with
  | [] => base
  | [i] => deriv i
  | _ => base

/-- The base coordinate of `firstOrderRows` is the supplied base value. -/
@[simp] theorem firstOrderRows_baseIndex {n : ℕ} {α : Type*}
    (base : α) (deriv : Fin n → α) :
    firstOrderRows base deriv (baseIndex n 1) = base := by
  simp [firstOrderRows]

/-- A coordinate derivative of `firstOrderRows` is the supplied value in
that direction. -/
@[simp] theorem firstOrderRows_singleDerivIndex {n : ℕ} {α : Type*}
    (base : α) (deriv : Fin n → α) (i : Fin n) :
    firstOrderRows base deriv (singleDerivIndex n i) = deriv i := by
  simp [firstOrderRows]

/-- The canonical second-derivative coordinate in a Sobolev bundle whose
ambient order is at least two. -/
def secondDerivIndex (n k : ℕ) (hk : 2 ≤ k) (i j : Fin n) : DerivIndex n k :=
  derivIndexOfList (n := n) (k := k) [i, j] (by simpa using hk)

/-- A two-direction derivative word is the canonical second-derivative
coordinate. -/
theorem derivIndexOfList_pair {n k : ℕ} (i j : Fin n)
    (h : [i, j].length ≤ k) :
    derivIndexOfList (n := n) (k := k) [i, j] h =
      secondDerivIndex n k (by simpa using h) i j :=
  rfl

/-- The chosen list representative of a second-derivative coordinate is a
permutation of its two directions. -/
theorem secondDerivIndex_toList_perm {n k : ℕ} (hk : 2 ≤ k) (i j : Fin n) :
    (secondDerivIndex n k hk i j).toList.Perm [i, j] :=
  derivIndexOfList_toList_perm (n := n) (k := k) [i, j] (by simpa using hk)

/-- The second-derivative coordinate in an exact order-two bundle. -/
def pairDerivIndex (n : ℕ) (i j : Fin n) : DerivIndex n 2 :=
  secondDerivIndex n 2 (by norm_num) i j

/-- At order two, the general second-derivative coordinate is the standard
pair coordinate. -/
@[simp] theorem secondDerivIndex_two (n : ℕ) (i j : Fin n) :
    secondDerivIndex n 2 (by norm_num) i j = pairDerivIndex n i j :=
  rfl

/-- The chosen list representative of an exact order-two pair coordinate is
a permutation of its two directions. -/
theorem pairDerivIndex_toList_perm {n : ℕ} (i j : Fin n) :
    (pairDerivIndex n i j).toList.Perm [i, j] := by
  simpa only [pairDerivIndex] using
    secondDerivIndex_toList_perm (n := n) (k := 2) (by norm_num) i j

/-- Swapping the two directions does not change a symmetric second-order
derivative index. -/
theorem secondDerivIndex_comm (n k : ℕ) (hk : 2 ≤ k) (i j : Fin n) :
    secondDerivIndex n k hk i j = secondDerivIndex n k hk j i := by
  apply derivIndexOfList_eq_of_perm
  exact (List.Perm.swap i j []).symm

/-- Swapping the two directions does not change an exact order-two pair
coordinate. -/
theorem pairDerivIndex_comm (n : ℕ) (i j : Fin n) :
    pairDerivIndex n i j = pairDerivIndex n j i := by
  simpa only [pairDerivIndex] using
    secondDerivIndex_comm n 2 (by norm_num) i j

/-- A second-order index represented by `[i, j]` is the canonical symmetric
coordinate for the pair of directions `i` and `j`. -/
theorem DerivIndex.eq_secondDerivIndex {n k : ℕ}
    (a : DerivIndex n k) (hk : 2 ≤ k)
    (i j : Fin n) (ha : a.toList = [i, j]) :
    a = secondDerivIndex n k hk i j := by
  calc
    a = derivIndexOfList (n := n) (k := k) a.toList a.toList_length_le :=
      (derivIndexOfList_toList a a.toList_length_le).symm
    _ = secondDerivIndex n k hk i j := by
      apply derivIndexOfList_eq_of_perm
      simp [ha]

/-- An exact order-two index represented by `[i, j]` is the canonical pair
coordinate for those directions. -/
theorem DerivIndex.eq_pairDerivIndex {n : ℕ}
    (a : DerivIndex n 2) (i j : Fin n) (ha : a.toList = [i, j]) :
    a = pairDerivIndex n i j := by
  simpa only [pairDerivIndex] using
    a.eq_secondDerivIndex (by norm_num) i j ha

/-- Induction over the base, first-order, and second-order coordinates of an
order-two derivative bundle.

The second-order branch receives the chosen ordered list representative
because weak-derivative data on a non-open set need not identify the two
orders almost everywhere. -/
theorem DerivIndex.inductionOnOrderTwo {n : ℕ}
    (motive : DerivIndex n 2 → Prop)
    (base : motive (baseIndex n 2))
    (first : ∀ i : Fin n, motive (firstDerivIndex n 2 (by omega) i))
    (second : ∀ (a : DerivIndex n 2) (i j : Fin n),
      a.toList = [i, j] → motive a)
    (a : DerivIndex n 2) :
    motive a := by
  have hlen : a.toList.length ≤ 2 := a.toList_length_le
  cases hlist : a.toList with
  | nil =>
      simpa [a.eq_baseIndex hlist] using base
  | cons i tail =>
      cases htail : tail with
      | nil =>
          have ha : a = firstDerivIndex n 2 (by omega) i := by
            apply DerivIndex.ext
            simp [hlist, htail]
          simpa [ha] using first i
      | cons j rest =>
          cases hrest : rest with
          | nil =>
              exact second a i j (by simp [hlist, htail, hrest])
          | cons k more =>
              simp [hlist, htail, hrest] at hlen

/-- Exhaustive case split for `DerivIndex 2 2`: every index is the base index, one of the two
first derivatives `[0]`, `[1]`, or one of the three symmetric second derivatives `[0,0]`,
`[0,1]`, `[1,1]` (the word `[1,0]` names the same index as `[0,1]`). This enumeration supports
the two-dimensional second-order computations. -/
theorem DerivIndex.cases_two_two (a : DerivIndex 2 2) :
    a = baseIndex 2 2 ∨
    a = derivIndexOfList [0] (by simp) ∨
    a = derivIndexOfList [1] (by simp) ∨
    a = derivIndexOfList [0, 0] (by simp) ∨
    a = derivIndexOfList [0, 1] (by simp) ∨
    a = derivIndexOfList [1, 1] (by simp) := by
  have hlen := a.toList_length_le
  cases hlist : a.toList with
  | nil =>
      exact Or.inl (a.eq_baseIndex hlist)
  | cons i tail =>
      cases htail : tail with
      | nil =>
          have ha : a = derivIndexOfList a.toList a.toList_length_le :=
            (derivIndexOfList_toList a a.toList_length_le).symm
          fin_cases i
          · exact Or.inr <| Or.inl <| by simpa [hlist, htail] using ha
          · exact Or.inr <| Or.inr <| Or.inl <| by simpa [hlist, htail] using ha
      | cons j rest =>
          cases hrest : rest with
          | nil =>
              have ha : a = derivIndexOfList a.toList a.toList_length_le :=
                (derivIndexOfList_toList a a.toList_length_le).symm
              fin_cases i <;> fin_cases j
              · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
                  simpa [hlist, htail, hrest] using ha
              · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
                  simpa [hlist, htail, hrest] using ha
              · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
                  calc
                    a = derivIndexOfList [1, 0] (by simp) := by
                      simpa [hlist, htail, hrest] using ha
                    _ = derivIndexOfList [0, 1] (by simp) :=
                      derivIndexOfList_eq_of_perm (by simp) (by simp)
                        (List.Perm.swap 1 0 []).symm
              · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| by
                  simpa [hlist, htail, hrest] using ha
          | cons k more =>
              simp [hlist, htail, hrest] at hlen

/-- Expand a finite sum over the six symmetric derivative coordinates of an
order-two Sobolev bundle in two dimensions. -/
theorem sum_derivIndex_two_two {M : Type*} [AddCommMonoid M]
    (f : DerivIndex 2 2 → M) :
    (∑ a, f a) =
      f (baseIndex 2 2) +
      f (derivIndexOfList [0] (by simp)) +
      f (derivIndexOfList [1] (by simp)) +
      f (derivIndexOfList [0, 0] (by simp)) +
      f (derivIndexOfList [0, 1] (by simp)) +
      f (derivIndexOfList [1, 1] (by simp)) := by
  let i0 := baseIndex 2 2
  let i10 := derivIndexOfList (n := 2) (k := 2) [0] (by simp)
  let i01 := derivIndexOfList (n := 2) (k := 2) [1] (by simp)
  let i20 := derivIndexOfList (n := 2) (k := 2) [0, 0] (by simp)
  let i11 := derivIndexOfList (n := 2) (k := 2) [0, 1] (by simp)
  let i02 := derivIndexOfList (n := 2) (k := 2) [1, 1] (by simp)
  have huniv : (Finset.univ : Finset (DerivIndex 2 2)) =
      {i0, i10, i01, i20, i11, i02} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact a.cases_two_two
  change Finset.univ.sum f = _
  rw [huniv]
  rw [Finset.sum_insert (by decide : i0 ∉ ({i10, i01, i20, i11, i02} : Finset _))]
  rw [Finset.sum_insert (by decide : i10 ∉ ({i01, i20, i11, i02} : Finset _))]
  rw [Finset.sum_insert (by decide : i01 ∉ ({i20, i11, i02} : Finset _))]
  rw [Finset.sum_insert (by decide : i20 ∉ ({i11, i02} : Finset _))]
  rw [Finset.sum_insert (by decide : i11 ∉ ({i02} : Finset _))]
  simp [i0, i10, i01, i20, i11, i02]
  ac_rfl

/-- Assemble an order-two derivative-coordinate family from its base,
first-order, and chosen second-order rows.

The final branch is unreachable for `DerivIndex n 2`; centralizing it here
prevents every order-two construction from carrying its own fallback. -/
noncomputable def secondOrderRows {n : ℕ} {α : Type*}
    (base : α) (first : Fin n → α) (second : Fin n → Fin n → α) :
    DerivIndex n 2 → α := fun a ↦
  match a.toList with
  | [] => base
  | [i] => first i
  | [i, j] => second i j
  | _ => base

/-- The base coordinate of `secondOrderRows` is the supplied base value. -/
@[simp] theorem secondOrderRows_baseIndex {n : ℕ} {α : Type*}
    (base : α) (first : Fin n → α) (second : Fin n → Fin n → α) :
    secondOrderRows base first second (baseIndex n 2) = base := by
  simp [secondOrderRows]

/-- A first derivative coordinate of `secondOrderRows` is the supplied row in
that direction. -/
@[simp] theorem secondOrderRows_firstDerivIndex {n : ℕ} {α : Type*}
    (base : α) (first : Fin n → α) (second : Fin n → Fin n → α)
    (i : Fin n) :
    secondOrderRows base first second
      (firstDerivIndex n 2 (by omega) i) = first i := by
  simp [secondOrderRows]

/-- At a coordinate represented by `[i, j]`, `secondOrderRows` returns the
supplied second-order row for that ordered representative. -/
theorem secondOrderRows_of_toList_eq_pair {n : ℕ} {α : Type*}
    (base : α) (first : Fin n → α) (second : Fin n → Fin n → α)
    (a : DerivIndex n 2) (i j : Fin n) (ha : a.toList = [i, j]) :
    secondOrderRows base first second a = second i j := by
  simp [secondOrderRows, ha]

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- The real `L^p` space on `Ω`, using Lebesgue measure restricted to `Ω`. -/
abbrev DerivLp (n : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n)) : Type :=
  MeasureTheory.Lp ℝ p (domainMeasure n Ω)

/-- Multiplication by a fixed `L^∞` coefficient as a continuous linear map on `L^p`.

This is the quantitative operation used by Sobolev cutoff multiplication and by the bounded
coefficient terms arising from chart Jacobians. -/
noncomputable def mulLpLeft [Fact (1 ≤ p)] (ψ : DerivLp n ∞ Ω) :
    DerivLp n p Ω →L[ℝ] DerivLp n p Ω :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ψ • u
      map_add' := fun u v ↦ MeasureTheory.Lp.add_smul ψ u v
      map_smul' := fun c u ↦ (MeasureTheory.Lp.smul_comm c ψ u).symm }
    ‖ψ‖
    (fun u ↦ MeasureTheory.Lp.norm_smul_le ψ u)

/-- `mulLpLeft ψ` acts through the `L^∞ · L^p` scalar action `ψ • u`. -/
@[simp] theorem mulLpLeft_apply [Fact (1 ≤ p)] (ψ : DerivLp n ∞ Ω)
    (u : DerivLp n p Ω) :
    mulLpLeft (n := n) (p := p) (Ω := Ω) ψ u = ψ • u :=
  rfl

/-- The pointwise representative of `mulLpLeft ψ u` is `ψ(x)u(x)` almost everywhere. -/
theorem mulLpLeft_apply_ae [Fact (1 ≤ p)] (ψ : DerivLp n ∞ Ω)
    (u : DerivLp n p Ω) :
    ((mulLpLeft (n := n) (p := p) (Ω := Ω) ψ u : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ ψ x * u x := by
  have hcoe := MeasureTheory.Lp.coeFn_lpSMul
    (p := (∞ : ℝ≥0∞)) (q := p) (r := p) ψ u
  filter_upwards [hcoe] with x hx
  simpa [mulLpLeft_apply, smul_eq_mul] using hx

/-- Operator norm control for multiplication by a bounded coefficient. -/
theorem norm_mulLpLeft_apply_le [Fact (1 ≤ p)] (ψ : DerivLp n ∞ Ω)
    (u : DerivLp n p Ω) :
    ‖mulLpLeft (n := n) (p := p) (Ω := Ω) ψ u‖ ≤ ‖ψ‖ * ‖u‖ :=
  MeasureTheory.Lp.norm_smul_le ψ u

/-- The multiplier's operator norm is bounded by the `L^∞` norm of its coefficient. -/
theorem norm_mulLpLeft_le [Fact (1 ≤ p)] (ψ : DerivLp n ∞ Ω) :
    ‖mulLpLeft (n := n) (p := p) (Ω := Ω) ψ‖ ≤ ‖ψ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
    (norm_mulLpLeft_apply_le (n := n) (p := p) (Ω := Ω) ψ)

/-- Multiplication by a real `L∞` coefficient is self-adjoint on `L²`. -/
theorem inner_lpSMul_left_eq_right
    (a : DerivLp n ∞ Ω) (u v : DerivLp n 2 Ω) :
    inner ℝ (a • u) v = inner ℝ u (a • v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  have hleft := mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) a u
  have hright := mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) a v
  filter_upwards [hleft, hright] with x hl hr
  simp only [mulLpLeft_apply] at hl hr
  rw [hl, hr]
  simp [RCLike.inner_apply]
  ring

/-- Associativity of the heterogeneous `L∞ · (L∞ · L²)` product. -/
theorem lpSMul_top_top_two_assoc
    (a b : DerivLp n ∞ Ω) (u : DerivLp n 2 Ω) :
    a • (b • u) = (a • b : DerivLp n ∞ Ω) • u := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_lpSMul (r := 2) b u,
    MeasureTheory.Lp.coeFn_lpSMul (r := 2) a (b • u : DerivLp n 2 Ω),
    MeasureTheory.Lp.coeFn_lpSMul (r := ∞) a b,
    MeasureTheory.Lp.coeFn_lpSMul (r := 2)
      (a • b : DerivLp n ∞ Ω) u]
      with x hbu habu hab habu'
  rw [habu, habu']
  change a x * (b • u : DerivLp n 2 Ω) x =
    (a • b : DerivLp n ∞ Ω) x * u x
  rw [hbu, hab]
  change a x * (b x * u x) = (a x * b x) * u x
  ring

/-- Bounded real coefficient multipliers commute on `L²`. -/
theorem lpSMul_top_top_two_comm
    (a b : DerivLp n ∞ Ω) (u : DerivLp n 2 Ω) :
    a • (b • u) = b • (a • u) := by
  rw [lpSMul_top_top_two_assoc, lpSMul_top_top_two_assoc]
  congr 1
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (r := ∞) a b,
    MeasureTheory.Lp.coeFn_lpSMul (r := ∞) b a] with x hab hba
  rw [hab, hba]
  change a x * b x = b x * a x
  ring

/-!
## Quantitative cutoff coordinates for `W^{1,p}`

For a smooth compactly supported cutoff `ψ`, multiplication by `ψ` sends `(u, ∂ᵢu)` to
`(ψu, ψ∂ᵢu + (∂ᵢψ)u)`, Leibniz's formula (7) of Evans §5.2.3, Theorem 1(iv), for `|α| = 1`. The
constructions below put the two coefficient functions in `L^∞` and realize the derivative coordinate
as a continuous linear map on `L^p × L^p`. This is the bounded coordinate-level ingredient used when
assembling the full bounded-domain extension operator.
-/

/-- A test function, viewed as an `L^∞` coefficient on `Ω`. -/
noncomputable def testFunctionLpTop (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    DerivLp n ∞ Ω :=
  ψ.memLp_top.toLp ψ.toFun

/-- The `L^∞` representative of a test function agrees almost everywhere with
the original smooth function. -/
theorem testFunctionLpTop_apply_ae (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ((testFunctionLpTop (n := n) (Ω := Ω) ψ : DerivLp n ∞ Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] ψ.toFun :=
  ψ.memLp_top.coeFn_toLp

/-- The `L∞` realization of a sum of test functions is their sum in `Lp`. -/
theorem testFunctionLpTop_add (φ ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    testFunctionLpTop (n := n) (Ω := Ω) (φ + ψ) =
      testFunctionLpTop (n := n) (Ω := Ω) φ +
        testFunctionLpTop (n := n) (Ω := Ω) ψ := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    testFunctionLpTop_apply_ae (n := n) (Ω := Ω) (φ + ψ),
    testFunctionLpTop_apply_ae (n := n) (Ω := Ω) φ,
    testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ,
    MeasureTheory.Lp.coeFn_add
      (testFunctionLpTop (n := n) (Ω := Ω) φ)
      (testFunctionLpTop (n := n) (Ω := Ω) ψ)] with x hsum hφ hψ hadd
  rw [hsum, hadd]
  change φ x + ψ x =
    testFunctionLpTop (n := n) (Ω := Ω) φ x +
      testFunctionLpTop (n := n) (Ω := Ω) ψ x
  rw [hφ, hψ]
  rfl

/-- The `L∞` realization of a product of test functions is their pointwise
`Lp` product. -/
theorem testFunctionLpTop_mul (φ ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    testFunctionLpTop (n := n) (Ω := Ω)
        (TestFunction.mul φ ψ) =
      testFunctionLpTop (n := n) (Ω := Ω) φ •
        testFunctionLpTop (n := n) (Ω := Ω) ψ := by
  apply MeasureTheory.Lp.ext
  have hprod := testFunctionLpTop_apply_ae
    (n := n) (Ω := Ω) (TestFunction.mul φ ψ)
  have hφ := testFunctionLpTop_apply_ae (n := n) (Ω := Ω) φ
  have hψ := testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ
  have hmul := mulLpLeft_apply_ae
    (n := n) (p := ∞) (Ω := Ω)
    (testFunctionLpTop (n := n) (Ω := Ω) φ)
    (testFunctionLpTop (n := n) (Ω := Ω) ψ)
  filter_upwards [hprod, hφ, hψ, hmul] with x hp hφx hψx hm
  simp only [mulLpLeft_apply] at hm
  rw [hp, hm, hφx, hψx]
  rfl

/-- The first partial derivative of a test function, viewed as an `L^∞`
coefficient on `Ω`. -/
noncomputable def partialTestFunctionLpTop (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (i : Fin n) : DerivLp n ∞ Ω :=
  testFunctionLpTop (n := n) (Ω := Ω)
    (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) ψ)

/-- The `L^∞` derivative coefficient represents the analytic partial
derivative of the cutoff almost everywhere. -/
theorem partialTestFunctionLpTop_apply_ae (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (i : Fin n) :
    ((partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i : DerivLp n ∞ Ω) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ iteratedPartialDeriv (n := n) [i] ψ.toFun x := by
  unfold partialTestFunctionLpTop
  rw [show (fun x ↦ iteratedPartialDeriv (n := n) [i] ψ.toFun x) =
      ((_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) ψ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ^n → ℝ) by
    funext x
    change (∂[i] ψ.toFun) x =
      _root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) ψ x
    rw [testFunction_lineDerivCLM_apply]
    rfl]
  exact testFunctionLpTop_apply_ae (n := n) (Ω := Ω)
    (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) ψ)

/-- The `L∞` derivative coefficient satisfies the test-function product
rule.  This is the multiplier-level Leibniz identity used by localized
Sobolev energy estimates. -/
theorem partialTestFunctionLpTop_mul
    (φ ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    partialTestFunctionLpTop (n := n) (Ω := Ω)
        (TestFunction.mul φ ψ) i =
      partialTestFunctionLpTop (n := n) (Ω := Ω) φ i •
          testFunctionLpTop (n := n) (Ω := Ω) ψ +
        testFunctionLpTop (n := n) (Ω := Ω) φ •
          partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i := by
  simp only [partialTestFunctionLpTop,
    TestFunction.lineDerivCLM_mul,
    testFunctionLpTop_add, testFunctionLpTop_mul]

/-- The derivative coordinate in cutoff multiplication:
`(u, ∂ᵢu) ↦ ψ ∂ᵢu + (∂ᵢψ) u`. -/
noncomputable def cutoffDerivativeLp [Fact (1 ≤ p)]
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    (DerivLp n p Ω × DerivLp n p Ω) →L[ℝ] DerivLp n p Ω :=
  (mulLpLeft (n := n) (p := p) (Ω := Ω)
      (testFunctionLpTop (n := n) (Ω := Ω) ψ)).comp
      (ContinuousLinearMap.snd ℝ (DerivLp n p Ω) (DerivLp n p Ω)) +
    (mulLpLeft (n := n) (p := p) (Ω := Ω)
      (partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i)).comp
      (ContinuousLinearMap.fst ℝ (DerivLp n p Ω) (DerivLp n p Ω))

/-- Unfolding `cutoffDerivativeLp`: the pair `(u, ∂ᵢu)` is sent to `ψ • ∂ᵢu + (∂ᵢψ) • u`, with
`ψ` and `∂ᵢψ` acting as `L^∞` classes. -/
@[simp] theorem cutoffDerivativeLp_apply [Fact (1 ≤ p)]
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (u du : DerivLp n p Ω) :
    cutoffDerivativeLp (n := n) (p := p) (Ω := Ω) ψ i (u, du) =
      testFunctionLpTop (n := n) (Ω := Ω) ψ • du +
        partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i • u := by
  rfl

/-- The continuous linear cutoff derivative has the expected pointwise product-rule
representative almost everywhere. -/
theorem cutoffDerivativeLp_apply_ae [Fact (1 ≤ p)]
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (u du : DerivLp n p Ω) :
    ((cutoffDerivativeLp (n := n) (p := p) (Ω := Ω) ψ i (u, du) :
        DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * du x +
          iteratedPartialDeriv (n := n) [i] ψ.toFun x * u x := by
  have hψmul :
      ((testFunctionLpTop (n := n) (Ω := Ω) ψ • du : DerivLp n p Ω) :
          ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦ (testFunctionLpTop (n := n) (Ω := Ω) ψ) x * du x := by
    simpa [mulLpLeft_apply] using
      mulLpLeft_apply_ae (n := n) (p := p) (Ω := Ω)
        (testFunctionLpTop (n := n) (Ω := Ω) ψ) du
  have hdψmul :
      ((partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i • u :
          DerivLp n p Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦
            (partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i) x * u x := by
    simpa [mulLpLeft_apply] using
      mulLpLeft_apply_ae (n := n) (p := p) (Ω := Ω)
        (partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i) u
  have hsum :
      ((testFunctionLpTop (n := n) (Ω := Ω) ψ • du +
          partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i • u :
          DerivLp n p Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦
            (testFunctionLpTop (n := n) (Ω := Ω) ψ) x * du x +
              (partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i) x * u x := by
    filter_upwards [
      MeasureTheory.Lp.coeFn_add
        (testFunctionLpTop (n := n) (Ω := Ω) ψ • du)
        (partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i • u),
      hψmul, hdψmul] with x hxadd hxψ hxdψ
    simpa [hxψ, hxdψ] using hxadd
  rw [cutoffDerivativeLp_apply]
  filter_upwards [hsum,
    testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ,
    partialTestFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ i] with x hx hψ hdψ
  simpa [hψ, hdψ] using hx

/-- Quantitative product-rule estimate for a cutoff derivative coordinate. -/
theorem norm_cutoffDerivativeLp_apply_le [Fact (1 ≤ p)]
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (u du : DerivLp n p Ω) :
    ‖cutoffDerivativeLp (n := n) (p := p) (Ω := Ω) ψ i (u, du)‖ ≤
      ‖testFunctionLpTop (n := n) (Ω := Ω) ψ‖ * ‖du‖ +
        ‖partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i‖ * ‖u‖ := by
  rw [cutoffDerivativeLp_apply]
  exact (norm_add_le _ _).trans
    (add_le_add
      (norm_mulLpLeft_apply_le (n := n) (p := p) (Ω := Ω)
        (testFunctionLpTop (n := n) (Ω := Ω) ψ) du)
      (norm_mulLpLeft_apply_le (n := n) (p := p) (Ω := Ω)
        (partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i) u))

/-- Test functions on `ℝ^n` with closed support in `Ω`. For open `Ω` these are the extensions by
zero of the test functions `C_c^∞(Ω)` of Evans §5.2.1. -/
noncomputable def testFunctionSubmoduleOn (n : ℕ) (Ω : Set (ℝ^n)) :
    Submodule ℝ (𝓓((⊤ : Opens (ℝ^n)), ℝ)) where
  carrier := {φ | tsupport φ.toFun ⊆ Ω}
  zero_mem' := by
    change tsupport (fun _ : ℝ^n ↦ (0 : ℝ)) ⊆ Ω
    simp
  add_mem' := by
    intro φ ψ hφ hψ
    have hts : tsupport ((φ + ψ).toFun) ⊆ tsupport φ.toFun ∪ tsupport ψ.toFun := by
      change tsupport (fun x ↦ φ.toFun x + ψ.toFun x) ⊆ tsupport φ.toFun ∪ tsupport ψ.toFun
      exact tsupport_add (f := φ.toFun) (g := ψ.toFun)
    exact hts.trans (union_subset hφ hψ)
  smul_mem' := by
    intro c φ hφ
    have hts : tsupport ((c • φ).toFun) ⊆ tsupport φ.toFun := by
      change tsupport ((fun _ : ℝ^n ↦ c) * φ.toFun) ⊆ tsupport φ.toFun
      exact tsupport_smul_subset_right (f := fun _ : ℝ^n ↦ c) (g := φ.toFun)
    exact hts.trans hφ

/-- The type of smooth compactly supported test functions whose topological support lies in
`Ω`. -/
abbrev TestFunctionOn (n : ℕ) (Ω : Set (ℝ^n)) : Type :=
  testFunctionSubmoduleOn (n := n) (Ω := Ω)

namespace TestFunctionOn

/-- An iterated classical partial derivative of a test function, regarded as a test function on
the same domain. -/
noncomputable def iteratedPartialDeriv
    (φ : TestFunctionOn n Ω) (α : List (Fin n)) : TestFunctionOn n Ω :=
  ⟨⟨PDE.iteratedPartialDeriv (n := n) α φ.1.toFun,
      PDE.contDiff_top_iteratedPartialDeriv (n := n) φ.1.contDiff α,
      SobolevSpace.iteratedPartialDeriv_hasCompactSupport (n := n) φ.1 α,
      subset_univ _⟩,
    (SobolevSpace.tsupport_iteratedPartialDeriv_subset_tsupport
      (n := n) α φ.1.toFun).trans φ.property⟩

/-- The underlying function of the iterated derivative of a test function is the iterated
partial derivative of its underlying function. -/
@[simp] theorem iteratedPartialDeriv_toFun
    (φ : TestFunctionOn n Ω) (α : List (Fin n)) :
    (φ.iteratedPartialDeriv α).1.toFun =
      fun x ↦ PDE.iteratedPartialDeriv (n := n) α φ.1.toFun x :=
  rfl

/-- Coercion form of `iteratedPartialDeriv_toFun`. -/
@[simp] theorem coe_iteratedPartialDeriv
    (φ : TestFunctionOn n Ω) (α : List (Fin n)) :
    ((φ.iteratedPartialDeriv α).1 : ℝ^n → ℝ) =
      fun x ↦ PDE.iteratedPartialDeriv (n := n) α φ.1.toFun x :=
  rfl

end TestFunctionOn

/-- Derivative coordinates with values in an arbitrary normed group, with the finite `PiLp`
Sobolev norm.

At `p = ∞` this is the maximum over derivative coordinates, which is equivalent to their sum
because `DerivIndex n k` is finite. -/
abbrev DerivativeFamily (n k : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n))
    (F : Type*) [NormedAddCommGroup F] :=
  PiLp p (fun _ : DerivIndex n k ↦ MeasureTheory.Lp F p (domainMeasure n Ω))

/-- The scalar specialization of the canonical derivative family. -/
abbrev WkpAmbientOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n)) : Type :=
  PiLp p (fun _ : DerivIndex n k ↦ DerivLp n p Ω)

/-- The weak-derivative constraints for a `PiLp`-family of `Lp` functions. -/
def IsWkpOn (U : WkpAmbientOn n k p Ω) : Prop :=
  ∀ a : DerivIndex n k,
    HasWeakDerivativeOn (n := n) Ω a.toList
      (U (baseIndex n k)) (U a)

/--
For every derivative word `α` of length at most `k`, the coordinate at the multi-index
`derivIndexOfList α` is a weak `α`-derivative of the base coordinate.
-/
theorem IsWkpOn.hasWeakDerivativeOn_list
    {U : WkpAmbientOn n k p Ω}
    (hU : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U)
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn (n := n) Ω α
      (U (baseIndex n k))
      (U (derivIndexOfList (n := n) (k := k) α hα)) :=
  (hU (derivIndexOfList (n := n) (k := k) α hα)).perm
    (derivIndexOfList_toList_perm (n := n) (k := k) α hα)

/--
The weak-derivative constraints of a Sobolev bundle may equivalently be
checked on arbitrary derivative words and their canonical symmetric indices.
-/
theorem isWkpOn_iff_hasWeakDerivativeOn_list
    (U : WkpAmbientOn n k p Ω) :
    IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U ↔
      ∀ (α : List (Fin n)) (hα : α.length ≤ k),
        HasWeakDerivativeOn (n := n) Ω α
          (U (baseIndex n k))
          (U (derivIndexOfList (n := n) (k := k) α hα)) := by
  constructor
  · exact fun hU ↦ hU.hasWeakDerivativeOn_list
  · intro hU a
    simpa using hU a.toList a.toList_length_le

/-- The canonical first-order coordinate is a weak derivative of the base
coordinate in its coordinate direction. -/
theorem IsWkpOn.hasWeakDerivativeOn_first
    {U : WkpAmbientOn n k p Ω}
    (hU : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U)
    (hk : 0 < k) (i : Fin n) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (U (baseIndex n k))
      (U (firstDerivIndex n k hk i)) := by
  simpa only [firstDerivIndex] using
    hU.hasWeakDerivativeOn_list [i] (by
      simpa using (Nat.succ_le_iff.mpr hk))

/-- The zero element of the ambient bundle satisfies the weak-derivative graph relations. -/
theorem isWkpOn_zero : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) 0 := by
  intro a
  have hbase :
      ((0 : WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] 0 := by
    change ((0 : DerivLp n p Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] 0
    exact MeasureTheory.Lp.coeFn_zero ℝ p (domainMeasure n Ω)
  have ha :
      ((0 : WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] 0 := by
    change ((0 : DerivLp n p Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] 0
    exact MeasureTheory.Lp.coeFn_zero ℝ p (domainMeasure n Ω)
  have h0 : HasWeakDerivativeOn (n := n) Ω a.toList 0 0 := by
    refine ⟨MeasureTheory.locallyIntegrableOn_const 0,
      MeasureTheory.locallyIntegrableOn_const 0, ?_⟩
    intro φ _
    simp
  have hcongr :=
    (hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω) (α := a.toList)
      (f := ((0 : WkpAmbientOn n k p Ω) (baseIndex n k))) (g := 0)
      (f' := ((0 : WkpAmbientOn n k p Ω) a)) (g' := 0) hbase ha)
  exact hcongr.2 h0

private theorem isWkpOn_add {U V : WkpAmbientOn n k p Ω}
    (hU : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U)
    (hV : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) V) :
    IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) (U + V) := by
  intro a
  have hsum :
      HasWeakDerivativeOn (n := n) Ω a.toList
        (fun x ↦ (U (baseIndex n k)) x + (V (baseIndex n k)) x)
        (fun x ↦ (U a) x + (V a) x) :=
    hasWeakDerivativeOn_add (hU a) (hV a)
  have hbase :
      ((U + V) (baseIndex n k) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦ (U (baseIndex n k)) x + (V (baseIndex n k)) x := by
    change
      ((U (baseIndex n k) + V (baseIndex n k) : DerivLp n p Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          ((U (baseIndex n k) : ℝ^n → ℝ) + (V (baseIndex n k) : ℝ^n → ℝ))
    exact MeasureTheory.Lp.coeFn_add (U (baseIndex n k)) (V (baseIndex n k))
  have ha :
      ((U + V) a : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ (U a) x + (V a) x := by
    change ((U a + V a : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] ((U a : ℝ^n → ℝ) + (V a : ℝ^n → ℝ))
    exact MeasureTheory.Lp.coeFn_add (U a) (V a)
  have hcongr :=
    (hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω) (α := a.toList)
      (f := ((U + V) (baseIndex n k)))
      (g := fun x ↦ (U (baseIndex n k)) x + (V (baseIndex n k)) x)
      (f' := ((U + V) a))
      (g' := fun x ↦ (U a) x + (V a) x) hbase ha)
  exact hcongr.2 hsum

private theorem isWkpOn_smul (c : ℝ) {U : WkpAmbientOn n k p Ω}
    (hU : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U) :
    IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) (c • U) := by
  intro a
  have hsmul :
      HasWeakDerivativeOn (n := n) Ω a.toList
        (fun x ↦ c • (U (baseIndex n k)) x)
        (fun x ↦ c • (U a) x) :=
    hasWeakDerivativeOn_smul (n := n) (Ω := Ω) (c := c) (α := a.toList) (hU a)
  have hbase :
      ((c • U) (baseIndex n k) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ c • (U (baseIndex n k)) x := by
    change
      ((c • U (baseIndex n k) : DerivLp n p Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] (c • (U (baseIndex n k) : ℝ^n → ℝ))
    exact MeasureTheory.Lp.coeFn_smul c (U (baseIndex n k))
  have ha :
      ((c • U) a : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ c • (U a) x := by
    change ((c • U a : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] (c • (U a : ℝ^n → ℝ))
    exact MeasureTheory.Lp.coeFn_smul c (U a)
  have hcongr :=
    (hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω) (α := a.toList)
      (f := ((c • U) (baseIndex n k)))
      (g := fun x ↦ c • (U (baseIndex n k)) x)
      (f' := ((c • U) a))
      (g' := fun x ↦ c • (U a) x) hbase ha)
  exact hcongr.2 hsmul

/-- The weak-derivative graph submodule of the ambient `PiLp` bundle.

For open `Ω` and `1 ≤ p`, this is the graph-space model of `W^{k,p}(Ω)`.
Its closedness in this range is proved in
`PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness`. -/
def wkpSubmoduleOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n)) :
    Submodule ℝ (WkpAmbientOn n k p Ω) where
  carrier := {U | IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U}
  zero_mem' := isWkpOn_zero (n := n) (k := k) (p := p) (Ω := Ω)
  add_mem' := by
    intro U V hU hV
    exact isWkpOn_add (n := n) (k := k) (p := p) (Ω := Ω) hU hV
  smul_mem' := by
    intro c U hU
    exact isWkpOn_smul (n := n) (k := k) (p := p) (Ω := Ω) c hU

/-- The weak-derivative graph space on `Ω`, with its inherited norm when `1 ≤ p`.

Each coordinate is a Mathlib `Lp` element, hence already quotiented by almost-everywhere equality.
For open `Ω` and `1 ≤ p`, this models `W^{k,p}(Ω)` of Evans §5.2.2. -/
abbrev WkpSpaceOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n)) : Type :=
  wkpSubmoduleOn n k p Ω

/-- The canonical pointwise representative of the order-zero coordinate of
a Sobolev graph-space element. -/
def baseRepresentative (U : WkpSpaceOn n k p Ω) : ℝ^n → ℝ :=
  (((U : WkpAmbientOn n k p Ω) (baseIndex n k) :
    DerivLp n p Ω) : ℝ^n → ℝ)

/-- The canonical base representative of the zero Sobolev element vanishes
almost everywhere. -/
theorem baseRepresentative_zero_ae :
    baseRepresentative (0 : WkpSpaceOn n k p Ω) =ᵐ[domainMeasure n Ω] 0 := by
  change
    ((0 : DerivLp n p Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] 0
  exact MeasureTheory.Lp.coeFn_zero ℝ p (domainMeasure n Ω)

/-- Canonical base representatives respect addition almost everywhere. -/
theorem baseRepresentative_add_ae
    (U V : WkpSpaceOn n k p Ω) :
    baseRepresentative (U + V) =ᵐ[domainMeasure n Ω]
      fun x ↦ baseRepresentative U x + baseRepresentative V x := by
  change
    (((U : WkpAmbientOn n k p Ω) (baseIndex n k) +
      (V : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] _
  exact MeasureTheory.Lp.coeFn_add _ _

/-- Canonical base representatives respect negation almost everywhere. -/
theorem baseRepresentative_neg_ae
    (U : WkpSpaceOn n k p Ω) :
    baseRepresentative (-U) =ᵐ[domainMeasure n Ω]
      fun x ↦ -baseRepresentative U x := by
  change
    ((-(U : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] _
  exact MeasureTheory.Lp.coeFn_neg _

/-- Canonical base representatives respect subtraction almost everywhere. -/
theorem baseRepresentative_sub_ae
    (U V : WkpSpaceOn n k p Ω) :
    baseRepresentative (U - V) =ᵐ[domainMeasure n Ω]
      fun x ↦ baseRepresentative U x - baseRepresentative V x := by
  change
    (((U : WkpAmbientOn n k p Ω) (baseIndex n k) -
      (V : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] _
  exact MeasureTheory.Lp.coeFn_sub _ _

/-- Canonical base representatives respect scalar multiplication almost
everywhere. -/
theorem baseRepresentative_smul_ae
    (c : ℝ) (U : WkpSpaceOn n k p Ω) :
    baseRepresentative (c • U) =ᵐ[domainMeasure n Ω]
      fun x ↦ c • baseRepresentative U x := by
  change
    ((c • (U : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] _
  exact MeasureTheory.Lp.coeFn_smul c _

/-- Canonical base representatives commute with finite sums almost
everywhere. -/
theorem baseRepresentative_sum_ae
    {ι : Type*} [Fintype ι] (U : ι → WkpSpaceOn n k p Ω) :
    baseRepresentative (∑ i, U i) =ᵐ[domainMeasure n Ω]
      fun x ↦ ∑ i, baseRepresentative (U i) x := by
  classical
  suffices h : ∀ s : Finset ι,
      baseRepresentative (∑ i ∈ s, U i) =ᵐ[domainMeasure n Ω]
        fun x ↦ ∑ i ∈ s, baseRepresentative (U i) x by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact baseRepresentative_zero_ae
  | @insert a s ha ih =>
      filter_upwards [baseRepresentative_add_ae (U a) (∑ i ∈ s, U i), ih] with
        x hxAdd hxSum
      calc
        baseRepresentative (∑ i ∈ insert a s, U i) x =
            baseRepresentative (U a + ∑ i ∈ s, U i) x := by
              rw [Finset.sum_insert ha]
        _ = baseRepresentative (U a) x +
              baseRepresentative (∑ i ∈ s, U i) x := hxAdd
        _ = baseRepresentative (U a) x +
              ∑ i ∈ s, baseRepresentative (U i) x := by rw [hxSum]
        _ = ∑ i ∈ insert a s, baseRepresentative (U i) x := by
              rw [Finset.sum_insert ha]

/-- The global Sobolev space `W^{k,p}(ℝ^n)` in this model. -/
abbrev WkpSpace (n k : ℕ) (p : ℝ≥0∞) : Type :=
  WkpSpaceOn n k p Set.univ

/-- The exponent-two graph space.  For open `Ω`, this follows the Hilbert-Sobolev convention
`H^k(Ω) = W^{k,2}(Ω)`. -/
abbrev HkSpaceOn (n k : ℕ) (Ω : Set (ℝ^n)) : Type :=
  WkpSpaceOn n k 2 Ω

/-- The global Hilbert-Sobolev space `H^k(ℝ^n) = W^{k,2}(ℝ^n)` in this model. -/
abbrev HkSpace (n k : ℕ) : Type :=
  WkpSpaceOn n k 2 Set.univ

end GraphSpace

end SobolevSpace
