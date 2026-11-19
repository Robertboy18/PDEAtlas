/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# First-order slices of higher Sobolev derivative bundles

For `U ∈ H^m(Ω)` and a derivative word `α` with `|α| < m`, the function `D^α U` belongs to
`H¹(Ω)`: its base coordinate is the `α` coordinate of `U`, and its first derivatives are the
`α ++ [i]` coordinates. `derivativeSlice` is this map, as a continuous linear map.

These slices let boundary compatibility be stated without choosing pointwise
representatives: saying that `D^α U` has zero trace means that this
`H¹` slice belongs to the closed subspace `H¹₀(Ω)`.

More generally, for `|α| + r ≤ m` and any exponent, extracting `D^α U` together
with its derivatives through order `r` is a contraction
`W^{m,p}(Ω) →L W^{r,p}(Ω)` (`derivativeWordCLM`). Classically these are the
statements `D^α u ∈ W^{k-|α|,p}` and `D^β D^α u = D^{α+β} u` for
`u ∈ W^{k,p}` (Evans, PDE, §5.2.3, Theorem 1(i)). Because `D^α` is addressed by a word while
the coordinates are indexed by symmetric multi-indices, we also prove that
words differing by a permutation address the same coordinate, and give
the converse assembly step: compatible `W^{m,p}` bundles for `U` and for all
of its first derivatives combine into a `W^{m+1,p}` element with the same
base function, with an explicit `L²` norm bound. This assembly is what the
higher-order product theorem in `Product.HigherOrder` uses to go up one order.

## Main results

* `derivativeSlice`: the continuous linear map `W^{m,2}(Ω) → H¹(Ω)`,
  `U ↦ D^α U`, for `|α| < m`.
* `derivativeWordIndex`, `derivativeWordIndex_eq_of_perm`,
  `derivativeWordIndex_injective`: the order-`m` coordinate addressed by a word
  `α` followed by an order-`r` index, and its permutation invariance.
* `IsWkpOn.hasWeakDerivativeOn_from_coordinate`,
  `HasWeakDerivativeOn.append_from_wkp`: inside a Sobolev bundle, the
  `α ++ β` coordinate is the weak `β` derivative of the `α` coordinate.
* `exists_succOrder_of_firstDerivatives`,
  `exists_succOrder_of_firstDerivatives_with_norm`: assembly of a `W^{m+1,p}`
  element from `U` and bundles for its first derivatives, with the constant
  `succOrderAssemblyNormBound n m = √(card (DerivIndex n (m+1)))` in the `L²`
  case.
* `derivativeWordCLM`: the contraction `W^{m,p}(Ω) →L W^{r,p}(Ω)` extracting
  `D^α U`, with `derivativeWordCLM_comp` (words concatenate),
  `derivativeWordCLM_lowerOrderCLM_apply` (compatibility with order
  restriction) and `restrictCLM_derivativeWordCLM` (compatibility with
  domain restriction).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(i), p. 261, and step 1 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace

open Set MeasureTheory Function
open scoped ENNReal Topology Sobolev

variable {n m : ℕ} {Ω : Set (ℝ^n)}

/-- The higher-order derivative index supplying one coordinate of the
first-order slice based at `α`. -/
def derivativeSliceIndex (α : List (Fin n)) (hα : α.length < m)
    (a : DerivIndex n 1) : DerivIndex n m :=
  firstOrderRows
    (derivIndexOfList (n := n) (k := m) α (Nat.le_of_lt hα))
    (fun i ↦ derivIndexOfList (n := n) (k := m) (α ++ [i]) (by
      simpa [List.length_append] using hα))
    a

/-- Ambient bounded map selecting `D^α U` and all of its first derivatives
from the finite order-`m` Sobolev bundle. -/
noncomputable def derivativeSliceAmbient (α : List (Fin n))
    (hα : α.length < m) :
    WkpAmbientOn n m 2 Ω →L[ℝ] WkpAmbientOn n 1 2 Ω := by
  classical
  let eHigh := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n m ↦ DerivLp n 2 Ω)
  let eOne := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)
  exact eOne.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
        ContinuousLinearMap.proj
          (derivativeSliceIndex (n := n) α hα a)).comp
      eHigh.toContinuousLinearMap)

/-- The `H¹` slice for `D^α` selects the corresponding coordinate from the higher-order bundle. -/
@[simp] theorem derivativeSliceAmbient_apply (α : List (Fin n))
    (hα : α.length < m) (U : WkpAmbientOn n m 2 Ω)
    (a : DerivIndex n 1) :
    derivativeSliceAmbient (n := n) (Ω := Ω) α hα U a =
      U (derivativeSliceIndex (n := n) α hα a) := by
  classical
  simp [derivativeSliceAmbient]

/-- Extracting the `H¹` slice `D^α U` preserves the weak-derivative graph
relations of the ambient bundle. -/
theorem derivativeSliceAmbient_mapsIsWkpOn
    (α : List (Fin n)) (hα : α.length < m)
    (U : WkpAmbientOn n m 2 Ω)
    (hU : IsWkpOn (n := n) (k := m) (p := (2 : ℝ≥0∞)) (Ω := Ω) U) :
    IsWkpOn (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      (derivativeSliceAmbient (n := n) (Ω := Ω) α hα U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [baseIndex_toList] using hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain
      (Lp.memLp ((derivativeSliceAmbient α hα U) (baseIndex n 1))) (by norm_num))
  · have hαi : (α ++ [i]).length ≤ m := by simpa [List.length_append] using hα
    let bα : DerivIndex n m := derivIndexOfList α hα.le
    let bαi : DerivIndex n m := derivIndexOfList (α ++ [i]) hαi
    have hbase : HasWeakDerivativeOn Ω α (U (baseIndex n m) : ℝ^n → ℝ) (U bα : ℝ^n → ℝ) := by
      simpa [bα] using hU.hasWeakDerivativeOn_list α hα.le
    have hnext : HasWeakDerivativeOn Ω (α ++ [i]) (U (baseIndex n m) : ℝ^n → ℝ)
        (U bαi : ℝ^n → ℝ) := by
      simpa [bαi] using hU.hasWeakDerivativeOn_list (α ++ [i]) hαi
    simpa [derivativeSliceAmbient_apply, derivativeSliceIndex, bα, bαi]
      using hbase.cancel_prefix_append_single i hnext

/-- Continuous linear extraction of the `H¹` function `D^α U` from an
order-`m` Sobolev function. -/
noncomputable def derivativeSlice (α : List (Fin n)) (hα : α.length < m) :
    W^{m,2}(Ω) →L[ℝ] H¹(Ω) :=
  ContinuousLinearMap.codRestrict
    ((derivativeSliceAmbient (n := n) (Ω := Ω) α hα).comp
      (Submodule.subtypeL (wkpSubmoduleOn n m 2 Ω)))
    (wkpSubmoduleOn n 1 2 Ω)
    (fun U ↦ derivativeSliceAmbient_mapsIsWkpOn
      (n := n) (Ω := Ω) α hα U U.property)

/-- Coercing the `H¹` slice to the ambient bundle gives the ambient slice map. -/
@[simp] theorem derivativeSlice_apply_coe
    (α : List (Fin n)) (hα : α.length < m)
    (U : W^{m,2}(Ω)) :
    ((derivativeSlice (n := n) (Ω := Ω) α hα U : H¹(Ω)) :
        WkpAmbientOn n 1 2 Ω) =
      derivativeSliceAmbient (n := n) (Ω := Ω) α hα
        (U : WkpAmbientOn n m 2 Ω) :=
  rfl

/-- The empty first-order slice is exactly Sobolev order restriction to
`H¹`. -/
@[simp]
theorem derivativeSlice_nil_apply
    (h : ([] : List (Fin n)).length < m)
    (U : W^{m,2}(Ω)) :
    derivativeSlice (n := n) (Ω := Ω) [] h U =
      lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (by omega) U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rw [derivativeSlice_apply_coe, lowerOrderCLM_apply]
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simp [derivativeSliceIndex]
  · simp [derivativeSliceIndex, derivIndexOfList_singleton]

/-! ## Derivative words with arbitrary remaining order -/

section DerivativeWord

variable {r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/--
The order-`m` coordinate representing the derivative obtained by first
applying the word `α` and then an order-at-most-`r` multi-index.
-/
def derivativeWordIndex (α : List (Fin n)) (hα : α.length + r ≤ m)
    (a : DerivIndex n r) : DerivIndex n m :=
  derivIndexOfList (n := n) (k := m) (α ++ a.toList) (by
    rw [List.length_append]
    exact (Nat.add_le_add_left a.toList_length_le α.length).trans hα)

/-- A derivative-word index represents its prefix followed by the remaining
multi-index, up to the ordering chosen for the symmetric multi-index. -/
theorem derivativeWordIndex_toList_perm
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (a : DerivIndex n r) :
    (derivativeWordIndex (n := n) (m := m) (r := r) α hα a).toList.Perm
      (α ++ a.toList) := by
  exact derivIndexOfList_toList_perm _ _

/--
Derivative-word indices agree whenever their full derivative words differ
only by a permutation.
-/
theorem derivativeWordIndex_eq_of_perm
    {s : ℕ}
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (a : DerivIndex n r)
    (β : List (Fin n)) (hβ : β.length + s ≤ m)
    (b : DerivIndex n s)
    (hperm : (α ++ a.toList).Perm (β ++ b.toList)) :
    derivativeWordIndex (n := n) (m := m) (r := r) α hα a =
      derivativeWordIndex (n := n) (m := m) (r := s) β hβ b := by
  unfold derivativeWordIndex
  apply derivIndexOfList_eq_of_perm
  exact hperm

/-- Prefixing by the empty word canonically embeds a lower-order derivative
coordinate into the larger Sobolev bundle. -/
@[simp]
theorem derivativeWordIndex_nil
    (h : ([] : List (Fin n)).length + r ≤ m)
    (a : DerivIndex n r) :
    derivativeWordIndex (n := n) (m := m) (r := r) [] h a =
      derivIndexOfList (n := n) (k := m) a.toList (by
        exact a.toList_length_le.trans (by simpa using h)) := by
  rfl

/-- The base coordinate after prefixing by `α` is the canonical coordinate
for the word `α`. -/
@[simp]
theorem derivativeWordIndex_baseIndex
    (α : List (Fin n)) (hα : α.length + r ≤ m) :
    derivativeWordIndex (n := n) (m := m) (r := r) α hα
        (baseIndex n r) =
      derivIndexOfList (n := n) (k := m) α (by omega) := by
  simp [derivativeWordIndex]

/--
Using the derivative word of a canonical index as a prefix and taking the
base remaining coordinate only enlarges the ambient order bound.
-/
@[simp 1100]
theorem derivativeWordIndex_toList_baseIndex
    (a : DerivIndex n m) (r : ℕ) :
    derivativeWordIndex (n := n) (m := m + r) (r := r) a.toList
        (Nat.add_le_add_right a.toList_length_le r) (baseIndex n r) =
      a.castOrder (Nat.le_add_right m r) := by
  rw [derivativeWordIndex_baseIndex]
  simpa using
    derivIndexOfList_toList
      (a.castOrder (Nat.le_add_right m r))
      (a.castOrder (Nat.le_add_right m r)).toList_length_le

/-- Prefixing a canonical first derivative appends its coordinate direction
to the derivative word. -/
@[simp]
theorem derivativeWordIndex_firstDerivIndex
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (hr : 0 < r) (i : Fin n) :
    derivativeWordIndex (n := n) (m := m) (r := r) α hα
        (firstDerivIndex n r hr i) =
      derivIndexOfList (n := n) (k := m) (α ++ [i]) (by
        have hsingle : α.length + 1 ≤ m :=
          (Nat.add_le_add_left (Nat.succ_le_iff.mpr hr) α.length).trans hα
        simpa using hsingle) := by
  simp [derivativeWordIndex]

/-- At order one, prefixing the standard singleton derivative coordinate
appends that singleton to the derivative word. -/
@[simp]
theorem derivativeWordIndex_singleDerivIndex
    (α : List (Fin n)) (hα : α.length + 1 ≤ m) (i : Fin n) :
    derivativeWordIndex (n := n) (m := m) (r := 1) α hα
        (singleDerivIndex n i) =
      derivIndexOfList (n := n) (k := m) (α ++ [i]) (by
        simpa using hα) := by
  simp [derivativeWordIndex]

/--
Moving one final derivative direction from the prefix into the remaining
index does not change the represented mixed partial.
-/
theorem derivativeWordIndex_append_singleton_baseIndex
    (α : List (Fin n)) (i : Fin n)
    (hα : α.length + r ≤ m)
    (hαi : (α ++ [i]).length + r ≤ m)
    (hr : 0 < r) :
    derivativeWordIndex (n := n) (m := m) (r := r)
        (α ++ [i]) hαi (baseIndex n r) =
      derivativeWordIndex (n := n) (m := m) (r := r)
        α hα (firstDerivIndex n r hr i) := by
  apply derivativeWordIndex_eq_of_perm
  simp

/-- Mixed first derivatives commute at the level of derivative-word
coordinates. -/
theorem derivativeWordIndex_singleDerivIndex_comm
    (i j : Fin n) (hm : 2 ≤ m) :
    derivativeWordIndex (n := n) (m := m) (r := 1)
        [i] (by simpa using hm) (singleDerivIndex n j) =
      derivativeWordIndex (n := n) (m := m) (r := 1)
        [j] (by simpa using hm) (singleDerivIndex n i) := by
  apply derivativeWordIndex_eq_of_perm
  simpa using List.Perm.swap j i []

/-- A singleton prefix of a base coordinate is the canonical first
derivative coordinate in the larger bundle. -/
@[simp 1100]
theorem derivativeWordIndex_singleton_baseIndex
    (i : Fin n) (h : [i].length + r ≤ m) :
    derivativeWordIndex (n := n) (m := m) (r := r) [i] h
        (baseIndex n r) =
      firstDerivIndex n m (by
        have hm : 1 + r ≤ m := by simpa using h
        omega) i := by
  simp [firstDerivIndex]

/-- Prefixing every derivative index by the same word is injective. -/
theorem derivativeWordIndex_injective
    (α : List (Fin n)) (hα : α.length + r ≤ m) :
    Function.Injective (derivativeWordIndex (n := n) α hα) := by
  intro a b hab
  have hrows :
      (a.toList : Multiset (Fin n)) =
        (b.toList : Multiset (Fin n)) := by
    have hfull := congrArg
      (fun c : DerivIndex n m ↦ c.2.1) hab
    change
      (α : Multiset (Fin n)) + (a.toList : Multiset (Fin n)) =
        (α : Multiset (Fin n)) + (b.toList : Multiset (Fin n)) at hfull
    exact Multiset.add_right_inj.mp hfull
  have hord : a.1 = b.1 := by
    apply Fin.ext
    rw [← DerivIndex.toList_length (a := a),
      ← DerivIndex.toList_length (a := b)]
    exact congrArg Multiset.card hrows
  apply Sigma.ext hord
  have hpq : ∀ s : Multiset (Fin n),
      Multiset.card s = a.1.1 ↔ Multiset.card s = b.1.1 := by
    intro s
    rw [congrArg Fin.val hord]
  exact (Subtype.heq_iff_coe_eq hpq).2 (by
    simpa [DerivIndex.toList] using hrows)

/--
Cancel an arbitrary common derivative prefix inside a Sobolev bundle.

If the bundle contains both `D^α u` and `D^(α ++ β) u`, then the latter is
the weak `β` derivative of the former.  This iterates the one-coordinate
cancellation theorem and is the analytic core of higher-order derivative
extraction.
-/
theorem IsWkpOn.hasWeakDerivativeOn_from_coordinate
    {U : WkpAmbientOn n m p Ω}
    (hU : IsWkpOn (n := n) (k := m) (p := p) (Ω := Ω) U)
    (α β : List (Fin n)) (hαβ : α.length + β.length ≤ m) :
    HasWeakDerivativeOn (n := n) Ω β
      (U (derivIndexOfList (n := n) (k := m) α (by omega)))
      (U (derivIndexOfList (n := n) (k := m) (α ++ β) (by
        simpa [List.length_append] using hαβ))) := by
  let bα : DerivIndex n m := derivIndexOfList α (by omega)
  have hreverse : ∀ (γ : List (Fin n)) (hγ : α.length + γ.length ≤ m),
      HasWeakDerivativeOn Ω γ.reverse (U bα)
        (U (derivIndexOfList (α ++ γ.reverse) (by simpa [List.length_append] using hγ))) := by
    intro γ hγ
    induction γ with
    | nil =>
      simpa [bα] using hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain (Lp.memLp (U bα)) (Fact.out : (1 : ℝ≥0∞) ≤ p))
    | cons i rest ih =>
      have hrest : α.length + rest.length ≤ m := by
        simp only [List.length_cons] at hγ
        omega
      have hlen : (α ++ rest.reverse ++ [i]).length ≤ m := by
        simp only [List.length_append, List.length_reverse, List.length_singleton]
        omega
      have hlen' : (α ++ rest.reverse).length ≤ m := by simpa [List.length_append] using hrest
      let bprefix : DerivIndex n m := derivIndexOfList (α ++ rest.reverse) hlen'
      let bnext : DerivIndex n m := derivIndexOfList (α ++ rest.reverse ++ [i]) hlen
      have hprefix : HasWeakDerivativeOn Ω (α ++ rest.reverse) (U (baseIndex n m))
          (U bprefix) := by
        simpa [bprefix] using hU.hasWeakDerivativeOn_list _ hlen'
      have hnext : HasWeakDerivativeOn Ω (α ++ rest.reverse ++ [i]) (U (baseIndex n m))
          (U bnext) := by
        simpa [bnext] using hU.hasWeakDerivativeOn_list _ hlen
      have hprefixWord : HasWeakDerivativeOn Ω rest.reverse (U bα) (U bprefix) := by
        simpa [bprefix] using ih hrest
      simpa [List.reverse_cons, bnext] using
        hprefixWord.append_single i (hprefix.cancel_prefix_append_single i hnext)
  simpa [bα] using hreverse β.reverse (by simpa using hαβ)

/--
Append every derivative in a Sobolev bundle to an already-certified weak
derivative word.

If `D^α f` is the base coordinate of `V ∈ W^{m,p}`, then the `β` coordinate
of `V` represents `D^(α ++ β) f`.
-/
theorem HasWeakDerivativeOn.append_from_wkp
    {f : ℝ^n → ℝ} (V : W^{m,p}(Ω))
    (α β : List (Fin n)) (hβ : β.length ≤ m)
    (hbase : HasWeakDerivativeOn (n := n) Ω α f
      ((V : WkpAmbientOn n m p Ω) (baseIndex n m) : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) Ω (α ++ β) f
      ((V : WkpAmbientOn n m p Ω)
        (derivIndexOfList (n := n) (k := m) β hβ) : ℝ^n → ℝ) := by
  have hreverse : ∀ (γ : List (Fin n)) (hγ : γ.length ≤ m),
      HasWeakDerivativeOn Ω (α ++ γ.reverse) f ((V : WkpAmbientOn n m p Ω)
        (derivIndexOfList γ.reverse (by simpa using hγ)) : ℝ^n → ℝ) := by
    intro γ hγ
    induction γ with
    | nil => simpa [derivIndexOfList, baseIndex] using hbase
    | cons i rest ih =>
      have hrest : rest.length ≤ m := by
        simp only [List.length_cons] at hγ
        omega
      have hstep := V.property.hasWeakDerivativeOn_from_coordinate rest.reverse [i] (by
        simp only [List.length_reverse, List.length_singleton]
        omega)
      simpa [List.reverse_cons, List.length_append] using (ih hrest).append_single i hstep
  simpa using hreverse β.reverse (by simpa using hβ)

private noncomputable def succOrderRow
    (U : W^{m,p}(Ω))
    (V : Fin n → W^{m,p}(Ω))
    (a : DerivIndex n (m + 1)) :
    DerivLp n p Ω :=
  if ha : a.toList.length ≤ m then
    (U : WkpAmbientOn n m p Ω)
      (derivIndexOfList (n := n) (k := m) a.toList ha)
  else
    let hne : a.toList ≠ [] := by
      intro hnil
      apply ha
      simp [hnil]
    (V (a.toList.head hne) : WkpAmbientOn n m p Ω)
      (derivIndexOfList (n := n) (k := m) a.toList.tail (by
        have htotal : a.toList.length ≤ m + 1 := a.toList_length_le
        have hpos : 0 < a.toList.length := List.length_pos_iff.mpr hne
        simp only [List.length_tail]
        omega))

omit [Fact (1 ≤ p)] in
private theorem succOrderRow_baseIndex (U : W^{m,p}(Ω)) (V : Fin n → W^{m,p}(Ω)) :
    succOrderRow U V (baseIndex n (m + 1)) = (U : WkpAmbientOn n m p Ω) (baseIndex n m) := by
  have hindex : derivIndexOfList (n := n) (k := m) [] (by simp) = baseIndex n m := rfl
  unfold succOrderRow
  rw [dite_eq_left (by simp)]
  simp [hindex]

private noncomputable def succOrderAssembly
    (hm : 0 < m) (U : W^{m,p}(Ω))
    (V : Fin n → W^{m,p}(Ω))
    (hV : ∀ i,
      ((V i : WkpAmbientOn n m p Ω) (baseIndex n m) :
          DerivLp n p Ω) =
        ((U : WkpAmbientOn n m p Ω)
          (firstDerivIndex n m hm i) : DerivLp n p Ω)) :
    {W : W^{m + 1,p}(Ω) //
      ∀ a : DerivIndex n (m + 1),
        ((W : WkpAmbientOn n (m + 1) p Ω) a :
            DerivLp n p Ω) =
          succOrderRow (n := n) (Ω := Ω) U V a} := by
  classical
  let f : ℝ^n → ℝ := ((U : WkpAmbientOn n m p Ω) (baseIndex n m) : DerivLp n p Ω)
  let d : DerivIndex n (m + 1) → ℝ^n → ℝ := fun a ↦ (succOrderRow U V a : ℝ^n → ℝ)
  have hbase : d (baseIndex n (m + 1)) = f :=
    congrArg (fun g : DerivLp n p Ω ↦ (g : ℝ^n → ℝ)) (succOrderRow_baseIndex U V)
  have hweak (a : DerivIndex n (m + 1)) : HasWeakDerivativeOn Ω a.toList f (d a) := by
    by_cases ha : a.toList.length ≤ m
    · have hda : d a = (U : WkpAmbientOn n m p Ω) (derivIndexOfList a.toList ha) := by
        change ((succOrderRow U V a : DerivLp n p Ω) : ℝ^n → ℝ) = _
        unfold succOrderRow
        rw [dite_eq_left ha]
      rw [hda]
      simpa [f] using U.property.hasWeakDerivativeOn_list a.toList ha
    · cases hlist : a.toList with
      | nil => exact (ha (by simp [hlist])).elim
      | cons i rest =>
        have hrest : rest.length ≤ m := by
          have := a.toList_length_le
          simp only [hlist, List.length_cons] at this
          omega
        have hfirstV : HasWeakDerivativeOn Ω [i] f
            ((V i : WkpAmbientOn n m p Ω) (baseIndex n m) : ℝ^n → ℝ) := by
          rw [hV i]
          simpa [f] using U.property.hasWeakDerivativeOn_first hm i
        have hda : d a = (V i : WkpAmbientOn n m p Ω) (derivIndexOfList rest hrest) := by
          change ((succOrderRow U V a : DerivLp n p Ω) : ℝ^n → ℝ) = _
          unfold succOrderRow
          rw [dite_eq_right ha]
          simp [hlist]
        rw [hda]
        simpa [hlist, f] using HasWeakDerivativeOn.append_from_wkp (V i) [i] rest hrest hfirstV
  have hmem (a : DerivIndex n (m + 1)) : MemLp (d a) p (domainMeasure n Ω) := Lp.memLp _
  refine ⟨mkWkpSpaceOnOfWeakDerivatives f d hbase hmem hweak, fun a ↦ Lp.ext ?_⟩
  simpa [d] using mkWkpSpaceOnOfWeakDerivatives_apply_ae f d hbase hmem hweak a

/--
Assemble one additional Sobolev order from compatible first derivatives.

Given `U ∈ W^{m,p}` and, for every coordinate `i`, a bundle
`V i ∈ W^{m,p}` whose base is the first derivative `DᵢU`, all derivative
rows combine into a single element of `W^{m+1,p}` with the same base
function as `U`.
-/
theorem exists_succOrder_of_firstDerivatives
    (hm : 0 < m) (U : W^{m,p}(Ω))
    (V : Fin n → W^{m,p}(Ω))
    (hV : ∀ i,
      ((V i : WkpAmbientOn n m p Ω) (baseIndex n m) :
          DerivLp n p Ω) =
        ((U : WkpAmbientOn n m p Ω)
          (firstDerivIndex n m hm i) : DerivLp n p Ω)) :
    ∃ W : W^{m + 1,p}(Ω),
      ⇑((W : WkpAmbientOn n (m + 1) p Ω)
          (baseIndex n (m + 1)) : DerivLp n p Ω)
        =ᵐ[domainMeasure n Ω]
          ⇑((U : WkpAmbientOn n m p Ω)
            (baseIndex n m) : DerivLp n p Ω) := by
  obtain ⟨W, hW⟩ := succOrderAssembly hm U V hV
  exact ⟨W, by rw [hW, succOrderRow_baseIndex]⟩

/--
The dimension-dependent loss in the elementary successor-order assembly
estimate.  The estimate treats every order-`m+1` derivative row uniformly.
-/
noncomputable def succOrderAssemblyNormBound (n m : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (DerivIndex n (m + 1)))

/-- The successor-order assembly bound is nonnegative. -/
theorem succOrderAssemblyNormBound_nonneg :
    0 ≤ succOrderAssemblyNormBound n m := by
  unfold succOrderAssemblyNormBound
  positivity

/--
Quantitative `L²` successor-order assembly.

The assembled graph norm is bounded by the square root of the number of
order-`m+1` derivative rows times the sum of the input graph norms.
-/
theorem exists_succOrder_of_firstDerivatives_with_norm
    (hm : 0 < m) (U : W^{m,2}(Ω))
    (V : Fin n → W^{m,2}(Ω))
    (hV : ∀ i,
      ((V i : WkpAmbientOn n m 2 Ω) (baseIndex n m) :
          DerivLp n 2 Ω) =
        ((U : WkpAmbientOn n m 2 Ω)
          (firstDerivIndex n m hm i) : DerivLp n 2 Ω)) :
    ∃ W : W^{m + 1,2}(Ω),
      (⇑((W : WkpAmbientOn n (m + 1) 2 Ω)
            (baseIndex n (m + 1)) : DerivLp n 2 Ω)
          =ᵐ[domainMeasure n Ω]
            ⇑((U : WkpAmbientOn n m 2 Ω)
              (baseIndex n m) : DerivLp n 2 Ω)) ∧
        ‖W‖ ≤ succOrderAssemblyNormBound n m *
          (‖U‖ + ∑ i, ‖V i‖) := by
  classical
  obtain ⟨W, hW⟩ := succOrderAssembly hm U V hV
  have hC : 0 ≤ ‖U‖ + ∑ i, ‖V i‖ := by positivity
  have hrow (a : DerivIndex n (m + 1)) :
      ‖(W : WkpAmbientOn n (m + 1) 2 Ω) a‖ ≤ ‖U‖ + ∑ i, ‖V i‖ := by
    rw [hW a]
    unfold succOrderRow
    split
    · exact (PiLp.norm_apply_le (U : WkpAmbientOn n m 2 Ω) _).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
    · exact (PiLp.norm_apply_le ((V _ : W^{m,2}(Ω)) : WkpAmbientOn n m 2 Ω) _).trans
        ((Finset.single_le_sum (fun j _ ↦ norm_nonneg (V j)) (Finset.mem_univ _)).trans
          (le_add_of_nonneg_left (norm_nonneg U)))
  refine ⟨W, by rw [hW, succOrderRow_baseIndex], ?_⟩
  change ‖(W : WkpAmbientOn n (m + 1) 2 Ω)‖ ≤ _
  rw [PiLp.norm_eq_of_L2, succOrderAssemblyNormBound, ← Real.sqrt_sq hC,
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ((Finset.sum_le_card_nsmul _ _ _ fun a _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (hrow a) 2).trans_eq ?_)
  rw [Finset.card_univ, nsmul_eq_mul]

/-- Coordinates of the ambient derivative-word extraction: the `a`-th coordinate
of `D^α U` is the `α`-prefixed coordinate of `U`. -/
noncomputable def derivativeWordAmbientPi
    (α : List (Fin n)) (hα : α.length + r ≤ m) :
    (∀ _ : DerivIndex n m, DerivLp n p Ω) →L[ℝ]
      (∀ _ : DerivIndex n r, DerivLp n p Ω) :=
  ContinuousLinearMap.pi fun a ↦
    ContinuousLinearMap.proj (derivativeWordIndex (n := n) α hα a)

/-- Ambient derivative-word extraction `D^α` from order `m` to order `r`, as a
continuous linear map between the `PiLp` bundles. -/
noncomputable def derivativeWordAmbient
    (α : List (Fin n)) (hα : α.length + r ≤ m) :
    WkpAmbientOn n m p Ω →L[ℝ] WkpAmbientOn n r p Ω := by
  classical
  let eHigh := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n m ↦ DerivLp n p Ω)
  let eLow := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n r ↦ DerivLp n p Ω)
  exact eLow.symm.toContinuousLinearMap.comp
    ((derivativeWordAmbientPi (n := n) (Ω := Ω) α hα).comp
      eHigh.toContinuousLinearMap)

private theorem derivativeWordAmbient_apply
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : WkpAmbientOn n m p Ω) (a : DerivIndex n r) :
    derivativeWordAmbient (n := n) (Ω := Ω) α hα U a =
      U (derivativeWordIndex (n := n) α hα a) := by
  classical
  simp [derivativeWordAmbient, derivativeWordAmbientPi]

/-- Extracting a derivative word contracts the ambient Sobolev bundle. -/
private theorem norm_derivativeWordAmbient_apply_le
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : WkpAmbientOn n m p Ω) :
    ‖derivativeWordAmbient (n := n) (Ω := Ω) α hα U‖ ≤ ‖U‖ := by
  apply PiLp.norm_mono_of_injective
    (derivativeWordIndex (n := n) α hα) (derivativeWordIndex_injective α hα)
  intro a
  exact le_of_eq (congrArg norm (derivativeWordAmbient_apply α hα U a))

/-- Ambient derivative-word extraction preserves the weak-derivative graph
relations. -/
theorem derivativeWordAmbient_mapsIsWkpOn
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : WkpAmbientOn n m p Ω)
    (hU : IsWkpOn (n := n) (k := m) (p := p) (Ω := Ω) U) :
    IsWkpOn (n := n) (k := r) (p := p) (Ω := Ω)
      (derivativeWordAmbient (n := n) (Ω := Ω) α hα U) := by
  intro a
  rw [derivativeWordAmbient_apply, derivativeWordAmbient_apply]
  simpa [derivativeWordIndex] using
    hU.hasWeakDerivativeOn_from_coordinate α a.toList (by
      exact (Nat.add_le_add_left
        a.toList_length_le α.length).trans hα)

/--
Bounded extraction of `D^α U` with all of its weak derivatives through
order `r`:

`W^{m,p}(Ω) →L W^{r,p}(Ω)`, provided `|α| + r ≤ m`.
-/
noncomputable def derivativeWordCLM
    (α : List (Fin n)) (hα : α.length + r ≤ m) :
    W^{m,p}(Ω) →L[ℝ] W^{r,p}(Ω) :=
  ContinuousLinearMap.codRestrict
    ((derivativeWordAmbient (n := n) (Ω := Ω) α hα).comp
      (Submodule.subtypeL (wkpSubmoduleOn n m p Ω)))
    (wkpSubmoduleOn n r p Ω)
    (fun U ↦ derivativeWordAmbient_mapsIsWkpOn
      (n := n) (m := m) (r := r) (p := p) (Ω := Ω) α hα
      (U : WkpAmbientOn n m p Ω) U.property)

/-- Every coordinate of `D^α U` is the `α`-prefixed coordinate of `U`. -/
@[simp]
theorem derivativeWordCLM_apply
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : W^{m,p}(Ω)) (a : DerivIndex n r) :
    ((derivativeWordCLM (n := n) (Ω := Ω) α hα U :
        W^{r,p}(Ω)) : WkpAmbientOn n r p Ω) a =
      (U : WkpAmbientOn n m p Ω)
        (derivativeWordIndex (n := n) α hα a) :=
  derivativeWordAmbient_apply (n := n) (Ω := Ω) α hα
    (U : WkpAmbientOn n m p Ω) a

/-- Extracting the empty derivative word is exactly Sobolev order
restriction. -/
@[simp]
theorem derivativeWordCLM_nil_apply
    (h : ([] : List (Fin n)).length + r ≤ m)
    (U : W^{m,p}(Ω)) :
    derivativeWordCLM (n := n) (Ω := Ω) [] h U =
      lowerOrderCLM (n := n) (p := p) (Ω := Ω) (by simpa using h) U := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  rw [derivativeWordCLM_apply, lowerOrderCLM_apply]
  apply congrArg fun b : DerivIndex n m ↦
    (U : WkpAmbientOn n m p Ω) b
  rw [derivativeWordIndex_nil]
  exact derivIndexOfList_toList
    (a.castOrder (by simpa using h))
    (a.castOrder (by simpa using h)).toList_length_le

/-- The canonical base representative of `D^α U` is the `α` coordinate of
the original Sobolev bundle. -/
theorem baseRepresentative_derivativeWordCLM
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : W^{m,p}(Ω)) :
    baseRepresentative
        (derivativeWordCLM (n := n) (Ω := Ω) α hα U) =
      (((U : WkpAmbientOn n m p Ω)
        (derivIndexOfList (n := n) (k := m) α (by omega)) :
          DerivLp n p Ω) : ℝ^n → ℝ) := by
  funext x
  simp only [baseRepresentative, derivativeWordCLM_apply,
    derivativeWordIndex_baseIndex]

/-- Derivative-word extraction is contractive in the Sobolev graph norm. -/
theorem norm_derivativeWordCLM_apply_le
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : W^{m,p}(Ω)) :
    ‖derivativeWordCLM (n := n) (Ω := Ω) α hα U‖ ≤ ‖U‖ := by
  exact norm_derivativeWordAmbient_apply_le
    (n := n) (Ω := Ω) α hα (U : WkpAmbientOn n m p Ω)

/--
Successive derivative-word extractions agree coordinatewise with extraction
by the concatenated word.
-/
theorem derivativeWordCLM_comp_apply
    {s : ℕ} (α : List (Fin n)) (hα : α.length + s ≤ m)
    (β : List (Fin n)) (hβ : β.length + r ≤ s)
    (hαβ : (α ++ β).length + r ≤ m)
    (U : W^{m,p}(Ω)) (a : DerivIndex n r) :
    ((derivativeWordCLM (n := n) (Ω := Ω) β hβ
          (derivativeWordCLM (n := n) (Ω := Ω) α hα U) :
        W^{r,p}(Ω)) : WkpAmbientOn n r p Ω) a =
      ((derivativeWordCLM (n := n) (Ω := Ω) (α ++ β) hαβ U :
          W^{r,p}(Ω)) : WkpAmbientOn n r p Ω) a := by
  rw [derivativeWordCLM_apply, derivativeWordCLM_apply,
    derivativeWordCLM_apply]
  apply congrArg (fun b : DerivIndex n m ↦
    (U : WkpAmbientOn n m p Ω) b)
  apply derivativeWordIndex_eq_of_perm
  simpa [List.append_assoc] using
    List.Perm.append_left α
      (derivativeWordIndex_toList_perm
        (n := n) (m := s) (r := r) β hβ a)

/--
Successive derivative-word extractions are the same Sobolev element as
extraction by the concatenated word.
-/
theorem derivativeWordCLM_comp
    {s : ℕ} (α : List (Fin n)) (hα : α.length + s ≤ m)
    (β : List (Fin n)) (hβ : β.length + r ≤ s)
    (hαβ : (α ++ β).length + r ≤ m)
    (U : W^{m,p}(Ω)) :
    derivativeWordCLM (n := n) (Ω := Ω) β hβ
        (derivativeWordCLM (n := n) (Ω := Ω) α hα U) =
      derivativeWordCLM (n := n) (Ω := Ω) (α ++ β) hαβ U := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  exact derivativeWordCLM_comp_apply
    (n := n) (Ω := Ω) α hα β hβ hαβ U a

/-- Forgetting output coordinates of a derivative slice gives the same slice
with the lower remaining Sobolev order. -/
theorem lowerOrderCLM_derivativeWordCLM_apply
    {s : ℕ} (hrs : r ≤ s)
    (α : List (Fin n)) (hα : α.length + s ≤ m)
    (U : W^{m,p}(Ω)) :
    lowerOrderCLM (n := n) (p := p) (Ω := Ω) hrs
        (derivativeWordCLM (n := n) (Ω := Ω) α hα U) =
      derivativeWordCLM (n := n) (Ω := Ω) α
        ((Nat.add_le_add_left hrs α.length).trans hα) U := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  simp only [lowerOrderCLM_apply, derivativeWordCLM_apply, derivativeWordIndex,
    DerivIndex.castOrder_toList]

/--
Derivative-word extraction commutes with forgetting unused higher-order
coordinates.
-/
theorem derivativeWordCLM_lowerOrderCLM_apply
    {s : ℕ} (hsm : s ≤ m)
    (α : List (Fin n)) (hα : α.length + r ≤ s)
    (U : W^{m,p}(Ω)) :
    derivativeWordCLM (n := n) (m := s) (Ω := Ω) α hα
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hsm U) =
      derivativeWordCLM (n := n) (m := m) (Ω := Ω) α
        (hα.trans hsm) U := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  rw [derivativeWordCLM_apply, derivativeWordCLM_apply, lowerOrderCLM_apply]
  rfl

/--
Restricting the domain commutes with extracting a derivative word.
-/
theorem restrictCLM_derivativeWordCLM_apply
    {Ωsmall : Set (ℝ^n)}
    (hΩsmall : MeasurableSet Ωsmall)
    (hsub : Ωsmall ⊆ Ω)
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : W^{m,p}(Ω)) :
    restrictCLM
        (n := n) (k := r) (p := p) hΩsmall hsub
        (derivativeWordCLM (n := n) (Ω := Ω) α hα U) =
      derivativeWordCLM (n := n) (Ω := Ωsmall) α hα
        (restrictCLM
          (n := n) (k := m) (p := p) hΩsmall hsub U) := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  simp only [restrictCLM_apply_coe, restrictAmbient_apply,
    derivativeWordCLM_apply]

/--
Domain restriction and derivative-word extraction commute as continuous
linear maps.
-/
theorem restrictCLM_derivativeWordCLM
    {Ωsmall : Set (ℝ^n)}
    (hΩsmall : MeasurableSet Ωsmall)
    (hsub : Ωsmall ⊆ Ω)
    (α : List (Fin n)) (hα : α.length + r ≤ m) :
    (restrictCLM
        (n := n) (k := r) (p := p) hΩsmall hsub).comp
        (derivativeWordCLM (n := n) (Ω := Ω) α hα) =
      (derivativeWordCLM (n := n) (Ω := Ωsmall) α hα).comp
        (restrictCLM
          (n := n) (k := m) (p := p) hΩsmall hsub) := by
  apply ContinuousLinearMap.ext
  exact restrictCLM_derivativeWordCLM_apply hΩsmall hsub α hα

end DerivativeWord

end GraphSpace
end SobolevSpace
