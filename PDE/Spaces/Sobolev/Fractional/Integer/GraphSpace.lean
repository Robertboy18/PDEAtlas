/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.WeakDerivative
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# From the fractional scale into the integer-order graph space

For a natural number `k`, an element of `H^k(ℝ^n)` with a real `L²` representative
determines a point of the integer-order graph space
`SobolevSpace.GraphSpace.WkpSpaceOn n k 2 Set.univ`: the tuple of real
representatives of its derivatives along every derivative word of order at most
`k`.

The weak derivatives come from `Fractional.WholeSpace.WeakDerivative`, and we assemble them
into a tuple. The inverse map and the linear equivalence are in
`Fractional.Integer.Reverse`, and the two-sided norm bounds that make it a continuous linear
equivalence are in `Fractional.Integer.NormComparison`. Together they give the classical
statement that, for integer `k`, the Bessel-potential space
`H^k(ℝ^n) = {u : (1 + |ξ|²)^{k/2} û ∈ L²}` coincides with the Sobolev space `W^{k,2}(ℝ^n)`
defined through weak derivatives (Evans, PDE, §5.8.5, Theorem 8, with the equivalent weight
`1 + |y|^k`).

## Main results

* `toDerivLp`, `coeFn_toDerivLp`: a complex `L²` function with real values, viewed as a
  real `L²` coordinate.
* `graphTuple`, `graphTuple_baseIndex`, `isWkpOn_graphTuple`: the tuple of weak derivatives
  and the proof that it satisfies the graph-space compatibility conditions.
* `graphTuple_apply_of_hasWeakDerivativeOn`, `graphTuple_apply_eq`,
  `hasWeakDerivativeOn_graphTuple`: each coordinate is the (unique) weak derivative along its
  word.
* `toWkpSpace`, `toWkpSpace_add`, `toWkpSpace_smul`, `toWkpSpaceLinear`: the bridge as a map
  and as an `ℝ`-linear map on the real subspace `HsSpaceReal n k`.

## Implementation notes

`IsWkpOn` quantifies over `a : DerivIndex n k` and tests the word `a.toList`, so no
commutativity of mixed partials is needed. The tuple is defined by a case split on
`a.toList = []`, which makes `U (baseIndex n k)` the representative of `u` by definition;
uniqueness of weak derivatives enters only in `graphTuple_apply_of_hasWeakDerivativeOn`.

The hypothesis `IsRealL2 (toL2Fun _ u)` is realness of the function representative. For
nonnegative order, `Fractional.WholeSpace.Conjugation` proves that it agrees with membership in
`hsRealSubmodule`, which is defined through the Bessel representative `toLp u`. Every
real-valued Schwartz function satisfies it (`isRealL2_ofSchwartz`, `toL2Fun_ofSchwartz`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298, and step 2 of its proof,
  p. 298: if `(1 + |y|^k)û ∈ L²`, then `((iy)^α û)^∨` is the weak derivative `D^α u` for `|α| ≤ k`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped BesselPotentialSpace ENNReal

namespace SobolevSpace.Fractional

variable {n k : ℕ}

open BesselPotentialSpace

/-- The derivative along a word, as an `L²` function rather than an element of the
fractional scale.  A restatement of `exists_hasWeakDerivativeOn_list` that drops
the order, which the graph space does not need. -/
theorem exists_l2_hasWeakDerivativeOn_list (α : List (Fin n)) {s : ℝ}
    (h0 : (0 : ℝ) ≤ s) (hlen : (α.length : ℝ) ≤ s) (u : H^{s}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) :
    ∃ g : Lp ℂ 2 (volume : Measure (ℝ^n)),
      HasWeakDerivativeOn (n := n) Set.univ α
        (reOfL2 (toL2Fun h0 u)) (reOfL2 g) := by
  obtain ⟨t, ht, v, _, _, hweak⟩ :=
    exists_hasWeakDerivativeOn_list α h0 hlen u hu
  exact ⟨toL2Fun ht v, hweak⟩

/-- Every real `L²` function is a member of `L²` against the domain measure of
`Set.univ`. -/
theorem memLp_reOfL2_univ (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    MemLp (reOfL2 g) 2 (domainMeasure n (Set.univ : Set (ℝ^n))) := by
  have h : MemLp (reOfL2 g) 2 (volume : Measure (ℝ^n)) := (Lp.memLp g).re
  simpa [domainMeasure] using h

/-- An `L²` function viewed as a coordinate of the graph space. -/
noncomputable def toDerivLp (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    DerivLp n 2 (Set.univ : Set (ℝ^n)) :=
  MemLp.toLp (reOfL2 g) (memLp_reOfL2_univ g)

/-- The graph-space coordinate built from `g` is represented a.e. by the real part of `g`. -/
theorem coeFn_toDerivLp (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ((toDerivLp g : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))] reOfL2 g :=
  MemLp.coeFn_toLp _

/-- The graph-space tuple attached to an element of `H^k(ℝ^n)`.

The base coordinate is the representative of `u` itself, by construction. -/
noncomputable def graphTuple (h0 : (0 : ℝ) ≤ (k : ℝ)) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) : WkpAmbientOn n k 2 (Set.univ : Set (ℝ^n)) :=
  WithLp.toLp 2 (fun a : DerivIndex n k ↦
    if a.toList = [] then toDerivLp (toL2Fun h0 u)
    else toDerivLp (Classical.choose
      (exists_l2_hasWeakDerivativeOn_list a.toList h0
        (by exact_mod_cast a.toList_length_le) u hu)))

/-- The base coordinate of the graph tuple is the representative of `u` itself; this holds by
construction (the `a.toList = []` branch) and needs no uniqueness of weak derivatives. -/
@[simp] theorem graphTuple_baseIndex (h0 : (0 : ℝ) ≤ (k : ℝ)) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) :
    graphTuple h0 u hu (baseIndex n k) = toDerivLp (toL2Fun h0 u) := by
  simp [graphTuple]

/-- The tuple satisfies the weak-derivative constraints of the graph space. -/
theorem isWkpOn_graphTuple (h0 : (0 : ℝ) ≤ (k : ℝ)) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) :
    IsWkpOn (n := n) (k := k) (p := 2) (Ω := Set.univ) (graphTuple h0 u hu) := by
  intro a
  rw [graphTuple_baseIndex]
  by_cases ha : a.toList = []
  · -- the word is empty: both coordinates are the representative of `u`
    have hcoord : graphTuple h0 u hu a = toDerivLp (toL2Fun h0 u) := by
      simp [graphTuple, ha]
    rw [hcoord, ha]
    exact (hasWeakDerivativeOn_congr_ae (coeFn_toDerivLp _).symm
      (coeFn_toDerivLp _).symm).mp (hasWeakDerivativeOn_nil _)
  · -- otherwise the coordinate is the chosen weak derivative
    have hspec := Classical.choose_spec
      (exists_l2_hasWeakDerivativeOn_list a.toList h0
        (by exact_mod_cast a.toList_length_le) u hu)
    have hcoord : graphTuple h0 u hu a = toDerivLp (Classical.choose
        (exists_l2_hasWeakDerivativeOn_list a.toList h0
          (by exact_mod_cast a.toList_length_le) u hu)) := by
      simp [graphTuple, ha]
    rw [hcoord]
    exact (hasWeakDerivativeOn_congr_ae (coeFn_toDerivLp _).symm
      (coeFn_toDerivLp _).symm).mp hspec

/-- The tuple coordinates are determined by the weak-derivative property, so the
`Classical.choose` in `graphTuple` is immaterial.

This uses uniqueness of weak derivatives on an open domain,
`SobolevSpace.HasWeakDerivativeOn.unique_ae`, together with the fact that the
coordinates live in `Lp`, i.e. are almost-everywhere classes. -/
theorem graphTuple_apply_of_hasWeakDerivativeOn (h0 : (0 : ℝ) ≤ (k : ℝ))
    (u : H^{(k : ℝ)}(ℝ^n)) (hu : IsRealL2 (toL2Fun h0 u))
    {a : DerivIndex n k} {g : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hg : HasWeakDerivativeOn (n := n) Set.univ a.toList
      (reOfL2 (toL2Fun h0 u)) (reOfL2 g)) :
    graphTuple h0 u hu a = toDerivLp g := by
  -- the coordinate itself is a weak derivative of the base representative
  have hbase := isWkpOn_graphTuple h0 u hu a
  rw [graphTuple_baseIndex] at hbase
  have hcoord : HasWeakDerivativeOn (n := n) Set.univ a.toList
      (reOfL2 (toL2Fun h0 u))
      ((graphTuple h0 u hu a : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ) :=
    (hasWeakDerivativeOn_congr_ae (coeFn_toDerivLp _) (Filter.EventuallyEq.refl _ _)).mp hbase
  -- uniqueness pins it down almost everywhere
  have hae := hcoord.unique_ae isOpen_univ hg
  refine Lp.ext_iff.mpr ?_
  exact hae.trans (coeFn_toDerivLp g).symm

/-- The coordinate characterisation, for an arbitrary graph-space element rather
than only one of the form `toDerivLp g`. -/
theorem graphTuple_apply_eq (h0 : (0 : ℝ) ≤ (k : ℝ)) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) {a : DerivIndex n k}
    {w : DerivLp n 2 (Set.univ : Set (ℝ^n))}
    (hw : HasWeakDerivativeOn (n := n) Set.univ a.toList
      (reOfL2 (toL2Fun h0 u)) ((w : ℝ^n → ℝ))) :
    graphTuple h0 u hu a = w := by
  have hbase := isWkpOn_graphTuple h0 u hu a
  rw [graphTuple_baseIndex] at hbase
  have hcoord : HasWeakDerivativeOn (n := n) Set.univ a.toList
      (reOfL2 (toL2Fun h0 u))
      ((graphTuple h0 u hu a : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ) :=
    (hasWeakDerivativeOn_congr_ae (coeFn_toDerivLp _) (Filter.EventuallyEq.refl _ _)).mp hbase
  exact Lp.ext_iff.mpr (hcoord.unique_ae isOpen_univ hw)

/-- The weak-derivative property of each coordinate, stated against the
representative of `u` rather than the base coordinate of the tuple. -/
theorem hasWeakDerivativeOn_graphTuple (h0 : (0 : ℝ) ≤ (k : ℝ))
    (u : H^{(k : ℝ)}(ℝ^n)) (hu : IsRealL2 (toL2Fun h0 u)) (a : DerivIndex n k) :
    HasWeakDerivativeOn (n := n) Set.univ a.toList (reOfL2 (toL2Fun h0 u))
      ((graphTuple h0 u hu a : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ) := by
  have hbase := isWkpOn_graphTuple h0 u hu a
  rw [graphTuple_baseIndex] at hbase
  exact (hasWeakDerivativeOn_congr_ae (coeFn_toDerivLp _) (Filter.EventuallyEq.refl _ _)).mp hbase

/-- The tuple attached to `c • u` is `c` times the tuple of `u`. -/
theorem graphTuple_smul (h0 : (0 : ℝ) ≤ (k : ℝ)) (c : ℝ) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u))
    (hcu : IsRealL2 (toL2Fun h0 ((c : ℂ) • u))) :
    graphTuple h0 ((c : ℂ) • u) hcu = c • graphTuple h0 u hu := by
  refine PiLp.ext fun a ↦ ?_
  refine graphTuple_apply_eq h0 ((c : ℂ) • u) hcu ?_
  have hbase : reOfL2 (toL2Fun h0 ((c : ℂ) • u))
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))] c • reOfL2 (toL2Fun h0 u) := by
    rw [toL2Fun_smul]
    simpa [domainMeasure] using reOfL2_smul_ae c (toL2Fun h0 u)
  have hcoord : ((c • graphTuple h0 u hu a :
        DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        c • ((graphTuple h0 u hu a : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ) :=
    Lp.coeFn_smul _ _
  refine (hasWeakDerivativeOn_congr_ae hbase.symm hcoord.symm).mp ?_
  exact hasWeakDerivativeOn_smul c (hasWeakDerivativeOn_graphTuple h0 u hu a)

/-- Realness of the representative is preserved by addition. -/
theorem isRealL2_toL2Fun_add (h0 : (0 : ℝ) ≤ (k : ℝ)) (u v : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) (hv : IsRealL2 (toL2Fun h0 v)) :
    IsRealL2 (toL2Fun h0 (u + v)) := by
  rw [toL2Fun_add]
  exact hu.add hv

/-- The tuple attached to `u + v` is the sum of the tuples. -/
theorem graphTuple_add (h0 : (0 : ℝ) ≤ (k : ℝ)) (u v : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) (hv : IsRealL2 (toL2Fun h0 v)) :
    graphTuple h0 (u + v) (isRealL2_toL2Fun_add h0 u v hu hv)
      = graphTuple h0 u hu + graphTuple h0 v hv := by
  refine PiLp.ext fun a ↦ ?_
  refine graphTuple_apply_eq h0 (u + v) (isRealL2_toL2Fun_add h0 u v hu hv) ?_
  -- the sum of the two coordinates is a weak derivative of the sum of the bases
  have hsum := hasWeakDerivativeOn_add
    (hasWeakDerivativeOn_graphTuple h0 u hu a) (hasWeakDerivativeOn_graphTuple h0 v hv a)
  -- transport along the two almost-everywhere identities
  have hbase : reOfL2 (toL2Fun h0 (u + v))
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        reOfL2 (toL2Fun h0 u) + reOfL2 (toL2Fun h0 v) := by
    rw [toL2Fun_add]
    simpa [domainMeasure] using reOfL2_add_ae (toL2Fun h0 u) (toL2Fun h0 v)
  have hcoord : ((graphTuple h0 u hu a + graphTuple h0 v hv a :
        DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        ((graphTuple h0 u hu a : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
          + ((graphTuple h0 v hv a : DerivLp n 2 (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ) :=
    Lp.coeFn_add _ _
  exact (hasWeakDerivativeOn_congr_ae hbase.symm hcoord.symm).mp hsum

/-- An `H^k` function with a real representative, as a point of the integer-order
graph space `W^{k,2}(ℝ^n)`. -/
noncomputable def toWkpSpace (h0 : (0 : ℝ) ≤ (k : ℝ)) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) : W^{k,2}((Set.univ : Set (ℝ^n))) :=
  ⟨graphTuple h0 u hu, isWkpOn_graphTuple h0 u hu⟩

/-- The ambient tuple underlying `toWkpSpace h0 u hu` is `graphTuple h0 u hu`. -/
@[simp] theorem toWkpSpace_coe (h0 : (0 : ℝ) ≤ (k : ℝ)) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) :
    ((toWkpSpace h0 u hu : W^{k,2}((Set.univ : Set (ℝ^n)))) :
        WkpAmbientOn n k 2 (Set.univ : Set (ℝ^n)))
      = graphTuple h0 u hu := rfl

/-- Additivity of the map into the graph space. -/
theorem toWkpSpace_add (h0 : (0 : ℝ) ≤ (k : ℝ)) (u v : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u)) (hv : IsRealL2 (toL2Fun h0 v)) :
    toWkpSpace h0 (u + v) (isRealL2_toL2Fun_add h0 u v hu hv)
      = toWkpSpace h0 u hu + toWkpSpace h0 v hv :=
  Subtype.ext (graphTuple_add h0 u v hu hv)

/-- Homogeneity of the map into the graph space. -/
theorem toWkpSpace_smul (h0 : (0 : ℝ) ≤ (k : ℝ)) (c : ℝ) (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun h0 u))
    (hcu : IsRealL2 (toL2Fun h0 ((c : ℂ) • u))) :
    toWkpSpace h0 ((c : ℂ) • u) hcu = c • toWkpSpace h0 u hu :=
  Subtype.ext (graphTuple_smul h0 c u hu hcu)

/-- The map into the integer-order graph space, as an `ℝ`-linear map.

On the canonical real subspace of `H^k`, passing to the tuple of weak
derivatives is `ℝ`-linear into the integer-order graph space.  The theorem
`HsSpaceReal.isRealL2_toL2Fun` supplies the physical-representative realness
required by `toWkpSpace`. -/
noncomputable def toWkpSpaceLinear (n k : ℕ) :
    HsSpaceReal n (k : ℝ)
      →ₗ[ℝ] W^{k,2}((Set.univ : Set (ℝ^n))) where
  toFun u :=
    toWkpSpace (Nat.cast_nonneg k) u.1
      (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u)
  map_add' u v :=
    toWkpSpace_add (Nat.cast_nonneg k) u.1 v.1
      (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u)
      (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) v)
  map_smul' c u :=
    toWkpSpace_smul (Nat.cast_nonneg k) c u.1
      (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u)
      (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) (c • u))

/-- Unfolding lemma: the bundled linear bridge evaluates to `toWkpSpace` on the underlying
`H^k` element, with realness supplied by `HsSpaceReal.isRealL2_toL2Fun`. -/
@[simp] theorem toWkpSpaceLinear_apply (u : HsSpaceReal n (k : ℝ)) :
    toWkpSpaceLinear n k u =
      toWkpSpace (Nat.cast_nonneg k) u.1
        (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u) := rfl

end SobolevSpace.Fractional
