/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakDerivativeData
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Sobolev assembly with one distinguished coordinate

Let `u ∈ W^{m,2}(Ω)` and single out one coordinate direction `normal`. If every first derivative
`∂ᵢu` with `i ≠ normal` is itself known to lie in `W^{m,2}(Ω)`, then every derivative of `u` of
order `m + 1` that involves at least one tangential index is already available: commute the
tangential derivative to the front and read it off the bundle of `∂ᵢu`. The only derivative of order
`m + 1` not covered this way is the pure normal one, `∂ₙ^{m+1} u`. We show that supplying that
single missing weak derivative (as an `L²` function for `m = 2`, or as a `W^{r,2}` element in
general) is enough to assemble a `W^{m+1,2}` representative of `u`.

This is the assembly step behind the classical boundary regularity argument for elliptic equations
(Evans §6.3.2, proof of Theorem 4, steps 3-5): tangential derivatives are controlled by difference
quotients in the flattened half-space, and the pure normal derivative is recovered from the equation
itself. The equation itself does not enter here; we only show how the two kinds of information
combine into a Sobolev element of one higher order.

## Main results

* `exists_H3_of_H2_coordinateDerivatives_except_one`: an `H²` function whose
  tangential first derivatives are `H²`, together with an `L²` weak derivative
  `∂ₙ(∂ₙ∂ₙ u)`, has an `H³` representative with the same base function.
* `exists_succOrder_of_coordinateDerivatives_except_one`: the same statement
  from `W^{r+2,2}` to `W^{r+3,2}`, where the pure normal third derivative is
  provided as `WeakDerivativeData` of order `r`.  Openness of the domain is
  needed here to identify the two candidate representatives of a first
  derivative through uniqueness of weak derivatives.

## Implementation notes

Weak derivatives are indexed by coordinate words (`List (Fin n)`), and the
proofs work by permuting words and cancelling common prefixes
(`HasWeakDerivativeOn.perm`, `cancel_prefix_append_single`) so that each
required row of the higher-order bundle is located in one of the given
bundles.  The final step is `exists_succOrder_of_firstDerivatives`, which
glues a family of first-derivative bundles into a bundle of one higher order.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4, pp. 334-340: tangential difference
  quotients give `u_{x_k} ∈ H¹(V)` for `k < n` in steps 3-4, (51), p. 336, and step 5, (52)-(56),
  pp. 336-337, recovers `u_{x_n x_n}` from the equation; Theorem 5, p. 340, for higher boundary
  regularity.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/--
Sharp third-order assembly with one distinguished coordinate.

Suppose an `H²` field has an `H²` representative for every first derivative
except `normal`.  All third derivatives containing one of those other
coordinates are then available.  A single additional weak derivative,
`D_normal(D_normal D_normal u)`, supplies the only remaining third derivative
and suffices to assemble an `H³` representative.
-/
theorem exists_H3_of_H2_coordinateDerivatives_except_one
    (U : W^{2,2}(Ω))
    (normal : Fin n)
    (derivativeRepresentative :
      ∀ i : Fin n, i ≠ normal → W^{2,2}(Ω))
    (derivativeRepresentative_base_eq :
      ∀ (i : Fin n) (hi : i ≠ normal),
        ((derivativeRepresentative i hi : WkpAmbientOn n 2 2 Ω)
            (baseIndex n 2) : DerivLp n 2 Ω) =
          ((U : WkpAmbientOn n 2 2 Ω)
            (firstDerivIndex n 2 (by norm_num) i) :
              DerivLp n 2 Ω))
    (g : DerivLp n 2 Ω)
    (hg : HasWeakDerivativeOn (n := n) Ω [normal]
      (((U : WkpAmbientOn n 2 2 Ω)
        (pairDerivIndex n normal normal) :
          DerivLp n 2 Ω) : ℝ^n → ℝ)
      (g : ℝ^n → ℝ)) :
    ∃ W : W^{3,2}(Ω),
      ⇑((W : WkpAmbientOn n 3 2 Ω)
          (baseIndex n 3) : DerivLp n 2 Ω)
        =ᵐ[domainMeasure n Ω]
      ⇑((U : WkpAmbientOn n 2 2 Ω)
            (baseIndex n 2) : DerivLp n 2 Ω) := by
  classical
  let V := derivativeRepresentative
  have hV := derivativeRepresentative_base_eq
  let f : ℝ^n → ℝ := ((U : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω)
  let Un : H¹(Ω) := derivativeWordCLM (m := 2) (r := 1) (p := 2) [normal] (by simp) U
  let d : Fin n → Fin n → DerivLp n 2 Ω := fun i j ↦
    if hi : i = normal then
      if hj : j = normal then g
      else ((V j hj : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n normal normal) : DerivLp n 2 Ω)
    else ((V i hi : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n normal j) : DerivLp n 2 Ω)
  have hfirstV (i : Fin n) (hi : i ≠ normal) : HasWeakDerivativeOn (n := n) Ω [i] f
      (((V i hi : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    rw [hV i hi]
    exact U.property.hasWeakDerivativeOn_first (by norm_num) i
  have hprefix (i : Fin n) : HasWeakDerivativeOn (n := n) Ω [normal, i] f
      (((Un : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    simpa [f, Un] using U.property.hasWeakDerivativeOn_list [normal, i] (by simp)
  -- every first derivative of a coordinate slice of `∂ₙ u` is a given third derivative
  have hdWeak (i j : Fin n) : HasWeakDerivativeOn (n := n) Ω [j]
      (((Un : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      (d i j : ℝ^n → ℝ) := by
    by_cases hi : i = normal
    · subst i
      by_cases hj : j = normal
      · subst j
        simpa [d, Un, pairDerivIndex, secondDerivIndex] using hg
      · simpa [d, hj, pairDerivIndex, secondDerivIndex] using
          (hprefix normal).cancel_prefix_append_single j
            ((HasWeakDerivativeOn.append_from_wkp (V j hj) [j] [normal, normal] (by simp)
              (hfirstV j hj)).perm List.perm_append_comm)
    · simpa [d, hi, pairDerivIndex, secondDerivIndex] using
        (hprefix i).cancel_prefix_append_single j
          ((HasWeakDerivativeOn.append_from_wkp (V i hi) [i] [normal, j] (by simp)
            (hfirstV i hi)).perm (List.Perm.swap i normal [j]).symm)
  obtain ⟨Vnormal, hVnormalBase, -⟩ := exists_H2_of_firstDerivatives_haveWeakDerivatives Un
    (fun i j ↦ d i j) (fun _ _ ↦ Lp.memLp _) hdWeak
  let allV : Fin n → W^{2,2}(Ω) := fun i ↦ if hi : i = normal then Vnormal else V i hi
  have hallV (i : Fin n) :
      ((allV i : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω) =
        ((U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by norm_num) i) : DerivLp n 2 Ω) := by
    by_cases hi : i = normal
    · subst i
      exact Lp.ext (by simpa [allV, Un] using hVnormalBase)
    · simpa [allV, hi] using hV i hi
  simpa using exists_succOrder_of_firstDerivatives (m := 2) (p := 2) (by norm_num) U allV hallV

/-- Extracting a derivative word from two Sobolev bundles preserves a weak first-derivative
relation between their base representatives. This commutes the first derivative past the word. -/
theorem hasWeakDerivativeOn_derivativeWordCLM
    {m r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U V : W^{m,p}(Ω)) (i : Fin n) (α : List (Fin n)) (hα : α.length + r ≤ m)
    (hV : HasWeakDerivativeOn (n := n) Ω [i] (baseRepresentative U) (baseRepresentative V)) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (baseRepresentative (derivativeWordCLM α hα U))
      (baseRepresentative (derivativeWordCLM α hα V)) := by
  rw [baseRepresentative_derivativeWordCLM, baseRepresentative_derivativeWordCLM]
  have hprefix := U.property.hasWeakDerivativeOn_list α (by omega)
  have hfull := HasWeakDerivativeOn.append_from_wkp V [i] α (by omega) hV
  exact hprefix.cancel_prefix_append_single i
    (hfull.perm (List.perm_append_comm (l₁ := [i]) (l₂ := α)))

/-- Raise the order of a derivative slice when its normal derivative is supplied separately;
all other first derivatives are obtained by commuting the word with the given representatives. -/
private theorem exists_succOrder_derivativeWord_of_normalData
    {m r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hΩ : IsOpen Ω) (hr : 0 < r)
    (U : W^{m,p}(Ω)) (normal : Fin n)
    (V : ∀ i : Fin n, i ≠ normal → W^{m,p}(Ω))
    (hV : ∀ i hi, HasWeakDerivativeOn (n := n) Ω [i]
      (baseRepresentative U) (baseRepresentative (V i hi)))
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    (normalData : WeakDerivativeData r p Ω [normal]
      (baseRepresentative (derivativeWordCLM α hα U))) :
    ∃ W : W^{r + 1,p}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω]
        baseRepresentative (derivativeWordCLM α hα U) := by
  classical
  let slice := derivativeWordCLM α hα U
  let first (i : Fin n) : W^{r,p}(Ω) :=
    if hi : i = normal then normalData.derivative else derivativeWordCLM α hα (V i hi)
  apply exists_succOrder_of_firstDerivatives hr slice first
  intro i
  apply MeasureTheory.Lp.ext
  have hfirst : HasWeakDerivativeOn (n := n) Ω [i]
      (baseRepresentative slice) (baseRepresentative (first i)) := by
    by_cases hi : i = normal
    · subst i
      simpa [first, slice, baseRepresentative] using normalData.derivative_spec
    · simpa [first, hi, slice] using
        hasWeakDerivativeOn_derivativeWordCLM U (V i hi) i α hα (hV i hi)
  exact hfirst.unique_ae hΩ (slice.property.hasWeakDerivativeOn_first hr i)

/--
Arbitrary-order Sobolev assembly with one distinguished coordinate.

Suppose `U ∈ W^{r+2,2}` and every first derivative except the distinguished
one has a representative in the same space.  A `W^{r,2}` representative of
the weak derivative `D_normal(D_normal D_normal U)` supplies the remaining
branch and yields a `W^{r+3,2}` representative of `U`.
-/
theorem exists_succOrder_of_coordinateDerivatives_except_one
    {r : ℕ}
    {Ω : Set (ℝ^n)}
    (hOmegaOpen : IsOpen Ω)
    (U : W^{r + 2,2}(Ω))
    (normal : Fin n)
    (derivativeRepresentative :
      ∀ i : Fin n, i ≠ normal → W^{r + 2,2}(Ω))
    (derivativeRepresentative_base_eq :
      ∀ (i : Fin n) (hi : i ≠ normal),
        ((derivativeRepresentative i hi :
            WkpAmbientOn n (r + 2) 2 Ω)
          (baseIndex n (r + 2)) : DerivLp n 2 Ω) =
            ((U : WkpAmbientOn n (r + 2) 2 Ω)
              (firstDerivIndex n (r + 2) (by omega) i) :
                DerivLp n 2 Ω))
    (pureNormalThirdData :
      WeakDerivativeData r 2 Ω [normal]
        (((U : WkpAmbientOn n (r + 2) 2 Ω)
          (secondDerivIndex n (r + 2) (by omega) normal normal) :
            DerivLp n 2 Ω) : ℝ^n → ℝ)) :
    ∃ W : W^{r + 3,2}(Ω),
      ⇑((W : WkpAmbientOn n (r + 3) 2 Ω)
          (baseIndex n (r + 3)) : DerivLp n 2 Ω)
        =ᵐ[domainMeasure n Ω]
          ⇑((U : WkpAmbientOn n (r + 2) 2 Ω)
            (baseIndex n (r + 2)) : DerivLp n 2 Ω) := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa using exists_H3_of_H2_coordinateDerivatives_except_one U normal
      derivativeRepresentative derivativeRepresentative_base_eq
      ((pureNormalThirdData.derivative : WkpAmbientOn n 0 2 Ω) (baseIndex n 0))
      (by simpa [pairDerivIndex, secondDerivIndex] using pureNormalThirdData.derivative_spec)
  have htangential (i : Fin n) (hi : i ≠ normal) :
      HasWeakDerivativeOn (n := n) Ω [i] (baseRepresentative U)
        (baseRepresentative (derivativeRepresentative i hi)) := by
    unfold baseRepresentative
    rw [derivativeRepresentative_base_eq i hi]
    exact U.property.hasWeakDerivativeOn_first (by omega) i
  have hnn : [normal, normal].length + r ≤ r + 2 := by
    simp only [List.length_cons, List.length_nil]; omega
  have hn : [normal].length + (r + 1) ≤ r + 2 := by
    simp only [List.length_cons, List.length_nil]; omega
  let Un : W^{r + 1,2}(Ω) := derivativeWordCLM [normal] hn U
  -- First raise the regularity of the second normal derivative using the supplied third derivative.
  obtain ⟨Dnn, hDnn⟩ := exists_succOrder_derivativeWord_of_normalData hOmegaOpen hr U normal
    derivativeRepresentative htangential [normal, normal] hnn
    ⟨pureNormalThirdData.derivative, by
      simpa [baseRepresentative, secondDerivIndex] using pureNormalThirdData.derivative_spec⟩
  -- The improved second normal derivative is the missing first derivative of the normal slice.
  have hbase : baseRepresentative Dnn =ᵐ[domainMeasure n Ω]
      (((Un : WkpAmbientOn n (r + 1) 2 Ω)
        (firstDerivIndex n (r + 1) (by omega) normal) : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    simpa [baseRepresentative, Un] using hDnn
  obtain ⟨Vnormal, hVnormal⟩ := exists_succOrder_derivativeWord_of_normalData
    hOmegaOpen (by omega : 0 < r + 1) U normal derivativeRepresentative htangential
    [normal] hn ⟨Dnn, (hasWeakDerivativeOn_congr_ae .rfl hbase.symm).1
      (Un.property.hasWeakDerivativeOn_first (by omega) normal)⟩
  -- Assemble the full family of first derivatives at the original order.
  refine exists_succOrder_of_firstDerivatives (by omega) U
    (fun i ↦ if hi : i = normal then Vnormal else derivativeRepresentative i hi) fun i ↦ ?_
  by_cases hi : i = normal
  · subst i
    exact Lp.ext (by simpa [baseRepresentative] using hVnormal)
  · simpa [hi] using derivativeRepresentative_base_eq i hi

end SobolevSpace.GraphSpace
