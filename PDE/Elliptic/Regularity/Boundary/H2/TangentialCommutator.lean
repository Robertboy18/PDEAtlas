/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.TangentialDifferenceQuotient
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.CoefficientCommutator

/-!
# Boundary regularity: tangential coefficient commutators

On the flattened upper half-space `Ω⁺ = {xₙ > 0}` a tangential translation
`x ↦ x + h eₖ` (`k ≠ n`) maps the half-space onto itself, so tangential
difference quotients act on `Lᵖ(Ω⁺)` without any extension convention.
Differencing a product `a • u` with `a ∈ L∞` and `u ∈ L²` gives the exact
discrete Leibniz rule

`Dₖʰ(a u) = (τₕ a) Dₖʰ u + (Dₖʰ a) u`,

whose second term is the coefficient commutator. When `a` has a Lipschitz
representative with constant `C`, the quotient `Dₖʰ a` is bounded by `C` in
`L∞` uniformly in `h ≠ 0`. This is the only place where Lipschitz regularity
of the principal coefficients enters the boundary `H²` estimate.

## Main results

* `tangentialTranslateLp_lpSMul`, `tangentialDifferenceQuotientL2_lpSMul`:
  translation commutes with the `L∞ × Lᵖ` product, and the tangential
  quotient of a product obeys the Leibniz rule above.
* `coefficientDifferenceLInfOnUpper`, `coefficientDifferenceLInfOnUpper.norm_le`:
  the forward difference of a Lipschitz coefficient as an `L∞` multiplier
  with norm at most the Lipschitz constant.
* `tangentialDifferenceQuotientLp.norm_top_le`,
  `tangentialCoefficientCommutatorL2.norm_le`: the same bound for the
  abstract tangential quotient of any `L∞` class with a Lipschitz
  representative, and for its action on an `L²` field.
* `tangentialCoefficientCommutatorL2.abs_sum_inner_le_young`: the full matrix
  commutator pairing costs, after Young's inequality, one quarter of the
  elliptic energy `α ∑ᵢ ‖wᵢ‖²` plus an explicit lower-order term.

## Implementation notes

The matrix bounds sum each coefficient row before pairing, so Young's
inequality is spent once per differentiated component rather than once per
matrix entry. The pointwise quotient `DifferenceQuotient.forwardDifference`
of a Lipschitz `f` is continuous and bounded by the Lipschitz constant; the
`L∞` class is built from it with `MemLp.toLp`, and `apply_ae` records the
almost-everywhere identification.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 4 of the proof of Theorem 4, (49)-(50), p. 336,
  which estimates the terms as in step 4 of the proof of §6.3.1, Theorem 1, with the product rule
  (17) and the splitting (18), p. 329.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity),
  pp. 177-218.
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Tangential translation commutes with multiplication of an `L∞`
coefficient and an `Lᵖ` field on the upper half-space. -/
theorem tangentialTranslateLp_lpSMul
    [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (a : DerivLp n ∞ (HalfSpace.upper n))
    (u : DerivLp n p (HalfSpace.upper n)) :
    tangentialTranslateLp p k hk h (a • u) =
      tangentialTranslateLp ∞ k hk h a •
        tangentialTranslateLp p k hk h u := by
  apply MeasureTheory.Lp.ext
  have hleft := tangentialTranslateLp.apply_ae p k hk h (a • u)
  have ha := tangentialTranslateLp.apply_ae ∞ k hk h a
  have hu := tangentialTranslateLp.apply_ae p k hk h u
  have hinput := MeasureTheory.Lp.coeFn_lpSMul (r := p) a u
  have hinputShift :=
      (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.ae_eq_comp
        hinput
  have hright := MeasureTheory.Lp.coeFn_lpSMul (r := p)
    (tangentialTranslateLp ∞ k hk h a)
    (tangentialTranslateLp p k hk h u)
  filter_upwards [hleft, ha, hu, hinputShift, hright] with
    x hleftx hax hux hinputx hrightx
  rw [hleftx, hrightx]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [hax, hux]
  simpa [Function.comp_def,
    SobolevSpace.GraphSpace.Rellich.translationContinuousMap,
    Pi.smul_apply, smul_eq_mul] using hinputx

/-- Exact tangential `Lp` Leibniz rule.  The first term contains the
translated coefficient and the quotient of the field; the second is the
coefficient commutator multiplying the unshifted field. -/
theorem tangentialDifferenceQuotientL2_lpSMul
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (a : DerivLp n ∞ (HalfSpace.upper n))
    (u : DerivLp n 2 (HalfSpace.upper n)) :
    tangentialDifferenceQuotientLp 2 k hk h (a • u) =
      tangentialTranslateLp ∞ k hk h a •
          tangentialDifferenceQuotientLp 2 k hk h u +
        tangentialDifferenceQuotientLp ∞ k hk h a • u := by
  apply MeasureTheory.Lp.ext
  have hleft := tangentialDifferenceQuotientLp.apply_ae 2 k hk h (a • u)
  have hprincipal := MeasureTheory.Lp.coeFn_lpSMul (r := 2)
    (tangentialTranslateLp ∞ k hk h a)
    (tangentialDifferenceQuotientLp 2 k hk h u)
  have hcommutator := MeasureTheory.Lp.coeFn_lpSMul (r := 2)
    (tangentialDifferenceQuotientLp ∞ k hk h a) u
  have hsum := MeasureTheory.Lp.coeFn_add
    (tangentialTranslateLp ∞ k hk h a •
      tangentialDifferenceQuotientLp 2 k hk h u)
    (tangentialDifferenceQuotientLp ∞ k hk h a • u)
  have ha := tangentialTranslateLp.apply_ae ∞ k hk h a
  have hdu := tangentialDifferenceQuotientLp.apply_ae 2 k hk h u
  have hda := tangentialDifferenceQuotientLp.apply_ae ∞ k hk h a
  have hinput := MeasureTheory.Lp.coeFn_lpSMul (r := 2) a u
  have hinputShift :=
      (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.ae_eq_comp
        hinput
  filter_upwards [hleft, hprincipal, hcommutator, hsum,
    ha, hdu, hda, hinput, hinputShift] with
    x hleftx hprincipalx hcommutatorx hsumx hax hdux hdax
      hinputx hinputShiftx
  rw [hleftx, hsumx]
  simp only [Pi.add_apply]
  rw [hprincipalx, hcommutatorx]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [hax, hdux, hdax]
  have hshift :
      ((a • u : DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)
          (x + DifferenceQuotient.coordinateStep k h) =
        a (x + DifferenceQuotient.coordinateStep k h) *
          u (x + DifferenceQuotient.coordinateStep k h) := by
    simpa [Function.comp_def,
      SobolevSpace.GraphSpace.Rellich.translationContinuousMap,
      Pi.smul_apply, smul_eq_mul] using hinputShiftx
  have hbase :
      ((a • u : DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ) x =
        a x * u x := by
    simpa [Pi.smul_apply, smul_eq_mul] using hinputx
  rw [hshift, hbase]
  ring

/-- A Lipschitz coefficient difference quotient, bundled as an `L∞`
multiplier on the upper half-space. -/
noncomputable def coefficientDifferenceLInfOnUpper
    [Fact (0 < n)] (k : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0) :
    DerivLp n ∞ (HalfSpace.upper n) := by
  let q := DifferenceQuotient.forwardDifference k h f
  have hcont : Continuous q := by
    dsimp [q]
    unfold DifferenceQuotient.forwardDifference
    exact continuous_const.mul
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
  have hm : MemLp q ∞ (domainMeasure n (HalfSpace.upper n)) := by
    apply memLp_top_of_bound hcont.aestronglyMeasurable C
    exact Filter.Eventually.of_forall
      (DifferenceQuotient.norm_forwardDifference_le_of_lipschitz
        k f hf hh)
  exact hm.toLp q

/-- The `L∞` coefficient quotient agrees almost everywhere with the
classical forward difference. -/
theorem coefficientDifferenceLInfOnUpper.apply_ae
    [Fact (0 < n)] (k : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0) :
    ((coefficientDifferenceLInfOnUpper k f hf h hh :
        DerivLp n ∞ (HalfSpace.upper n)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        DifferenceQuotient.forwardDifference k h f := by
  let q := DifferenceQuotient.forwardDifference k h f
  have hcont : Continuous q := by
    dsimp [q]
    unfold DifferenceQuotient.forwardDifference
    exact continuous_const.mul
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
  have hm : MemLp q ∞ (domainMeasure n (HalfSpace.upper n)) := by
    apply memLp_top_of_bound hcont.aestronglyMeasurable C
    exact Filter.Eventually.of_forall
      (DifferenceQuotient.norm_forwardDifference_le_of_lipschitz
        k f hf hh)
  simpa [coefficientDifferenceLInfOnUpper, q] using hm.coeFn_toLp

/-- A Lipschitz constant controls the `L∞` norm of the coefficient quotient
on the flattened half-space. -/
theorem coefficientDifferenceLInfOnUpper.norm_le
    [Fact (0 < n)] (k : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0) :
    ‖coefficientDifferenceLInfOnUpper k f hf h hh‖ ≤ C := by
  let q := DifferenceQuotient.forwardDifference k h f
  have hcont : Continuous q := by
    dsimp [q]
    unfold DifferenceQuotient.forwardDifference
    exact continuous_const.mul
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
  have hqbound :
      ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), ‖q x‖ ≤ (C : ℝ) :=
    Filter.Eventually.of_forall
      (DifferenceQuotient.norm_forwardDifference_le_of_lipschitz
        k f hf hh)
  have hm : MemLp q ∞ (domainMeasure n (HalfSpace.upper n)) :=
    memLp_top_of_bound hcont.aestronglyMeasurable C hqbound
  rw [show coefficientDifferenceLInfOnUpper k f hf h hh = hm.toLp q by rfl,
    MeasureTheory.Lp.norm_toLp]
  have help :
      eLpNorm q ∞ (domainMeasure n (HalfSpace.upper n)) ≤
        ENNReal.ofReal (C : ℝ) := by
    rw [eLpNorm_exponent_top hm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound hqbound
  calc
    ENNReal.toReal (eLpNorm q ∞ (domainMeasure n (HalfSpace.upper n))) ≤
        ENNReal.toReal (ENNReal.ofReal (C : ℝ)) :=
      ENNReal.toReal_mono (by simp) help
    _ = C := by simp

/-- The abstract tangential quotient of an `L∞` coefficient agrees with the
concrete quotient of any Lipschitz representative. -/
theorem tangentialDifferenceQuotientLp.eq_coefficientDifferenceLInfOnUpper
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (a : DerivLp n ∞ (HalfSpace.upper n))
    (f : ℝ^n → ℝ) {C : NNReal} (hf : LipschitzWith C f)
    (ha : (a : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] f)
    (h : ℝ) (hh : h ≠ 0) :
    tangentialDifferenceQuotientLp ∞ k hk h a =
      coefficientDifferenceLInfOnUpper k f hf h hh := by
  apply MeasureTheory.Lp.ext
  have hdq := tangentialDifferenceQuotientLp.apply_ae ∞ k hk h a
  have hcoeff := coefficientDifferenceLInfOnUpper.apply_ae k f hf h hh
  have hashift :=
    (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.ae_eq_comp ha
  filter_upwards [hdq, hcoeff, ha, hashift] with
    x hdqx hcoeffx hax hashiftx
  rw [hdqx, hcoeffx]
  have hashift' :
      a (x + DifferenceQuotient.coordinateStep k h) =
        f (x + DifferenceQuotient.coordinateStep k h) := by
    simpa [Function.comp_def,
      SobolevSpace.GraphSpace.Rellich.translationContinuousMap] using hashiftx
  rw [hax, hashift']
  rfl

/-- Quantitative coefficient-commutator estimate used in the boundary
energy argument. -/
theorem tangentialDifferenceQuotientLp.norm_top_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (a : DerivLp n ∞ (HalfSpace.upper n))
    (f : ℝ^n → ℝ) {C : NNReal} (hf : LipschitzWith C f)
    (ha : (a : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] f)
    (h : ℝ) (hh : h ≠ 0) :
    ‖tangentialDifferenceQuotientLp ∞ k hk h a‖ ≤ C := by
  rw [tangentialDifferenceQuotientLp.eq_coefficientDifferenceLInfOnUpper
    k hk a f hf ha h hh]
  exact coefficientDifferenceLInfOnUpper.norm_le k f hf h hh

/-- The coefficient commutator multiplying an `L²` field is controlled by
the Lipschitz constant of the coefficient. -/
theorem tangentialCoefficientCommutatorL2.norm_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (a : DerivLp n ∞ (HalfSpace.upper n))
    (f : ℝ^n → ℝ) {C : NNReal} (hf : LipschitzWith C f)
    (ha : (a : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] f)
    (h : ℝ) (hh : h ≠ 0)
    (v : DerivLp n 2 (HalfSpace.upper n)) :
    ‖tangentialDifferenceQuotientLp ∞ k hk h a • v‖ ≤ C * ‖v‖ := by
  calc
    ‖tangentialDifferenceQuotientLp ∞ k hk h a • v‖ ≤
        ‖tangentialDifferenceQuotientLp ∞ k hk h a‖ * ‖v‖ :=
      MeasureTheory.Lp.norm_smul_le _ _
    _ ≤ C * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (tangentialDifferenceQuotientLp.norm_top_le
          k hk a f hf ha h hh) (norm_nonneg v)

/-- Row-wise matrix commutator bound after taking one tangential difference
quotient of the flattened principal coefficients. -/
theorem tangentialCoefficientCommutatorL2.sum_norm_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (row : Fin n)
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    (h : ℝ) (hh : h ≠ 0)
    (v : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    ‖∑ j : Fin n,
        tangentialDifferenceQuotientLp ∞ k hk h (A row j) • v j‖ ≤
      ∑ j : Fin n, (C row j : ℝ) * ‖v j‖ := by
  calc
    ‖∑ j : Fin n,
        tangentialDifferenceQuotientLp ∞ k hk h (A row j) • v j‖ ≤
        ∑ j : Fin n,
          ‖tangentialDifferenceQuotientLp ∞ k hk h (A row j) • v j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin n, (C row j : ℝ) * ‖v j‖ :=
      Finset.sum_le_sum fun j _ ↦
        tangentialCoefficientCommutatorL2.norm_le
          k hk (A row j) (a row j) (haLip row j)
            (haRep row j) h hh (v j)

/-- Bound the complete tangential coefficient-commutator pairing on the
flattened half-space.  The coefficient row is summed before pairing, which
is the form needed to absorb one error term for each differentiated
component rather than one error term for every matrix entry. -/
theorem tangentialCoefficientCommutatorL2.abs_sum_inner_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    (h : ℝ) (hh : h ≠ 0)
    (v w : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j)
          (w i)| ≤
      ∑ i : Fin n, (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) * ‖w i‖ := by
  calc
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j)
          (w i)| ≤
        ∑ i : Fin n,
          |inner ℝ
            (∑ j : Fin n,
              tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j)
            (w i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,
        ‖∑ j : Fin n,
          tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j‖ * ‖w i‖ := by
      exact Finset.sum_le_sum fun i _ ↦
        abs_real_inner_le_norm
          (∑ j : Fin n,
            tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j)
          (w i)
    _ ≤ ∑ i : Fin n, (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) * ‖w i‖ := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right
          (tangentialCoefficientCommutatorL2.sum_norm_le
            k hk i A a C haLip haRep h hh v)
          (norm_nonneg (w i))

/-- Young-absorbed boundary commutator estimate.  With ellipticity constant
`alpha`, the commutator absorbs exactly one quarter of the tangential
principal energy and leaves an explicit lower-order term. -/
theorem tangentialCoefficientCommutatorL2.abs_sum_inner_le_young
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    (h : ℝ) (hh : h ≠ 0)
    (v w : Fin n → DerivLp n 2 (HalfSpace.upper n))
    {alpha : ℝ} (halpha : 0 < alpha) :
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j)
          (w i)| ≤
      (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ^ 2 / alpha) +
      (alpha / 4) * ∑ i : Fin n, ‖w i‖ ^ 2 := by
  calc
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            tangentialDifferenceQuotientLp ∞ k hk h (A i j) • v j)
          (w i)| ≤
        ∑ i : Fin n,
          (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) * ‖w i‖ :=
      tangentialCoefficientCommutatorL2.abs_sum_inner_le
        k hk A a C haLip haRep h hh v w
    _ ≤ ∑ i : Fin n,
        ((∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ^ 2 / alpha +
          (alpha / 4) * ‖w i‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _ ↦
        DifferenceQuotient.mul_le_sq_div_add_quarter halpha
          (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ‖w i‖
    _ = (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ^ 2 / alpha) +
        (alpha / 4) * ∑ i : Fin n, ‖w i‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

end GraphSpace.BoundaryRegularity
end SobolevSpace
