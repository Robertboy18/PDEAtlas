/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.TestFunctionConvergence
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension
import Mathlib.Topology.MetricSpace.UniformConvergence
import PDE.Analysis.WeakCompactness
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
import PDE.Analysis.MeasureTheory.Lp.Reflexivity
import Mathlib.MeasureTheory.Group.Integral

/-!
# Weak derivatives from difference quotients

The difference-quotient characterization of `H¹` (Evans, PDE, §5.8.2): an `L²(ℝ^n)` function
whose coordinate difference quotients `Dᵢʰ u` are bounded in `L²` uniformly along a sequence of
steps `h → 0` has a weak derivative `∂ᵢu ∈ L²` with `‖∂ᵢu‖ ≤ sup_h ‖Dᵢʰ u‖`; conversely, for
`u ∈ W^{1,p}(ℝ^n)` with `p < ∞`, `‖Dᵢʰ u‖_p ≤ ‖∂ᵢu‖_p` uniformly in `h ≠ 0` and
`Dᵢʰ u → ∂ᵢu` in `Lᵖ`.

For `1 < p < ∞`, a bound on the quotients restricted to a measurable set `V` constructs
a derivative in `Lp(V)` with the same bound. The compactness input is real `Lp`
reflexivity for σ-finite measures. For open `V`, this is the usual weak derivative;
on arbitrary measurable sets the supported test class may be trivial. A domain-local
version starts with `u ∈ Lp(Ω)` and bounds the restricted quotients of its zero extension.
That extension need not have a global weak derivative.

For the zero extension of an `H¹₀(Ω)` function, the uniform
bound `‖Dᵢʰ(E₀u)‖_{L²} ≤ ‖u‖_{H¹}` is the form of §5.8.2, Theorem 3(i), that the interior
regularity argument of Evans, PDE, §6.3.1, uses to bound the error terms.

## Main results

* `lpPairing_translateLp_left`, `lpPairing_differenceQuotientLp_left`: translation adjointness
  and discrete integration by parts for conjugate real Lp spaces.
* `exists_Lp_weakDerivativeOn_of_bounded_restrictedDifferenceQuotients_with_norm`: the
  converse for `1 < p < ∞`, with the same derivative norm bound.
* `exists_Lp_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm`,
  `exists_Lp_weakDerivativeOn_of_bounded_zeroExtensionDifferenceQuotients_with_norm`:
  cutoff and domain-local forms of the converse.
* `inner_differenceQuotientL2_left`: discrete integration by parts.
* `exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm`: uniformly bounded
  quotients in direction `i` give an `L²` weak derivative with the same bound.
* `exists_L2_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm`: the local
  version on an open set.
* `exists_H1_of_bounded_differenceQuotients`: bounds in every direction give an `H¹(ℝ^n)`
  representative.
* `norm_differenceQuotientLp_base_le_deriv_of_ne_top`,
  `tendsto_differenceQuotientLp_base_of_ne_top`: for `W^{1,p}(ℝ^n)`, `p < ∞`, the sharp bound
  `‖Dᵢʰ u‖_p ≤ ‖∂ᵢu‖_p` and strong convergence `Dᵢʰ u → ∂ᵢu`.
* `zeroExtensionDifferenceQuotient`, `zeroExtensionDifferenceQuotient.norm_le`: the difference
  quotient of the zero extension of an `H¹₀(Ω)` function and its `h`-uniform bound.

## How it works

In `L²`, bounded quotients give a weak derivative by weak compactness, as in Evans's proof of
§5.8.2, Theorem 3(ii). Discrete integration by parts, `⟪Dᵢʰ u, φ⟫ = -⟪u, Dᵢ⁻ʰ φ⟫`, holds exactly
because translation is an isometry of `L²` with adjoint the opposite translation. A bounded sequence
`Dᵢʰ u` has a weak limit point `g` along an ultrafilter, and passing to the limit in the identity
against smooth `φ` (for which `Dᵢ⁻ʰ φ → ∂ᵢφ` strongly) shows that `g` is the weak derivative. A
localized version, with bounds only for the cutoff-localized quotients, gives weak derivatives on an
open set. The finite-exponent proofs share this passage to the limit, and none of them needs finite
volume of the localization set. The estimate `‖Dᵢʰ u‖_p ≤ ‖∂ᵢu‖_p` is the density extension of the
smooth estimate in `DifferenceQuotient.TestFunctionConvergence`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 3, pp. 292-293: part (i), the estimate (8),
  and part (ii), the converse for `1 < p < ∞`, proved from the summation-by-parts formula (10) and
  the weak compactness step (11); and §6.3.1, Theorem 1, pp. 327-331, whose proof uses Theorem 3(i)
  in steps 4 and 5 and Theorem 3(ii) in step 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology
open SobolevSpace.GraphSpace.Rellich
open SobolevSpace.Extension.Lp
open PDE.Analysis

variable {n : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

/-- Opposite translations are adjoint under the real `Lp`–`Lq` integral pairing. -/
theorem lpPairing_translateLp_left (a : ℝ^n)
    (u : DerivLp n p Set.univ) (v : DerivLp n q Set.univ) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        (translateLp p a u) v =
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (translateLp q (-a) v) := by
  simp only [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
  calc
    (∫ x, (translateLp p a u) x * v x ∂domainMeasure n Set.univ) =
        ∫ x, u (x + a) * v x ∂domainMeasure n Set.univ := by
      apply integral_congr_ae
      filter_upwards [translateLp_apply_ae p a u] with x hx
      rw [hx]
    _ = ∫ x, u x * v (x + -a) ∂domainMeasure n Set.univ := by
      simp only [domainMeasure, Measure.restrict_univ]
      simpa only [add_assoc, add_neg_cancel, add_zero] using
        (integral_add_right_eq_self (μ := volume) (fun x ↦ u x * v (x + -a)) a)
    _ = ∫ x, u x * (translateLp q (-a) v) x ∂domainMeasure n Set.univ := by
      apply integral_congr_ae
      filter_upwards [translateLp_apply_ae q (-a) v] with x hx
      rw [hx]

/-- Discrete integration by parts for conjugate real `Lp` spaces. The identity also
holds for a zero step, since the totalized difference quotient is then zero. -/
theorem lpPairing_differenceQuotientLp_left (i : Fin n) (h : ℝ)
    (u : DerivLp n p Set.univ) (v : DerivLp n q Set.univ) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        (differenceQuotientLp p i h u) v =
      -(ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (differenceQuotientLp q i (-h) v) := by
  have hstep : coordinateStep i (-h) = -(coordinateStep i h) := by
    simp [coordinateStep]
  simp only [differenceQuotientLp_apply, map_smul, map_sub,
    smul_apply, sub_apply, smul_eq_mul,
    hstep, lpPairing_translateLp_left, inv_neg, neg_mul, neg_neg]

/-- The conjugate pairing with a bundled test function is its distributional integral. -/
private theorem lpPairing_testFunctionLp_eq_integral
    (u : DerivLp n p Set.univ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (testFunctionLp q φ) =
      ∫ x, u x * φ.toFun x ∂domainMeasure n Set.univ := by
  simp only [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  have hφ : (testFunctionLp q φ : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ] φ.toFun := by
    simpa only [domainMeasure, Measure.restrict_univ] using testFunctionLp_apply_ae q φ
  filter_upwards [hφ] with x hx
  rw [hx]

/-- The conjugate pairing with a bundled test derivative is the classical derivative integral. -/
private theorem lpPairing_partialTestFunctionLp_eq_integral
    (u : DerivLp n p Set.univ) (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (partialTestFunctionLp q i φ) =
      ∫ x, u x * (∂[i] φ.toFun) x ∂domainMeasure n Set.univ := by
  simp only [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  have hφ : (partialTestFunctionLp q i φ : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
      fun x ↦ (∂[i] φ.toFun) x := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      partialTestFunctionLp_apply_ae q i φ
  filter_upwards [hφ] with x hx
  rw [hx]

/-- Pass from convergent quotient pairings to the weak derivative identity. Strong convergence
of the backward test quotients supplies the limit; supported tests localize both integrals. -/
private theorem hasWeakDerivativeOn_of_tendsto_differenceQuotient_pairings
    (hq_top : q ≠ ∞) (i : Fin n) (h : ℕ → ℝ)
    (hzero : Tendsto h atTop (nhds 0)) (hne : ∀ m, h m ≠ 0)
    (l : Filter ℕ) [l.NeBot] (hl : l ≤ atTop)
    (u g : DerivLp n p Set.univ) (V : Set (ℝ^n))
    (hforward : ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ.toFun ⊆ V →
      Tendsto (fun m ↦
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
          (differenceQuotientLp p i (h m) u) (testFunctionLp q φ)) l
        (nhds ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
          g (testFunctionLp q φ)))) :
    HasWeakDerivativeOn (n := n) V [i] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  refine ⟨
    (memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp u) (Fact.out : 1 ≤ p)).mono_set
      (subset_univ V),
    (memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp g) (Fact.out : 1 ≤ p)).mono_set
      (subset_univ V), ?_⟩
  intro φ hφV
  have hnegzero : Tendsto (fun m ↦ -(h m)) atTop (nhds 0) := by
    simpa using hzero.neg
  have hnegne : ∀ m, -(h m) ≠ 0 := fun m ↦ neg_ne_zero.mpr (hne m)
  have htest := (tendsto_differenceQuotientLp_testFunction q hq_top
    i φ (fun m ↦ -(h m)) hnegzero hnegne).mono_left hl
  have hright : Tendsto (fun m ↦
      -(ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (differenceQuotientLp q i (-(h m)) (testFunctionLp q φ))) l
      (nhds (-(ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (partialTestFunctionLp q i φ))) :=
    (((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
      u).continuous.continuousAt.tendsto.comp htest).neg
  have hpairLimit :
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
          g (testFunctionLp q φ) =
        -(ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
          u (partialTestFunctionLp q i φ) := by
    apply tendsto_nhds_unique (hforward φ hφV)
    simpa only [lpPairing_differenceQuotientLp_left] using hright
  rw [lpPairing_testFunctionLp_eq_integral,
    lpPairing_partialTestFunctionLp_eq_integral] at hpairLimit
  have hsuppDeriv :
      Function.support (fun x ↦ (∂[i] φ.toFun) x) ⊆ V := by
    refine (subset_tsupport _).trans ?_
    simpa only [partialDeriv] using
      (tsupport_fderiv_apply_subset ℝ (f := φ.toFun)
        (EuclideanSpace.single i (1 : ℝ))).trans hφV
  have hsuppLeft : Function.support
      (fun x ↦ u x * (∂[i] φ.toFun) x) ⊆ V :=
    (Function.support_mul_subset_right (f := (u : ℝ^n → ℝ))
      (g := fun x ↦ (∂[i] φ.toFun) x)).trans hsuppDeriv
  have hsuppRight : Function.support (fun x ↦ g x * φ.toFun x) ⊆ V :=
    (Function.support_mul_subset_right (f := (g : ℝ^n → ℝ)) (g := φ.toFun)).trans
      ((subset_tsupport _).trans hφV)
  have hleftRestrict :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := V) (f := fun x ↦ u x * (∂[i] φ.toFun) x)
      (fun x hx ↦ by
        by_contra hfx
        exact hx (hsuppLeft hfx))).symm
  have hrightRestrict :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := V) (f := fun x ↦ g x * φ.toFun x)
      (fun x hx ↦ by
        by_contra hfx
        exact hx (hsuppRight hfx))).symm
  simp only [iteratedPartialDeriv, List.length_cons, List.length_nil,
    Nat.zero_add, pow_one, neg_mul, one_mul]
  change (∫ x, u x * (∂[i] φ.toFun) x ∂domainMeasure n V) =
    -(∫ x, g x * φ.toFun x ∂domainMeasure n V)
  simp only [domainMeasure, Measure.restrict_univ] at hpairLimit
  rw [← hleftRestrict, ← hrightRestrict]
  linarith

/-- Tests supported in V cannot distinguish a whole-space field from the zero extension
of its restriction to V. -/
private theorem lpPairing_zeroExtend_restrict_testFunction
    (V : Set (ℝ^n)) (hV : MeasurableSet V)
    (u : DerivLp n p Set.univ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hφV : tsupport φ.toFun ⊆ V) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        (zeroExtendLp hV (restrictDerivLp (subset_univ V) u)) (testFunctionLp q φ) =
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        u (testFunctionLp q φ) := by
  rw [lpPairing_testFunctionLp_eq_integral, lpPairing_testFunctionLp_eq_integral]
  apply integral_congr_ae
  have hzero := zeroExtendLp_apply_ae hV (restrictDerivLp (subset_univ V) u)
  have hrestrict : ∀ᵐ x ∂domainMeasure n Set.univ, x ∈ V →
      (restrictDerivLp (subset_univ V) u) x = u x := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact (ae_restrict_iff' hV).1 (restrictDerivLp_apply_ae (subset_univ V) u)
  filter_upwards [hzero, hrestrict] with x hxzero hxrestrict
  rw [hxzero]
  by_cases hx : x ∈ V
  · simp only [extensionByZero, Set.indicator_of_mem hx, hxrestrict hx]
  · have hφzero : φ.toFun x = 0 := by
      by_contra hne
      exact hx (hφV (subset_tsupport φ.toFun hne))
    simp [hφzero]

omit [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] in
/-- Let `1 < p < ∞`, let `V` be measurable, and let `u ∈ Lp(ℝ^n)`.
If the coordinate difference quotients restricted to `V` have norm at most `C` along
nonzero steps tending to zero, there is `g ∈ Lp(V)` of norm at most `C` satisfying
`HasWeakDerivativeOn V [i] u g`. For open `V` this is the usual weak derivative. On an
arbitrary measurable `V` the supported test class may be trivial.
The proof constructs `g` by `Lp` weak compactness; no representation
or differentiability hypothesis is imposed on `u`. -/
theorem exists_Lp_weakDerivativeOn_of_bounded_restrictedDifferenceQuotients_with_norm
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (V : Set (ℝ^n)) (hV : MeasurableSet V)
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Tendsto h atTop (nhds 0)) (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n p Set.univ) (C : ℝ)
    (hbound : ∀ m,
      ‖restrictDerivLp (subset_univ V) (differenceQuotientLp p i (h m) u)‖ ≤ C) :
    ∃ g : DerivLp n p V, ‖g‖ ≤ C ∧
      HasWeakDerivativeOn (n := n) V [i] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  let q := ENNReal.conjExponent p
  have : ENNReal.HolderConjugate p q := inferInstance
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq_top : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp).ne
  let s : ℕ → DerivLp n p V :=
    fun m ↦ restrictDerivLp (subset_univ V) (differenceQuotientLp p i (h m) u)
  have hsbounded : Bornology.IsBounded (Set.range s) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * C, fun m k ↦ ?_⟩
    rw [dist_eq_norm]
    calc
      ‖s m - s k‖ ≤ ‖s m‖ + ‖s k‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound m) (hbound k)
      _ = 2 * C := by ring
  obtain ⟨gw, U, hU, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter_of_reflexive
      (MeasureTheory.Lp.surjective_inclusionInDoubleDual hp hp_top) atTop s hsbounded
  let g : DerivLp n p V := (toWeakSpace ℝ (DerivLp n p V)).symm gw
  refine ⟨g, ?_, ?_⟩
  · exact WeakCompactness.norm_le_of_tendsto_of_norm_le hweak
      (Filter.Eventually.of_forall hbound)
  have hg : HasWeakDerivativeOn (n := n) V [i] (u : ℝ^n → ℝ)
      (zeroExtendLp hV g : ℝ^n → ℝ) := by
    apply hasWeakDerivativeOn_of_tendsto_differenceQuotient_pairings
      hq_top i h hzero hne (U : Filter ℕ) hU u (zeroExtendLp hV g) V
    intro φ hφV
    let ell : StrongDual ℝ (DerivLp n p V) :=
      (((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q).flip
        (testFunctionLp q φ)).comp (zeroExtendLp hV)
    have heval := WeakCompactness.tendsto_evaluation hweak ell
    change Tendsto
      (fun m ↦ (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        (zeroExtendLp hV (s m)) (testFunctionLp q φ)) (U : Filter ℕ)
      (nhds ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) p q
        (zeroExtendLp hV g) (testFunctionLp q φ))) at heval
    simpa only [s, lpPairing_zeroExtend_restrict_testFunction V hV _ φ hφV] using heval
  exact (hasWeakDerivativeOn_congr_ae (MeasureTheory.ae_eq_refl _)
    (zeroExtendLp_agree_ae hV g)).mp hg

omit [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] in
/-- On a measurable set, bounds for difference quotients multiplied
by an `L∞` coefficient equal to one almost everywhere on the set give an `Lp` function
satisfying `HasWeakDerivativeOn`, with the same bound. This is the usual weak derivative
when the set is open; on arbitrary measurable sets the supported test class may be trivial.
The coefficient need not have bounded support. -/
theorem exists_Lp_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (V : Set (ℝ^n)) (hV : MeasurableSet V)
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Tendsto h atTop (nhds 0)) (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n p Set.univ) (a : DerivLp n ∞ Set.univ) (C : ℝ)
    (hbound : ∀ m, ‖a • differenceQuotientLp p i (h m) u‖ ≤ C)
    (ha_one : ∀ᵐ x ∂domainMeasure n V, a x = 1) :
    ∃ g : DerivLp n p V, ‖g‖ ≤ C ∧
      HasWeakDerivativeOn (n := n) V [i] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  apply exists_Lp_weakDerivativeOn_of_bounded_restrictedDifferenceQuotients_with_norm
    hp hp_top V hV i h hzero hne u C
  intro m
  have hmul :
      restrictDerivLp (subset_univ V) (a • differenceQuotientLp p i (h m) u) =
        restrictDerivLp (subset_univ V) (differenceQuotientLp p i (h m) u) := by
    apply MeasureTheory.Lp.ext
    have hrep := (MeasureTheory.Lp.coeFn_lpSMul (r := p) a
      (differenceQuotientLp p i (h m) u)).filter_mono
        (MeasureTheory.ae_mono (domainMeasure_le (subset_univ V)))
    filter_upwards [restrictDerivLp_apply_ae (subset_univ V)
      (a • differenceQuotientLp p i (h m) u),
      restrictDerivLp_apply_ae (subset_univ V) (differenceQuotientLp p i (h m) u),
      hrep, ha_one] with x hleft hright hprod ha
    simp only [smul_eq_mul, Pi.mul_apply] at hprod
    rw [hleft, hright, hprod, ha, one_mul]
  rw [← hmul]
  exact (norm_restrictDerivLp_le (subset_univ V)
    (a • differenceQuotientLp p i (h m) u)).trans (hbound m)

omit [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] in
/-- Domain-local form of the finite-exponent converse. For an `Lp(Ω)` function,
uniform bounds on the restricted difference quotients of its zero extension construct
an `Lp(V)` function satisfying `HasWeakDerivativeOn` on a measurable
subset `V ⊆ Ω`, with the same norm bound. For open `V` this is the usual weak derivative;
on arbitrary measurable sets the supported test class may be trivial.
If `V` has a positive buffer inside `Ω`, for example when its closure is compact and
contained in an open `Ω`, all sufficiently small translations of `V` stay in `Ω`.
Under that additional geometry these are the usual interior difference quotients.
The theorem itself assumes bounds on the zero-extension quotients and asserts no
weak derivative of the extension on all of `ℝ^n`. -/
theorem exists_Lp_weakDerivativeOn_of_bounded_zeroExtensionDifferenceQuotients_with_norm
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (Ω V : Set (ℝ^n)) (hΩ : MeasurableSet Ω) (hV : MeasurableSet V)
    (hsub : V ⊆ Ω)
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Tendsto h atTop (nhds 0)) (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n p Ω) (C : ℝ)
    (hbound : ∀ m, ‖restrictDerivLp (subset_univ V)
      (differenceQuotientLp p i (h m) (zeroExtendLp hΩ u))‖ ≤ C) :
    ∃ g : DerivLp n p V, ‖g‖ ≤ C ∧
      HasWeakDerivativeOn (n := n) V [i] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨g, hnorm, hg⟩ :=
    exists_Lp_weakDerivativeOn_of_bounded_restrictedDifferenceQuotients_with_norm
      hp hp_top V hV i h hzero hne (zeroExtendLp hΩ u) C hbound
  refine ⟨g, hnorm, ?_⟩
  exact (hasWeakDerivativeOn_congr_ae
    ((zeroExtendLp_agree_ae hΩ u).filter_mono (MeasureTheory.ae_mono (domainMeasure_le hsub)))
    (MeasureTheory.ae_eq_refl _)).mp hg

end SobolevSpace.GraphSpace.DifferenceQuotient

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace Sobolev
open SobolevSpace.GraphSpace.Rellich
open PDE.Analysis

variable {n : ℕ}

private theorem wkpBaseCoordinate_mkWkpSpaceOnOfContDiff_eq_testFunctionLp
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcs : HasCompactSupport f) :
    wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p)
        (Ω := Set.univ)
        (mkWkpSpaceOnOfContDiff
          (n := n) (k := 1) (p := p)
          (Ω := Set.univ) f hf hcs) =
      testFunctionLp p (_root_.TestFunction.mk f hf hcs (Set.subset_univ _)) := by
  apply MeasureTheory.Lp.ext
  have hU :=
    mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := p)
      (Ω := Set.univ) f hf hcs (baseIndex n 1)
  have hUvol :
      ((wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := p)
          (Ω := Set.univ)
          (mkWkpSpaceOnOfContDiff
            (n := n) (k := 1) (p := p)
            (Ω := Set.univ) f hf hcs) :
            DerivLp n p Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] f := by
    simpa [iteratedPartialDeriv, domainMeasure] using hU
  have hφ :=
    testFunctionLp_apply_ae
      (n := n) p (_root_.TestFunction.mk f hf hcs (Set.subset_univ _))
  simpa using hUvol.trans hφ.symm

private theorem wkpDerivativeCoordinate_mkWkpSpaceOnOfContDiff_eq_partialTestFunctionLp
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin n) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcs : HasCompactSupport f) :
    wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i)
        (mkWkpSpaceOnOfContDiff
          (n := n) (k := 1) (p := p)
          (Ω := Set.univ) f hf hcs) =
      partialTestFunctionLp p i
        (_root_.TestFunction.mk f hf hcs (Set.subset_univ _)) := by
  apply MeasureTheory.Lp.ext
  have hU :=
    mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := p)
      (Ω := Set.univ) f hf hcs (singleDerivIndex n i)
  have hUvol :
      ((wkpCoordinateCLM
          (n := n) (p := p) (Ω := Set.univ)
          (singleDerivIndex n i)
          (mkWkpSpaceOnOfContDiff
            (n := n) (k := 1) (p := p)
            (Ω := Set.univ) f hf hcs) :
            DerivLp n p Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume]
          fun x ↦ (∂[i] f) x := by
    simpa [singleDerivIndex_toList, iteratedPartialDeriv, domainMeasure] using hU
  have hφ :=
    partialTestFunctionLp_apply_ae
      (n := n) p i (_root_.TestFunction.mk f hf hcs (Set.subset_univ _))
  simpa using hUvol.trans hφ.symm

/-- Elementary `L²` bound requiring no Sobolev regularity. -/
theorem norm_differenceQuotientL2_le (i : Fin n) (h : ℝ)
    (u : DerivLp n 2 Set.univ) :
    ‖differenceQuotientLp 2 i h u‖ ≤ 2 * |h|⁻¹ * ‖u‖ := by
  rw [differenceQuotientL2_apply, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |h|⁻¹ * ‖translateLp 2 (coordinateStep i h) u - u‖
        ≤ |h|⁻¹ * (‖translateLp 2 (coordinateStep i h) u‖ + ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (abs_nonneg h))
    _ = 2 * |h|⁻¹ * ‖u‖ := by rw [norm_translateLp]; ring

/-- Translation is adjoint to translation by the opposite vector. -/
theorem inner_translateL2_left (a : ℝ^n) (u v : DerivLp n 2 Set.univ) :
    inner ℝ (translateLp 2 a u) v = inner ℝ u (translateLp 2 (-a) v) := by
  have hv : translateLp 2 a (translateLp 2 (-a) v) = v := by
    rw [translateLp_add, add_neg_cancel, translateLp_zero]
  calc
    inner ℝ (translateLp 2 a u) v =
        inner ℝ (translateLp 2 a u) (translateLp 2 a (translateLp 2 (-a) v)) := by rw [hv]
    _ = inner ℝ u (translateLp 2 (-a) v) :=
      (translateLp 2 a).inner_map_map u (translateLp 2 (-a) v)

/-- Discrete integration by parts for forward and backward coordinate
difference quotients, Evans §5.8.2 and §6.3.1. -/
theorem inner_differenceQuotientL2_left (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (u v : DerivLp n 2 Set.univ) :
    inner ℝ (differenceQuotientLp 2 i h u) v =
      -inner ℝ u (differenceQuotientLp 2 i (-h) v) := by
  rw [differenceQuotientL2_apply, differenceQuotientL2_apply,
    real_inner_smul_left, inner_sub_left, inner_translateL2_left,
    real_inner_smul_right, inner_sub_right]
  have hstep : coordinateStep i (-h) = -(coordinateStep i h) := by
    simp [coordinateStep]
  rw [hstep]
  field_simp

/-- Limit form of discrete integration by parts.  If forward difference
quotients of `u` and matching backward difference quotients of a test vector
`v` converge strongly, their limits satisfy the weak derivative pairing.
This is the proof-theoretic bridge used when identifying a difference-
quotient limit as a weak derivative. -/
theorem inner_limit_of_differenceQuotients
    (i : Fin n) (h : ℕ → ℝ) (hh : ∀ m, h m ≠ 0)
    (u v g w : DerivLp n 2 Set.univ)
    (hforward : Filter.Tendsto
      (fun m ↦ differenceQuotientLp 2 i (h m) u) Filter.atTop (nhds g))
    (hbackward : Filter.Tendsto
      (fun m ↦ differenceQuotientLp 2 i (-(h m)) v) Filter.atTop (nhds w)) :
    inner ℝ g v = -inner ℝ u w := by
  have hpair (m : ℕ) :
      inner ℝ (differenceQuotientLp 2 i (h m) u) v =
        -inner ℝ u (differenceQuotientLp 2 i (-(h m)) v) :=
    inner_differenceQuotientL2_left i (hh m) u v
  have hleft : Filter.Tendsto
      (fun m ↦ inner ℝ (differenceQuotientLp 2 i (h m) u) v)
      Filter.atTop (nhds (inner ℝ g v)) :=
    hforward.inner tendsto_const_nhds
  have hright : Filter.Tendsto
      (fun m ↦ -inner ℝ u (differenceQuotientLp 2 i (-(h m)) v))
      Filter.atTop (nhds (-inner ℝ u w)) :=
    (tendsto_const_nhds.inner hbackward).neg
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext m
  exact hpair m

/-- Weak-limit form of discrete integration by parts.  This is the form used
in Evans's difference-quotient characterization: only the difference
quotients of the unknown converge weakly, whereas the smooth test-function
difference quotients converge strongly. -/
theorem inner_limit_of_weak_differenceQuotients
    (i : Fin n) (h : ℕ → ℝ) (hh : ∀ m, h m ≠ 0)
    (l : Filter ℕ) [l.NeBot]
    (u v w : DerivLp n 2 Set.univ) (g : WeakSpace ℝ (DerivLp n 2 Set.univ))
    (hforward : Filter.Tendsto
      (fun m ↦ toWeakSpace ℝ (DerivLp n 2 Set.univ)
        (differenceQuotientLp 2 i (h m) u))
      l (nhds g))
    (hbackward : Filter.Tendsto
      (fun m ↦ differenceQuotientLp 2 i (-(h m)) v) l (nhds w)) :
    inner ℝ ((toWeakSpace ℝ (DerivLp n 2 Set.univ)).symm g) v =
      -inner ℝ u w := by
  have hpair (m : ℕ) :
      inner ℝ (differenceQuotientLp 2 i (h m) u) v =
        -inner ℝ u (differenceQuotientLp 2 i (-(h m)) v) :=
    inner_differenceQuotientL2_left i (hh m) u v
  have hleft : Filter.Tendsto
      (fun m ↦ inner ℝ (differenceQuotientLp 2 i (h m) u) v)
      l
      (nhds (inner ℝ ((toWeakSpace ℝ (DerivLp n 2 Set.univ)).symm g) v)) := by
    have hround (z : DerivLp n 2 Set.univ) :
        (toWeakSpace ℝ (DerivLp n 2 Set.univ)).symm
            (toWeakSpace ℝ (DerivLp n 2 Set.univ) z) = z :=
      (toWeakSpace ℝ (DerivLp n 2 Set.univ)).symm_apply_apply z
    simpa [hround, real_inner_comm, inner_smul_right] using
      WeakCompactness.tendsto_evaluation hforward (innerSL ℝ v)
  have hright : Filter.Tendsto
      (fun m ↦ -inner ℝ u (differenceQuotientLp 2 i (-(h m)) v))
      l (nhds (-inner ℝ u w)) :=
    (tendsto_const_nhds.inner hbackward).neg
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext m
  exact hpair m

/-- A uniformly `L²`-bounded sequence of coordinate difference quotients
has a weakly convergent ultrafilter refining `atTop`.  This is the
weak compactness step (11) in the proof of Evans, PDE, §5.8.2, Theorem 3(ii),
stated with an ultrafilter, so no separability assumption enters. -/
theorem exists_ultrafilter_tendsto_weak_differenceQuotients
    (i : Fin n) (h : ℕ → ℝ) (u : DerivLp n 2 Set.univ)
    (C : ℝ)
    (hbound : ∀ m, ‖differenceQuotientLp 2 i (h m) u‖ ≤ C) :
    ∃ (g : WeakSpace ℝ (DerivLp n 2 Set.univ)) (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto
        (fun m ↦ toWeakSpace ℝ (DerivLp n 2 Set.univ)
          (differenceQuotientLp 2 i (h m) u))
        U (nhds g) := by
  let q : ℕ → DerivLp n 2 Set.univ := fun m ↦ differenceQuotientLp 2 i (h m) u
  have hbounded : Bornology.IsBounded (Set.range q) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * C, fun m k ↦ ?_⟩
    rw [dist_eq_norm]
    calc
      ‖q m - q k‖ ≤ ‖q m‖ + ‖q k‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound m) (hbound k)
      _ = 2 * C := by ring
  simpa [q] using
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      Filter.atTop q hbounded

/-- The `L²` case of Evans's difference-quotient criterion in one coordinate direction.
If a sequence of nonzero steps tends to zero and the corresponding
difference quotients are bounded in `L²` by `C`, then the function has an
`L²` weak derivative in that direction with norm at most `C`. -/
theorem exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n 2 Set.univ) (C : ℝ)
    (hbound : ∀ m, ‖differenceQuotientLp 2 i (h m) u‖ ≤ C) :
    ∃ g : DerivLp n 2 Set.univ, ‖g‖ ≤ C ∧
      HasWeakDerivativeOn (n := n) Set.univ [i]
        (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨gw, U, hU, hweak⟩ :=
    exists_ultrafilter_tendsto_weak_differenceQuotients i h u C hbound
  let g : DerivLp n 2 Set.univ :=
    (toWeakSpace ℝ (DerivLp n 2 Set.univ)).symm gw
  refine ⟨g, ?_, ?_⟩
  · have hnorm := WeakCompactness.norm_le_of_tendsto_of_norm_le hweak
      (Filter.Eventually.of_forall hbound)
    simpa [g] using hnorm
  apply hasWeakDerivativeOn_of_tendsto_differenceQuotient_pairings
    (p := 2) (q := 2) (by norm_num) i h hzero hne (U : Filter ℕ) hU u g Set.univ
  intro φ _hφ
  simpa only [g, LinearEquiv.symm_apply_apply, ContinuousLinearMap.flip_apply] using
    WeakCompactness.tendsto_evaluation hweak
      (((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) 2 2).flip
        (testFunctionLp 2 φ))

/-- Qualitative corollary of the bounded difference-quotient criterion. -/
theorem exists_L2_weakDerivative_of_bounded_differenceQuotients
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n 2 Set.univ) (C : ℝ)
    (hbound : ∀ m, ‖differenceQuotientLp 2 i (h m) u‖ ≤ C) :
    ∃ g : DerivLp n 2 Set.univ,
      HasWeakDerivativeOn (n := n) Set.univ [i]
        (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ :=
    exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm
      i h hzero hne u C hbound
  exact ⟨g, hg⟩

/-- Local form of Evans's `L²` difference-quotient criterion.  It is enough
to bound the quotients after multiplication by a fixed `L∞` cutoff which is
identically one on test functions supported in `V`.

The formulation records only the action of the cutoff on test
vectors, so it applies equally to a smooth cutoff known
pointwise to equal one near `V`, or to any bounded multiplier with the same
local action. -/
theorem exists_L2_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n 2 Set.univ) (q : DerivLp n ∞ Set.univ)
    (V : Set (ℝ^n)) (C : ℝ)
    (hbound : ∀ m, ‖q • differenceQuotientLp 2 i (h m) u‖ ≤ C)
    (hq_one : ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ.toFun ⊆ V →
        q • testFunctionL2 φ = testFunctionL2 φ) :
    ∃ g : DerivLp n 2 Set.univ, ‖g‖ ≤ C ∧
      HasWeakDerivativeOn (n := n) V [i]
        (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  let s : ℕ → DerivLp n 2 Set.univ := fun m ↦
    q • differenceQuotientLp 2 i (h m) u
  have hsbounded : Bornology.IsBounded (Set.range s) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * C, fun m k ↦ ?_⟩
    rw [dist_eq_norm]
    calc
      ‖s m - s k‖ ≤ ‖s m‖ + ‖s k‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound m) (hbound k)
      _ = 2 * C := by ring
  obtain ⟨gw, U, hU, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      Filter.atTop s hsbounded
  let g : DerivLp n 2 Set.univ :=
    (toWeakSpace ℝ (DerivLp n 2 Set.univ)).symm gw
  refine ⟨g, ?_, ?_⟩
  · have hnorm := WeakCompactness.norm_le_of_tendsto_of_norm_le hweak
      (Filter.Eventually.of_forall hbound)
    simpa [g, s] using hnorm
  apply hasWeakDerivativeOn_of_tendsto_differenceQuotient_pairings
    (p := 2) (q := 2) (by norm_num) i h hzero hne (U : Filter ℕ) hU u g V
  intro φ hφV
  have hq : q • testFunctionLp 2 φ = testFunctionLp 2 φ := hq_one φ hφV
  have heval := WeakCompactness.tendsto_evaluation hweak
    (((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n Set.univ) 2 2).flip
      (testFunctionLp 2 φ))
  change Filter.Tendsto
    (fun m ↦ (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (domainMeasure n Set.univ) 2 2
      (q • differenceQuotientLp 2 i (h m) u) (testFunctionLp 2 φ))
    (U : Filter ℕ)
    (nhds ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (domainMeasure n Set.univ) 2 2 g (testFunctionLp 2 φ))) at heval
  simpa only [MeasureTheory.Lp.lpPairing_lpSMul_left, hq] using heval

/-- Qualitative local corollary of the bounded localized
difference-quotient criterion. -/
theorem exists_L2_weakDerivativeOn_of_bounded_localizedDifferenceQuotients
    (i : Fin n) (h : ℕ → ℝ)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n 2 Set.univ) (q : DerivLp n ∞ Set.univ)
    (V : Set (ℝ^n)) (C : ℝ)
    (hbound : ∀ m, ‖q • differenceQuotientLp 2 i (h m) u‖ ≤ C)
    (hq_one : ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ.toFun ⊆ V →
        q • testFunctionL2 φ = testFunctionL2 φ) :
    ∃ g : DerivLp n 2 Set.univ,
      HasWeakDerivativeOn (n := n) V [i]
        (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ :=
    exists_L2_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm
      i h hzero hne u q V C hbound hq_one
  exact ⟨g, hg⟩

/-- A smooth cutoff which is pointwise equal to one on `V` acts as the
identity on every `L²` test vector supported in `V`.  This discharges the
semantic cutoff hypothesis in the localized difference-quotient criterion. -/
theorem testFunctionLpTop_smul_testFunctionL2_eq_of_eq_one
    (η φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (V : Set (ℝ^n))
    (hηone : ∀ x ∈ V, η.toFun x = 1)
    (hφV : tsupport φ.toFun ⊆ V) :
    testFunctionLpTop (n := n) (Ω := Set.univ) η • testFunctionL2 φ =
      testFunctionL2 φ := by
  apply MeasureTheory.Lp.ext
  have hmul := MeasureTheory.Lp.coeFn_lpSMul (r := 2)
    (testFunctionLpTop (n := n) (Ω := Set.univ) η) (testFunctionL2 φ)
  have hη := testFunctionLpTop_apply_ae (n := n) (Ω := Set.univ) η
  have hφ :
      ((testFunctionL2 φ : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Set.univ] φ.toFun := by
    simpa [domainMeasure] using testFunctionL2_apply_ae φ
  filter_upwards [hmul, hη, hφ] with x hmulx hηx hφx
  rw [hmulx]
  change
    ((testFunctionLpTop (n := n) (Ω := Set.univ) η : ℝ^n → ℝ) x) *
        ((testFunctionL2 φ : ℝ^n → ℝ) x) =
      ((testFunctionL2 φ : ℝ^n → ℝ) x)
  rw [hηx, hφx]
  by_cases hx : φ.toFun x = 0
  · simp [hx]
  · have hxV : x ∈ V := hφV (subset_tsupport φ.toFun (by simpa [Function.support]))
    rw [hηone x hxV]
    simp

/-- Evans's global `L²` difference-quotient characterization of `H¹`.
Uniform coordinatewise quotient bounds produce a bundled
`H¹(ℝ^n)` representative of the original `L²` function. -/
theorem exists_H1_of_bounded_differenceQuotients
    (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (u : DerivLp n 2 Set.univ) (C : Fin n → ℝ)
    (hbound : ∀ i m, ‖differenceQuotientLp 2 i (h m) u‖ ≤ C i) :
    ∃ U : H¹((Set.univ : Set (ℝ^n))),
      ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] (u : ℝ^n → ℝ)) := by
  choose g hg using fun i ↦
    exists_L2_weakDerivative_of_bounded_differenceQuotients
      i h hzero hne u (C i) (hbound i)
  let f0 : ℝ^n → ℝ := (u : ℝ^n → ℝ)
  let d : DerivIndex n 1 → ℝ^n → ℝ :=
    firstOrderRows f0 fun i ↦ (g i : ℝ^n → ℝ)
  have hbase : d (baseIndex n 1) = f0 := by simp [d]
  have hmem : ∀ a : DerivIndex n 1,
      MemLp (d a) 2 (domainMeasure n Set.univ) := by
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
    · subst a
      simpa [d, f0] using MeasureTheory.Lp.memLp u
    · subst a
      simpa [d] using MeasureTheory.Lp.memLp (g i)
  have hu0 : HasWeakDerivativeOn (n := n) Set.univ [] f0 f0 := by
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp u) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact hasWeakDerivativeOn_nil hloc
  have hweak : ∀ a : DerivIndex n 1,
      HasWeakDerivativeOn (n := n) Set.univ a.toList f0 (d a) := by
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
    · subst a
      simpa [d] using hu0
    · subst a
      simpa [d, f0] using hg i
  let U := mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
      f0 d hbase hmem hweak
  refine ⟨U, ?_⟩
  have hU := mkWkpSpaceOnOfWeakDerivatives_apply_ae
    (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
      f0 d hbase hmem hweak (baseIndex n 1)
  rw [hbase] at hU
  simpa [U, f0, domainMeasure] using hU

variable {Ω : Set (ℝ^n)}

/-- Difference quotient of the global zero extension of an `H¹₀(Ω)` function. -/
noncomputable def zeroExtensionDifferenceQuotient
    (hΩmeas : MeasurableSet Ω) (i : Fin n) (h : ℝ) :
    H¹₀(Ω) →L[ℝ] DerivLp n 2 Set.univ :=
  h⁻¹ • translationDefectCLM (n := n) (Ω := Ω) hΩmeas (coordinateStep i h)

/-- Unfolding lemma: the zero-extension difference quotient is `h⁻¹ (τ_{h eᵢ} E₀u - E₀u)` on the
`L²` zero extension `E₀u` of the base coordinate. -/
@[simp]
theorem zeroExtensionDifferenceQuotient_apply
    (hΩmeas : MeasurableSet Ω) (i : Fin n) (h : ℝ)
    (u : H¹₀(Ω)) :
    zeroExtensionDifferenceQuotient hΩmeas i h u =
      h⁻¹ • (translateLp 2 (coordinateStep i h)
          (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) -
        zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) := by
  rfl

/-- For measurable `Ω`, a coordinate `i` and a step `h ≠ 0`, the difference quotient
`D_i^h(E₀u)` of the zero extension of `u ∈ H¹₀(Ω)` has `L²(ℝ^n)` norm at most `‖u‖_{H¹}`. -/
theorem zeroExtensionDifferenceQuotient.norm_le
    (hΩmeas : MeasurableSet Ω) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(Ω)) :
    ‖zeroExtensionDifferenceQuotient hΩmeas i h u‖ ≤ ‖u‖ := by
  rw [zeroExtensionDifferenceQuotient_apply, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |h|⁻¹ * ‖translateLp 2 (coordinateStep i h)
          (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) -
        zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u‖
      ≤ |h|⁻¹ * (‖coordinateStep i h‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left
          (translationDefectCLM.norm_le hΩmeas (coordinateStep i h) u)
          (inv_nonneg.mpr (abs_nonneg h))
    _ = ‖u‖ := by simp [norm_coordinateStep, hh]

/-- Coordinate form of the uniform difference-quotient estimate for the
base component of the global zero extension. -/
theorem differenceQuotientL2.zeroExtend_base_norm_le
    (hΩmeas : MeasurableSet Ω) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(Ω)) :
    ‖differenceQuotientLp 2 i h
      (((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖ ≤ ‖u‖ := by
  change ‖zeroExtensionDifferenceQuotient hΩmeas i h u‖ ≤ ‖u‖
  exact zeroExtensionDifferenceQuotient.norm_le hΩmeas i hh u

/-- The sharp whole-space estimate for a coordinate difference quotient of a
finite-exponent `W¹ᵖ` field, stated directly at an extended-real exponent. -/
theorem norm_differenceQuotientLp_base_le_deriv_of_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (U : W^{1,p}(ℝ^n)) :
    ‖differenceQuotientLp p i h
        (wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := p)
          (Ω := Set.univ) U)‖ ≤
      ‖wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i) U‖ := by
  let T :
      W^{1,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
    (differenceQuotientLp p i h).comp
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p)
          (Ω := Set.univ))
  let D :
      W^{1,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
    wkpCoordinateCLM
      (n := n) (p := p) (Ω := Set.univ)
      (singleDerivIndex n i)
  let S : Set (W^{1,p}(ℝ^n)) :=
    {V | ‖T V‖ ≤ ‖D V‖}
  have hSclosed : IsClosed S :=
    isClosed_le (by fun_prop) (by fun_prop)
  obtain ⟨f_m, hf_m, hcs_m, hnorm⟩ :=
    globalApproximation_WkpSpace
      (Approximation.standardMollifier n) hp_top 1 U
  let U_m : ℕ → W^{1,p}(ℝ^n) := fun m ↦
    mkWkpSpaceOnOfContDiff
      (n := n) (k := 1) (p := p)
      (Ω := Set.univ) (f_m m) (hf_m m) (hcs_m m)
  have hUm : Filter.Tendsto U_m Filter.atTop (𝓝 U) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa [U_m] using hnorm
  have hUmS : ∀ m, U_m m ∈ S := by
    intro m
    have hbase :=
      wkpBaseCoordinate_mkWkpSpaceOnOfContDiff_eq_testFunctionLp
        (p := p) (f_m m) (hf_m m) (hcs_m m)
    have hderiv :=
      wkpDerivativeCoordinate_mkWkpSpaceOnOfContDiff_eq_partialTestFunctionLp
        (p := p) i (f_m m) (hf_m m) (hcs_m m)
    change ‖T (U_m m)‖ ≤ ‖D (U_m m)‖
    simpa [T, D, U_m, hbase, hderiv] using
      norm_differenceQuotientLp_testFunction_le_of_ne_top
        (n := n) p hp_top i hh
          (_root_.TestFunction.mk (f_m m) (hf_m m) (hcs_m m) (Set.subset_univ _))
  have hUS : U ∈ S :=
    hSclosed.mem_of_tendsto hUm (Filter.Eventually.of_forall hUmS)
  simpa [S, T, D] using hUS

/-- Coordinate difference quotients of a whole-space finite-exponent `W¹ᵖ`
field converge strongly in `Lᵖ` to the corresponding weak derivative. This
is the exponent-native form used by concrete exponents such as `p = 2`. -/
theorem tendsto_differenceQuotientLp_base_of_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (i : Fin n) (U : W^{1,p}(ℝ^n))
    (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (𝓝 0))
    (hne : ∀ m, h m ≠ 0) :
    Filter.Tendsto
      (fun m ↦ differenceQuotientLp p i (h m)
        (wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := p)
          (Ω := Set.univ) U))
      Filter.atTop
      (𝓝 (wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i) U)) := by
  let T : ℕ →
      W^{1,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ := fun m ↦
    (differenceQuotientLp p i (h m)).comp
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p)
          (Ω := Set.univ))
  let D :
      W^{1,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
    wkpCoordinateCLM
      (n := n) (p := p) (Ω := Set.univ)
      (singleDerivIndex n i)
  have hTnorm (m : ℕ) : ‖T m‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro V
    calc
      ‖T m V‖ ≤
          ‖wkpCoordinateCLM
            (n := n) (p := p) (Ω := Set.univ)
            (singleDerivIndex n i) V‖ := by
        simpa [T] using
          norm_differenceQuotientLp_base_le_deriv_of_ne_top
            (n := n) p hp_top i (hne m) V
      _ ≤ ‖V‖ :=
        PiLp.norm_apply_le
          (V : WkpAmbientOn n 1 p Set.univ)
          (singleDerivIndex n i)
      _ = 1 * ‖V‖ := by ring
  have hLip (m : ℕ) : LipschitzWith 1 (T m) :=
    (T m).lipschitzWith_of_opNorm_le (by simpa using hTnorm m)
  have hEqui :
      Equicontinuous
        (fun m ↦ (T m :
          W^{1,p}(ℝ^n) → DerivLp n p Set.univ)) :=
    (LipschitzWith.uniformEquicontinuous
      (fun m ↦ (T m :
        W^{1,p}(ℝ^n) → DerivLp n p Set.univ))
      1 hLip).equicontinuous
  let S : Set (W^{1,p}(ℝ^n)) :=
    {V | Filter.Tendsto (fun m ↦ T m V) Filter.atTop (𝓝 (D V))}
  have hSclosed : IsClosed S :=
    hEqui.isClosed_setOfPred_tendsto D.continuous
  obtain ⟨f_m, hf_m, hcs_m, hnorm⟩ :=
    globalApproximation_WkpSpace
      (Approximation.standardMollifier n) hp_top 1 U
  let U_m : ℕ → W^{1,p}(ℝ^n) := fun m ↦
    mkWkpSpaceOnOfContDiff
      (n := n) (k := 1) (p := p)
      (Ω := Set.univ) (f_m m) (hf_m m) (hcs_m m)
  have hUm : Filter.Tendsto U_m Filter.atTop (𝓝 U) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa [U_m] using hnorm
  have hUmS : ∀ m, U_m m ∈ S := by
    intro m
    have hbase :=
      wkpBaseCoordinate_mkWkpSpaceOnOfContDiff_eq_testFunctionLp
        (p := p) (f_m m) (hf_m m) (hcs_m m)
    have hderiv :=
      wkpDerivativeCoordinate_mkWkpSpaceOnOfContDiff_eq_partialTestFunctionLp
        (p := p) i (f_m m) (hf_m m) (hcs_m m)
    change Filter.Tendsto
      (fun k ↦ T k (U_m m)) Filter.atTop (𝓝 (D (U_m m)))
    simpa [T, D, U_m, hbase, hderiv] using
      tendsto_differenceQuotientLp_testFunction
        (n := n) p hp_top i
          (_root_.TestFunction.mk (f_m m) (hf_m m) (hcs_m m) (Set.subset_univ _))
          h hzero hne
  have hUS : U ∈ S :=
    hSclosed.mem_of_tendsto hUm (Filter.Eventually.of_forall hUmS)
  simpa [S, T, D] using hUS

/-- On the whole space, every `H¹` field lies in `H¹₀`. -/
theorem h1Space_mem_H10_univ (U : H¹(ℝ^n)) :
    U ∈ (h10SubmoduleOn
      (n := n) (Ω := (Set.univ : Set (ℝ^n)))).toSubmodule := by
  simpa [h10SubmoduleOn] using
    (wkpSpace_mem_Wkp0_univ
      (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (by norm_num) U)

/-- A whole-space `H¹` field controls the `L²` norm of every nonzero
coordinate difference quotient of its base coordinate. -/
theorem norm_differenceQuotientL2_base_le
    (i : Fin n) {h : ℝ} (hh : h ≠ 0) (U : H¹(ℝ^n)) :
    ‖differenceQuotientLp 2 i h
      ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖ ≤ ‖U‖ := by
  calc
    ‖differenceQuotientLp 2 i h
        ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖
        ≤ ‖(U : WkpAmbientOn n 1 2 Set.univ)
          (singleDerivIndex n i)‖ := by
      exact norm_differenceQuotientLp_base_le_deriv_of_ne_top
        (n := n) 2 (by norm_num) i hh U
    _ ≤ ‖U‖ :=
      PiLp.norm_apply_le
        (U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)

/-- Coordinate difference quotients of the base coordinate of a whole-space
`H¹` field converge strongly in `L²` to its corresponding weak derivative. -/
theorem tendsto_differenceQuotientL2_base
    (i : Fin n) (U : H¹(ℝ^n))
    (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (𝓝 0))
    (hne : ∀ m, h m ≠ 0) :
    Filter.Tendsto
      (fun m ↦ differenceQuotientLp 2 i (h m)
        ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)))
      Filter.atTop
      (𝓝 ((U : WkpAmbientOn n 1 2 Set.univ)
        (singleDerivIndex n i))) := by
  exact tendsto_differenceQuotientLp_base_of_ne_top
    (n := n) 2 (by norm_num) i U h hzero hne

end SobolevSpace.GraphSpace.DifferenceQuotient
