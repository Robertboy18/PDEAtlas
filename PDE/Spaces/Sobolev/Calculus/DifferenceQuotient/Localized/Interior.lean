/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.Coordinates
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalForward
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalPairing
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Interior quotient tests for arbitrary first-order Sobolev fields

A larger cutoff makes an arbitrary `H¹` field extendible by zero. Where
that cutoff is one, the extension retains every original weak derivative.
Multiplication by a smaller cutoff then removes the choice of extension
from each difference quotient, provided both evaluation points lie in the
region of agreement.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Filter
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {Ω S : Set (ℝ^n)}

/-- Zero extension after an interior cutoff preserves the entire first jet
on every open region where the cutoff is one. The input has no trace condition. -/
theorem zeroExtend_cutoffH1ToH10_coordinate_eq_on
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1) (u : H¹(Ω))
    (a : DerivIndex n 1) :
    ((ZeroTrace.zeroExtendH10 hΩ.measurableSet
        (cutoffH1ToH10 hΩ χ hχ u)).val a : ℝ^n → ℝ)
      =ᵐ[domainMeasure n S] (u.val a : ℝ^n → ℝ) := by
  let v := cutoffH1ToH10 hΩ χ hχ u
  let Z := ZeroTrace.zeroExtendH10 hΩ.measurableSet v
  have hzero :
      (Z.val (baseIndex n 1) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] (v.val.val (baseIndex n 1) : ℝ^n → ℝ) :=
    Extension.Lp.zeroExtendLp_agree_ae hΩ.measurableSet _
  have heq : restrictCLM hS.measurableSet (subset_univ S) Z =
      restrictCLM hS.measurableSet hSΩ u := by
    apply WkpSpaceOn.ext_of_base_ae hS
    filter_upwards
      [restrictCLM_apply_ae hS.measurableSet (subset_univ S) Z (baseIndex n 1),
        restrictCLM_apply_ae hS.measurableSet hSΩ u (baseIndex n 1),
        hzero.filter_mono (ae_mono (domainMeasure_le hSΩ)),
        (cutoffCLM_base_apply_ae (p := 2) χ u).filter_mono
          (ae_mono (domainMeasure_le hSΩ)),
        ae_restrict_mem hS.measurableSet] with x hx hy hz hc hs
    have hc' : v.val.val (baseIndex n 1) x = u.val (baseIndex n 1) x := by
      change (((cutoffH1ToH10 hΩ χ hχ u : H¹₀(Ω)) :
        H¹(Ω)).val (baseIndex n 1)) x = _
      rw [cutoffH1ToH10_apply_coe]
      simpa only [hone x hs, one_mul] using hc
    exact hx.trans (hz.trans (hc'.trans hy.symm))
  have hr := restrictCLM_apply_ae hS.measurableSet (subset_univ S) Z a
  rw [heq] at hr
  exact hr.symm.trans (restrictCLM_apply_ae hS.measurableSet hSΩ u a)

/-- A cutoff-weighted quotient depends only on the input on the cutoff
support and its translate. Both signs of the step, including zero, are allowed. -/
theorem testFunction_smul_differenceQuotient_eq_of_agree
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hS : MeasurableSet S)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    (k : Fin n) (h : ℝ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (f g : DerivLp n p univ) (hfg : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n S] g) :
    testFunctionLpTop (Ω := univ) η • differenceQuotientLp p k h f =
      testFunctionLpTop (Ω := univ) η • differenceQuotientLp p k h g := by
  have hag : ∀ᵐ x ∂volume, x ∈ S → f x = g x := (ae_restrict_iff' hS).mp hfg
  have htrans := (measurePreserving_add_right (volume : Measure (ℝ^n))
    (coordinateStep k h)).quasiMeasurePreserving.ae hag
  apply Lp.ext
  have hleft := Lp.coeFn_lpSMul (r := p) (testFunctionLpTop (Ω := univ) η)
    (differenceQuotientLp p k h f)
  have hright := Lp.coeFn_lpSMul (r := p) (testFunctionLpTop (Ω := univ) η)
    (differenceQuotientLp p k h g)
  have heta := testFunctionLpTop_apply_ae (Ω := univ) η
  simp only [domainMeasure, Measure.restrict_univ] at hleft hright heta ⊢
  filter_upwards [hleft, hright, heta,
    differenceQuotientLp_apply_ae p k h f, differenceQuotientLp_apply_ae p k h g,
    hag, htrans] with x hl hr heta hf hg hx hxt
  rw [hl, hr]
  change testFunctionLpTop (Ω := univ) η x * differenceQuotientLp p k h f x =
    testFunctionLpTop (Ω := univ) η x * differenceQuotientLp p k h g x
  rw [heta]
  by_cases hxη : η.toFun x = 0
  · simp only [hxη, zero_mul]
  · have hxs := subset_tsupport η.toFun hxη
    rw [hf, hg, hx (hη hxs), hxt (hshift hxs)]

/-- After multiplication by the smaller cutoff, every quotient of the
cutoff extension equals the quotient of the original coordinate extended
as an `L²` function. The input need not have a Sobolev zero extension. -/
theorem weighted_differenceQuotient_cutoffH1ToH10
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    (k : Fin n) (h : ℝ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (u : H¹(Ω)) (a : DerivIndex n 1) :
    testFunctionLpTop (Ω := univ) η • differenceQuotientLp 2 k h
        ((ZeroTrace.zeroExtendH10 hΩ.measurableSet
          (cutoffH1ToH10 hΩ χ hχ u)).val a) =
      testFunctionLpTop (Ω := univ) η • differenceQuotientLp 2 k h
        (Extension.Lp.zeroExtendLp hΩ.measurableSet (u.val a)) := by
  apply testFunction_smul_differenceQuotient_eq_of_agree
    hS.measurableSet η hη k h hshift
  exact (zeroExtend_cutoffH1ToH10_coordinate_eq_on hΩ hS hSΩ χ hχ hone u a).trans
    ((Extension.Lp.zeroExtendLp_agree_ae hΩ.measurableSet (u.val a)).filter_mono
      (ae_mono (domainMeasure_le hSΩ))).symm

/-- The localized forward field obtained from an arbitrary `H¹` input has
the original base coordinate and every original weak derivative in its
product-rule formula. The larger cutoff disappears from both formulas. -/
theorem zeroExtended_localizedDifference_cutoffH1ToH10
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    (k : Fin n) (h : ℝ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (u : H¹(Ω)) :
    let E := Extension.Lp.zeroExtendLp (p := 2) hΩ.measurableSet
    let w := localizedDifferenceH10 hΩ η (hη.trans hSΩ) k h
      (cutoffH1ToH10 hΩ χ hχ u)
    let Z := ZeroTrace.zeroExtendH10 hΩ.measurableSet w
    Z.val (baseIndex n 1) =
      testFunctionLpTop (Ω := univ) (squaredCutoff η) •
        differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))) ∧
    ∀ i : Fin n, Z.val (singleDerivIndex n i) =
      testFunctionLpTop (Ω := univ) (squaredCutoff η) •
          differenceQuotientLp 2 k h (E (u.val (singleDerivIndex n i))) +
        partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i •
          differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))) := by
  let v := cutoffH1ToH10 hΩ χ hχ u
  let U := ZeroTrace.zeroExtendH10 hΩ.measurableSet v
  let E := Extension.Lp.zeroExtendLp (p := 2) hΩ.measurableSet
  have hη2 := (tsupport_squaredCutoff_subset η).trans hη
  have hshift2 :
      MapsTo (fun x ↦ x + coordinateStep k h) (tsupport (squaredCutoff η).toFun) S :=
    fun _ hx ↦ hshift (tsupport_squaredCutoff_subset η hx)
  have hsquared (a : DerivIndex n 1) :
      testFunctionLpTop (Ω := univ) (squaredCutoff η) •
          differenceQuotientLp 2 k h (U.val a) =
        testFunctionLpTop (Ω := univ) (squaredCutoff η) •
          differenceQuotientLp 2 k h (E (u.val a)) :=
    weighted_differenceQuotient_cutoffH1ToH10 hΩ hS hSΩ χ hχ hone
      (squaredCutoff η) hη2 k h hshift2 u a
  have hbase := weighted_differenceQuotient_cutoffH1ToH10 hΩ hS hSΩ χ hχ hone
    η hη k h hshift u (baseIndex n 1)
  change testFunctionLpTop (Ω := univ) η •
      differenceQuotientLp 2 k h (U.val (baseIndex n 1)) =
    testFunctionLpTop (Ω := univ) η •
      differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))) at hbase
  have hpartial (i : Fin n) :
      partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i •
          differenceQuotientLp 2 k h (U.val (baseIndex n 1)) =
        partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i •
          differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))) := by
    rw [partialSquaredCutoff_smul, partialSquaredCutoff_smul]
    simp only [lpSMul_top_top_two_comm (testFunctionLpTop (Ω := univ) η),
      hbase]
  constructor
  · exact (zeroExtendedBase_localizedDifferenceH10 hΩ η (hη.trans hSΩ) k h v).trans
      (hsquared (baseIndex n 1))
  · intro i
    exact (zeroExtendedDeriv_localizedDifferenceH10 hΩ η (hη.trans hSΩ) k h v i).trans
      (congrArg₂ (· + ·) (hsquared (singleDerivIndex n i)) (hpartial i))

/-- The signed backward test for arbitrary `H¹` data. Its
zero trace follows from the collar, and all its coordinates are expressed
using the original data. This statement has no weak-equation premise. -/
theorem exists_interior_backward_test
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    (k : Fin n) (h : ℝ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (u : H¹(Ω)) :
    let E := Extension.Lp.zeroExtendLp (p := 2) hΩ.measurableSet
    ∃ v : H¹₀(Ω),
      baseCoordCLM v = -restrictDerivLp (subset_univ Ω)
        (differenceQuotientLp 2 k (-h)
          (testFunctionLpTop (Ω := univ) (squaredCutoff η) •
            differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))))) ∧
      ∀ i : Fin n, derivCoordCLM i v = -restrictDerivLp (subset_univ Ω)
        (differenceQuotientLp 2 k (-h)
          (testFunctionLpTop (Ω := univ) (squaredCutoff η) •
              differenceQuotientLp 2 k h (E (u.val (singleDerivIndex n i))) +
            partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i •
              differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))))) := by
  dsimp only
  -- a collar of the shifted support inside `Ω`: the shifted support is the translate of the
  -- compact support of `η` by `h eₖ`, which lies in `S ⊆ Ω`
  obtain ⟨δ, hδ, hcollar⟩ : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω := by
    have hK : IsCompact (tsupport η.toFun) := by
      simpa [HasCompactSupport] using η.hasCompactSupport
    refine IsCompact.exists_cthickening_subset_open ?_ hΩ ?_
    · exact (Homeomorph.addRight (coordinateStep k (-h))).isCompact_preimage.mpr hK
    · intro x hx
      have hx' : x + coordinateStep k (-h) + coordinateStep k h = x := by
        simp [coordinateStep]
      exact hSΩ (hx' ▸ hshift hx)
  let uχ := cutoffH1ToH10 hΩ χ hχ u
  let v := backwardLocalizedDifferenceH10 hΩ η (hη.trans hSΩ) k h uχ hδ hcollar
  obtain ⟨hbase, hderiv⟩ := zeroExtended_localizedDifference_cutoffH1ToH10
    hΩ hS hSΩ χ hχ hone η hη k h hshift u
  refine ⟨v, ?_, ?_⟩
  · rw [baseCoord_backwardLocalizedDifferenceH10, hbase]
  · intro i
    rw [derivCoord_backwardLocalizedDifferenceH10, hderiv i]

/-- Test an original weak divergence equation by the interior
backward test. The principal pairing and cutoff error both use quotients
of the original coordinates. The input may have arbitrary boundary trace. -/
theorem interior_backward_test_identity
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (u : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (q i) (derivCoordCLM i v)) = inner ℝ f (baseCoordCLM v)) :
    let E := Extension.Lp.zeroExtendLp (p := 2) hΩ.measurableSet
    (∑ i, inner ℝ (differenceQuotientLp 2 k h (E (q i)))
      (testFunctionLpTop (Ω := univ) (squaredCutoff η) •
        differenceQuotientLp 2 k h (E (u.val (singleDerivIndex n i))))) +
    (∑ i, inner ℝ (differenceQuotientLp 2 k h (E (q i)))
      (partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i •
        differenceQuotientLp 2 k h (E (u.val (baseIndex n 1))))) =
      inner ℝ f (-restrictDerivLp (subset_univ Ω)
        (differenceQuotientLp 2 k (-h)
          (testFunctionLpTop (Ω := univ) (squaredCutoff η) •
            differenceQuotientLp 2 k h (E (u.val (baseIndex n 1)))))) := by
  obtain ⟨v, hbase, hderiv⟩ := exists_interior_backward_test
    hΩ hS hSΩ χ hχ hone η hη k h hshift u
  have hv := hweak v
  simp only [hderiv, inner_neg_restrict_backwardDifference_eq hΩ.measurableSet k hh,
    inner_add_right, Finset.sum_add_distrib] at hv
  rw [hbase] at hv
  exact hv

end SobolevSpace.GraphSpace.DifferenceQuotient
