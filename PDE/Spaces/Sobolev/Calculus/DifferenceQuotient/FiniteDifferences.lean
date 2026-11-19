/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.CoefficientCommutator
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Operators

/-!
# Bundled finite-difference calculus

The exact Leibniz rule for bundled `Lᵖ` difference quotients, and the passage from an
abstract `L^∞` coefficient class to a concrete Lipschitz representative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, pp. 328-331, for difference
  quotients in the interior regularity argument, with the summation by parts formula (16) and the
  product rule (17) `D_k^h(vw) = v^h D_k^h w + w D_k^h v`, `v^h(x) = v(x + h e_k)`, p. 329.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace
open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}

/-- Exact `Lp` Leibniz rule for a bounded coefficient and an `L²` field.
The coefficient in the principal term is translated, exactly as in Evans's product rule
§6.3.1, (17). -/
theorem differenceQuotientL2_lpSMul
    (i : Fin n) (h : ℝ)
    (a : DerivLp n ∞ Set.univ) (u : DerivLp n 2 Set.univ) :
    differenceQuotientLp 2 i h (a • u) =
      translateLp ∞ (coordinateStep i h) a • differenceQuotientLp 2 i h u +
        differenceQuotientLp ∞ i h a • u := by
  rw [differenceQuotientL2_apply, translateLp_lpSMul]
  rw [differenceQuotientL2_apply, differenceQuotientLp_apply]
  apply MeasureTheory.Lp.ext
  have hleft := MeasureTheory.Lp.coeFn_smul h⁻¹
    (translateLp ∞ (coordinateStep i h) a •
      translateLp 2 (coordinateStep i h) u - a • u)
  have hprincipal := mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞))
    (translateLp ∞ (coordinateStep i h) a)
    (h⁻¹ • (translateLp 2 (coordinateStep i h) u - u) :
      DerivLp n 2 Set.univ)
  have hcommutator := mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞))
    (h⁻¹ • (translateLp ∞ (coordinateStep i h) a - a) :
      DerivLp n ∞ Set.univ) u
  have hsum := MeasureTheory.Lp.coeFn_add
    (translateLp ∞ (coordinateStep i h) a •
      (h⁻¹ • (translateLp 2 (coordinateStep i h) u - u)))
    ((h⁻¹ • (translateLp ∞ (coordinateStep i h) a - a)) • u)
  have htranslatedProduct := mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞))
    (translateLp ∞ (coordinateStep i h) a)
    (translateLp 2 (coordinateStep i h) u)
  have horiginalProduct := mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞)) a u
  have hproductSub := MeasureTheory.Lp.coeFn_sub
    (translateLp ∞ (coordinateStep i h) a •
      translateLp 2 (coordinateStep i h) u) (a • u)
  have hsubU := MeasureTheory.Lp.coeFn_sub
    (translateLp 2 (coordinateStep i h) u) u
  have hsubA := MeasureTheory.Lp.coeFn_sub
    (translateLp ∞ (coordinateStep i h) a) a
  have hscaleU := MeasureTheory.Lp.coeFn_smul h⁻¹
    (translateLp 2 (coordinateStep i h) u - u)
  have hscaleA := MeasureTheory.Lp.coeFn_smul h⁻¹
    (translateLp ∞ (coordinateStep i h) a - a)
  filter_upwards [hleft, hprincipal, hcommutator, hsum,
    htranslatedProduct, horiginalProduct, hproductSub,
    hsubU, hsubA, hscaleU, hscaleA] with
    x hxleft hxprincipal hxcommutator hxsum hxtranslated hxoriginal
      hxproductSub hxsubU hxsubA hxscaleU hxscaleA
  simp only [mulLpLeft_apply] at hxprincipal hxcommutator hxtranslated hxoriginal
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at *
  rw [hxleft, hxproductSub, hxtranslated, hxoriginal, hxsum, hxprincipal, hxscaleU,
    hxsubU, hxcommutator, hxscaleA, hxsubA]
  ring

/-- The abstract global `L∞` difference quotient agrees with the concrete
quotient of any Lipschitz representative.  This connects the exact `Lp`
Leibniz rule to the quantitative coefficient bounds. -/
theorem differenceQuotientLp_top_eq_coefficientDifferenceLInf
    (i : Fin n) (a : DerivLp n ∞ Set.univ) (f : ℝ^n → ℝ)
    {C : NNReal} (hf : LipschitzWith C f)
    (ha : (a : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume] f)
    (h : ℝ) (hh : h ≠ 0) :
    differenceQuotientLp ∞ i h a =
      coefficientDifferenceLInf i f hf h hh := by
  apply MeasureTheory.Lp.ext
  have hdq := differenceQuotientLp_apply_ae (n := n) ∞ i h a
  have hcoeff := coefficientDifferenceLInf_apply_ae i f hf h hh
  have hshift :
      (fun x ↦ (a : ℝ^n → ℝ) (x + coordinateStep i h))
        =ᵐ[MeasureTheory.volume]
          fun x ↦ f (x + coordinateStep i h) := by
    have hpres : MeasurePreserving
        (translationContinuousMap (coordinateStep i h))
        MeasureTheory.volume MeasureTheory.volume := by
      simpa [domainMeasure] using
        translationMeasurePreserving (n := n) (coordinateStep i h)
    simpa [Function.comp_def, translationContinuousMap] using
      hpres.quasiMeasurePreserving.ae_eq_comp ha
  have hresult :
      ((differenceQuotientLp ∞ i h a : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume]
      ((coefficientDifferenceLInf i f hf h hh : DerivLp n ∞ Set.univ) :
        ℝ^n → ℝ) := by
    filter_upwards [hdq, hcoeff, ha, hshift] with x hxdq hxcoeff hax hashift
    rw [hxdq, hxcoeff, hax, hashift]
    rfl
  simpa [domainMeasure] using hresult

/-- Lipschitz control of the abstract `L∞` coefficient quotient. -/
theorem norm_differenceQuotientLp_top_le
    (i : Fin n) (a : DerivLp n ∞ Set.univ) (f : ℝ^n → ℝ)
    {C : NNReal} (hf : LipschitzWith C f)
    (ha : (a : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume] f)
    (h : ℝ) (hh : h ≠ 0) :
    ‖differenceQuotientLp ∞ i h a‖ ≤ C := by
  rw [differenceQuotientLp_top_eq_coefficientDifferenceLInf i a f hf ha h hh]
  exact norm_coefficientDifferenceLInf_le i f hf h hh
end SobolevSpace.GraphSpace.DifferenceQuotient
