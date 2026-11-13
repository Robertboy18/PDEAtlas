/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.Quantities
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.Coordinates
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.WeakEquation
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.FiniteDifferences

/-!
# Energy identities for interior difference quotients

The algebraic step of Evans' interior `H²` argument. After the weak equation
`∫ aᵢⱼ ∂ⱼ u ∂ᵢ v = ∫ f v` has been tested with `v = -Dₖ⁻ʰ(η² Dₖʰ u)` and
integrated by parts discretely, the discrete Leibniz rule

`Dₖʰ(aᵢⱼ ∂ⱼ u) = (τₕ aᵢⱼ) Dₖʰ ∂ⱼ u + (Dₖʰ aᵢⱼ) ∂ⱼ u`

and the Sobolev product rule `∂ᵢ(η² w) = η² ∂ᵢ w + ∂ᵢ(η²) w` split the
equation into a coercive principal energy and three error terms: the
derivative of the cutoff, the coefficient quotient, and their product. No
estimate is performed here; the identities are exact.

## Main results

* `weakDivergence_restrictedGlobalCoefficients_split`: the Leibniz split of
  every flux quotient for coefficients defined on `ℝ^n` and restricted to `Ω`.
* `weakDivergence_restrictedGlobalCoefficients_expanded`: the fully expanded
  identity, with the coercive field `η² Dₖʰ ∂ᵢ u` and the cutoff error
  `∂ᵢ(η²) Dₖʰ u` displayed separately.
* `weakDivergence_restrictedGlobalCoefficients_energyBalance`: the same
  identity regrouped as principal energy plus the three error terms.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, step 4 (summation by parts
  (16), product rule (17) and the splitting (18)).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Principal/commutator decomposition for globally defined bounded
coefficients.  The weak equation on `Ω` uses their restrictions; after zero
extension and discrete integration by parts, the exact `Lp` Leibniz rule
splits every flux quotient into
`(τₕaᵢⱼ) Dₖʰ(E₀∂ⱼu)` plus `(Dₖʰaᵢⱼ) E₀∂ⱼu`.
This is Evans' algebraic interior-regularity identity before ellipticity and
Young estimates are applied. -/
theorem weakDivergence_restrictedGlobalCoefficients_split
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (Rellich.translateLp ∞ (coordinateStep k h) (A i j) •
            zeroExtendedGradientQuotient hΩopen.measurableSet k h u j +
          differenceQuotientLp ∞ k h (A i j) • zeroExtendedGradient hΩopen.measurableSet u j)
        (zeroExtendedGradient hΩopen.measurableSet
          (localizedDifferenceH10 hΩopen η hηΩ k h u) i)) =
      inner ℝ f (baseCoordCLM (n := n) (Ω := Ω)
        (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift)) := by
  dsimp only [zeroExtendedGradient, zeroExtendedBaseQuotient,
    zeroExtendedGradientQuotient]
  have hd0 (j : Fin n) :
      Extension.Lp.zeroExtendLp hΩopen.measurableSet
          (derivCoordCLM (n := n) (Ω := Ω) j u) =
        ((ZeroTrace.zeroExtendH10 hΩopen.measurableSet u : WkpAmbientOn n 1 2 Set.univ)
          (singleDerivIndex n j)) := rfl
  simpa only [multiplicationCoefficientOperator_apply,
    Extension.Lp.zeroExtendLp_restrict_lpSMul,
    differenceQuotientL2_lpSMul, hd0, zeroExtendedGradient] using
    (weakDivergence_multiplication_forwardQuotients hΩopen
      (fun i j ↦ restrictDerivLp
        (n := n) (p := ∞) (subset_univ Ω) (A i j))
      f u hu η hηΩ k hh hδ hshift)

/-- Evans' interior identity with the localized derivative fully expanded.
The first summand in the second inner-product argument is the coercive
`η² DₖʰDᵢu` field.  The second is the cutoff error
`Dᵢ(η²) Dₖʰu`; the coefficient quotient in the first argument is the
remaining commutator.  Thus every term that must later be estimated is
present explicitly, with no boundary term hidden in notation.

This is the algebraic identity in Evans, 2nd ed., §6.3.1, obtained after
testing the weak equation with `-Dₖ⁻ʰ(η² Dₖʰu)` and applying the discrete
product rule. -/
theorem weakDivergence_restrictedGlobalCoefficients_expanded
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (Rellich.translateLp ∞ (coordinateStep k h) (A i j) •
            zeroExtendedGradientQuotient hΩopen.measurableSet k h u j +
          differenceQuotientLp ∞ k h (A i j) • zeroExtendedGradient hΩopen.measurableSet u j)
        (testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) •
            zeroExtendedGradientQuotient hΩopen.measurableSet k h u i +
          partialTestFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) i •
            zeroExtendedBaseQuotient hΩopen.measurableSet k h u)) =
      inner ℝ f (baseCoordCLM (n := n) (Ω := Ω)
        (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift)) := by
  dsimp only [zeroExtendedGradient, zeroExtendedBaseQuotient,
    zeroExtendedGradientQuotient]
  have hsplit := weakDivergence_restrictedGlobalCoefficients_split
    hΩopen A f u hu η hηΩ k hh hδ hshift
  dsimp only [zeroExtendedGradient, zeroExtendedBaseQuotient,
    zeroExtendedGradientQuotient] at hsplit
  have hz (i : Fin n) := zeroExtendedDeriv_localizedDifferenceH10
    hΩopen η hηΩ k h u i
  dsimp only at hz
  simp_rw [hz] at hsplit
  exact hsplit

/-- The expanded weak equation regrouped into its coercive principal energy
and the three error terms: derivative of the cutoff, coefficient
difference quotient, and their mixed product. -/
theorem weakDivergence_restrictedGlobalCoefficients_energyBalance
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    localizedDifferencePrincipalEnergy A η k h
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) +
      (localizedDifferenceCutoffError A η k h
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u)
        (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) +
      localizedDifferenceCoefficientError A η k h
        (zeroExtendedGradient hΩopen.measurableSet u)
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) +
      localizedDifferenceMixedError A η k h
        (zeroExtendedGradient hΩopen.measurableSet u)
        (zeroExtendedBaseQuotient hΩopen.measurableSet k h u)) =
      inner ℝ f (baseCoordCLM (n := n) (Ω := Ω)
        (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift)) := by
  dsimp only [zeroExtendedGradient, zeroExtendedBaseQuotient,
    zeroExtendedGradientQuotient, localizedDifferencePrincipalEnergy,
    localizedDifferenceCutoffError, localizedDifferenceCoefficientError,
    localizedDifferenceMixedError]
  have hexpanded := weakDivergence_restrictedGlobalCoefficients_expanded
    hΩopen A f u hu η hηΩ k hh hδ hshift
  dsimp only [zeroExtendedGradient, zeroExtendedBaseQuotient,
    zeroExtendedGradientQuotient] at hexpanded
  simp only [inner_add_left, inner_add_right, Finset.sum_add_distrib] at hexpanded
  linear_combination hexpanded

end SobolevSpace.GraphSpace
