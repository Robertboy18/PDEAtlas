/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.Quantities
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.Coordinates
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalPairing

/-!
# Weak-equation transforms for interior difference quotients

The first step of Evans' interior `H²` argument: take the weak equation
`∫_Ω aᵢⱼ ∂ⱼ u ∂ᵢ v = ∫_Ω f v` for `u ∈ H¹₀(Ω)`, insert the admissible test
`v = -Dₖ⁻ʰ(η² Dₖʰ u)`, and move the backward quotient onto the flux by the
discrete integration-by-parts identity `⟪q, -Dₖ⁻ʰ w⟫ = ⟪Dₖʰ(E₀ q), w⟫`. Since
`E₀` extends by zero, no boundary term appears, and the equation becomes a
whole-space pairing of forward quotients of the fluxes with the localized
forward field `η² Dₖʰ u`.

## Main results

* `weakDivergence_equation_backwardLocalizedDifferenceH10`,
  `weakDivergence_equation_backwardQuotients`: the abstract operator-valued
  weak equation on the signed test, with the derivatives expanded.
* `weakDivergence_multiplication_backwardLocalizedDifferenceH10`: the
  specialization to multiplication coefficients `aᵢⱼ ∈ L∞` and `L²` forcing.
* `weakDivergence_multiplication_forwardQuotients`: the transformed equation
  in which every pairing involves a forward quotient of a zero-extended flux.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, steps 3-4 (the test function
  (11) and summation by parts (16)).
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

/-- The abstract operator-valued weak equation tested against Evans' signed
localized backward quotient. -/
theorem weakDivergence_equation_backwardLocalizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (ell : StrongDual ℝ (H¹₀(Ω)))
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω) A) ell u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    let v := backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (A i j (derivCoordCLM (n := n) (Ω := Ω) j u))
        (derivCoordCLM (n := n) (Ω := Ω) i v)) = ell v := by
  dsimp only
  let v :=
    backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift
  calc
    _ = variableCoeffForm (n := n) (Ω := Ω) A u v :=
      (variableCoeffForm_apply
        (n := n) (Ω := Ω) A u v).symm
    _ = ell v := hu v

/-- The same weak equation with every derivative of the signed test expanded
as a restricted backward `L²` quotient. -/
theorem weakDivergence_equation_backwardQuotients
    (hΩopen : IsOpen Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (ell : StrongDual ℝ (H¹₀(Ω)))
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω) A) ell u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    let w := localizedDifferenceH10 hΩopen η hηΩ k h u
    let v := backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (A i j (derivCoordCLM (n := n) (Ω := Ω) j u))
        (-restrictDerivLp (n := n) (p := 2)
          (subset_univ Ω)
          (differenceQuotientLp 2 k (-h)
            (zeroExtendedGradient hΩopen.measurableSet w i)))) =
      ell v := by
  dsimp only [zeroExtendedGradient]
  simpa only [derivCoord_backwardLocalizedDifferenceH10] using
    weakDivergence_equation_backwardLocalizedDifferenceH10 hΩopen A ell u hu
      η hηΩ k h hδ hshift

/-- Multiplication-coefficient specialization with an `L²` source.  This is
the exact Hilbert-space form of
`∫ aᵢⱼ ∂ⱼu ∂ᵢ[-Dₖ⁻ʰ(η²Dₖʰu)] = ∫ f[-Dₖ⁻ʰ(η²Dₖʰu)]`. -/
theorem weakDivergence_multiplication_backwardLocalizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    let v := backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
          (derivCoordCLM (n := n) (Ω := Ω) j u))
        (derivCoordCLM (n := n) (Ω := Ω) i v)) =
      inner ℝ f
        (baseCoordCLM (n := n) (Ω := Ω) v) := by
  dsimp only
  let v :=
    backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift
  calc
    _ = variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator
            (n := n) (Ω := Ω) a) u v :=
      (variableCoeffForm_apply
        (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u v).symm
    _ = loadFunctional (n := n) (Ω := Ω) f v :=
      hu v
    _ = inner ℝ f
          (baseCoordCLM (n := n) (Ω := Ω) v) :=
      loadFunctional_apply
        (n := n) (Ω := Ω) f v

/-- Evans' weak equation after discrete integration by parts.  The principal-part
pairings against the signed backward test become whole-space pairings of forward
quotients of the zero-extended flux with the zero-extended gradient of the
localized forward field, while the load pairing stays on `Ω`.  This is the
starting identity for separating the elliptic principal term from coefficient
commutators. -/
theorem weakDivergence_multiplication_forwardQuotients
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    let w := localizedDifferenceH10 hΩopen η hηΩ k h u
    let v := backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (differenceQuotientLp 2 k h
          (Extension.Lp.zeroExtendLp
            (n := n) (p := 2) (Ω := Ω) hΩopen.measurableSet
            (multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
              (derivCoordCLM (n := n) (Ω := Ω) j u))))
        (zeroExtendedGradient hΩopen.measurableSet w i)) =
      inner ℝ f
        (baseCoordCLM (n := n) (Ω := Ω) v) := by
  dsimp only [zeroExtendedGradient]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (differenceQuotientLp 2 k h
          (Extension.Lp.zeroExtendLp
            (n := n) (p := 2) (Ω := Ω) hΩopen.measurableSet
            (multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
              (derivCoordCLM (n := n) (Ω := Ω) j u))))
        ((((ZeroTrace.zeroExtendH10
          (n := n) (Ω := Ω) hΩopen.measurableSet
          (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
            WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)))) =
        ∑ i : Fin n, ∑ j : Fin n,
          inner ℝ
            (multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
              (derivCoordCLM (n := n) (Ω := Ω) j u))
            (-restrictDerivLp (n := n) (p := 2)
              (subset_univ Ω)
              (differenceQuotientLp 2 k (-h)
                ((((ZeroTrace.zeroExtendH10
                  (n := n) (Ω := Ω) hΩopen.measurableSet
                  (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
                    WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      let wi : DerivLp n 2 Set.univ :=
        (((ZeroTrace.zeroExtendH10
          (n := n) (Ω := Ω) hΩopen.measurableSet
          (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
            WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))
      exact (inner_neg_restrict_backwardDifference_eq
        hΩopen.measurableSet k hh
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
          (derivCoordCLM (n := n) (Ω := Ω) j u))
        wi).symm
    _ = inner ℝ f
        (baseCoordCLM (n := n) (Ω := Ω)
          (backwardLocalizedDifferenceH10
            hΩopen η hηΩ k h u hδ hshift)) := by
      simpa [loadFunctional_apply, zeroExtendedGradient] using
        (weakDivergence_equation_backwardQuotients hΩopen
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
          (loadFunctional (n := n) (Ω := Ω) f)
          u hu η hηΩ k h hδ hshift)

end SobolevSpace.GraphSpace
