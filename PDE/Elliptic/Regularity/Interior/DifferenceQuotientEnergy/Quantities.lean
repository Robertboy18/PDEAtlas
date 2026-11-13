/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized

/-!
# Quantities in the interior difference-quotient estimate

The zero extension of an `H¹₀` state has an `L²` gradient on the whole space.
Its coordinate difference quotients enter the localized elliptic energy.
The cutoff and coefficient remainders below are the lower-order terms in
Young's inequality; their definitions do not assert any elliptic estimate.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The whole-space gradient of a zero-extended zero-trace state. -/
def zeroExtendedGradient (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) :
    Fin n → DerivLp n 2 univ :=
  fun i ↦ ((ZeroTrace.zeroExtendH10 hΩ u : WkpAmbientOn n 1 2 univ)
    (singleDerivIndex n i))

/-- The base-coordinate difference quotient of the zero extension. -/
def zeroExtendedBaseQuotient (hΩ : MeasurableSet Ω)
    (k : Fin n) (h : ℝ) (u : H¹₀(Ω)) : DerivLp n 2 univ :=
  differenceQuotientLp 2 k h
    ((ZeroTrace.zeroExtendH10 hΩ u : WkpAmbientOn n 1 2 univ) (baseIndex n 1))

/-- Coordinate difference quotients of the zero-extended gradient. -/
def zeroExtendedGradientQuotient (hΩ : MeasurableSet Ω)
    (k : Fin n) (h : ℝ) (u : H¹₀(Ω)) : Fin n → DerivLp n 2 univ :=
  fun i ↦ differenceQuotientLp 2 k h (zeroExtendedGradient hΩ u i)

/-- The squared `L²` norm of a gradient quotient localized by the cutoff. -/
def localizedDifferenceEnergy (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (v : Fin n → DerivLp n 2 univ) : ℝ :=
  ∑ i, ‖testFunctionLpTop (n := n) (Ω := univ) η • v i‖ ^ 2

/-- The coercive weight left after absorbing the source contribution. -/
def localizedDifferenceWeight (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (alpha gamma : ℝ) : ℝ :=
  (alpha - gamma * ‖testFunctionLpTop (n := n) (Ω := univ) η‖ ^ 2) / 2

/-- Young's remainder for differentiating the cutoff in the principal form. -/
def localizedDifferenceCutoffRemainder
    (A : Fin n → Fin n → DerivLp n ∞ univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : ℝ) (q0 : DerivLp n 2 univ) : ℝ :=
  ∑ j, (∑ i, 2 * ‖A i j‖ *
    ‖partialTestFunctionLpTop (n := n) (Ω := univ) η i‖ * ‖q0‖) ^ 2 / alpha

/-- Young's remainder for the Lipschitz coefficient commutator. -/
def localizedDifferenceCoefficientRemainder
    (C : Fin n → Fin n → NNReal) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (alpha : ℝ) (d0u : Fin n → DerivLp n 2 univ) : ℝ :=
  ∑ i, (∑ j, (C i j : ℝ) *
    ‖testFunctionLpTop (n := n) (Ω := univ) η • d0u j‖) ^ 2 / alpha

/-- The mixed remainder from differentiating both coefficient and cutoff. -/
def localizedDifferenceMixedRemainder
    (C : Fin n → Fin n → NNReal) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (d0u : Fin n → DerivLp n 2 univ) (q0 : DerivLp n 2 univ) : ℝ :=
  ∑ i, ∑ j, 2 * (C i j : ℝ) *
    ‖testFunctionLpTop (n := n) (Ω := univ) η • d0u j‖ *
    ‖partialTestFunctionLpTop (n := n) (Ω := univ) η i‖ * ‖q0‖

/-- The source bound before absorption of its highest-order part. -/
def localizedDifferenceSourceRemainder
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (fnorm gamma : ℝ)
    (q0 : DerivLp n 2 univ) (v : Fin n → DerivLp n 2 univ) : ℝ :=
  let q := testFunctionLpTop (n := n) (Ω := univ) η
  fnorm ^ 2 / gamma + (gamma / 4) *
    ((‖q‖ * ‖q • q0‖) ^ 2 +
      ∑ i, (2 * (‖q‖ * ‖q • v i‖) ^ 2 +
        2 * (2 * ‖q‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := univ) η i‖ * ‖q0‖) ^ 2))

/-- The lower-order part of the localized test norm in the source bound. -/
def localizedDifferenceSourceLower (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q0 : DerivLp n 2 univ) : ℝ :=
  let q := testFunctionLpTop (n := n) (Ω := univ) η
  (‖q‖ * ‖q • q0‖) ^ 2 + ∑ i, 2 *
    (2 * ‖q‖ * ‖partialTestFunctionLpTop (n := n) (Ω := univ) η i‖ * ‖q0‖) ^ 2

/-- The principal form of a gradient quotient with translated coefficients. -/
def localizedDifferencePrincipalEnergy
    (A : Fin n → Fin n → DerivLp n ∞ univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (k : Fin n) (h : ℝ)
    (v : Fin n → DerivLp n 2 univ) : ℝ :=
  ∑ i, ∑ j,
    inner ℝ (Rellich.translateLp ∞ (coordinateStep k h) (A i j) • v j)
      (testFunctionLpTop (n := n) (Ω := univ) (squaredCutoff η) • v i)

/-- The error in the principal form caused by differentiating the cutoff. -/
def localizedDifferenceCutoffError
    (A : Fin n → Fin n → DerivLp n ∞ univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (k : Fin n) (h : ℝ)
    (v : Fin n → DerivLp n 2 univ) (q0 : DerivLp n 2 univ) : ℝ :=
  ∑ i, ∑ j,
    inner ℝ (Rellich.translateLp ∞ (coordinateStep k h) (A i j) • v j)
      (partialTestFunctionLpTop (n := n) (Ω := univ) (squaredCutoff η) i • q0)

/-- The coefficient commutator paired with the localized gradient quotient. -/
def localizedDifferenceCoefficientError
    (A : Fin n → Fin n → DerivLp n ∞ univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (k : Fin n) (h : ℝ)
    (d0u v : Fin n → DerivLp n 2 univ) : ℝ :=
  ∑ i, ∑ j, inner ℝ (differenceQuotientLp ∞ k h (A i j) • d0u j)
    (testFunctionLpTop (n := n) (Ω := univ) (squaredCutoff η) • v i)

/-- The coefficient commutator paired with the differentiated cutoff. -/
def localizedDifferenceMixedError
    (A : Fin n → Fin n → DerivLp n ∞ univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (k : Fin n) (h : ℝ)
    (d0u : Fin n → DerivLp n 2 univ) (q0 : DerivLp n 2 univ) : ℝ :=
  ∑ i, ∑ j, inner ℝ (differenceQuotientLp ∞ k h (A i j) • d0u j)
    (partialTestFunctionLpTop (n := n) (Ω := univ) (squaredCutoff η) i • q0)

end SobolevSpace.GraphSpace
