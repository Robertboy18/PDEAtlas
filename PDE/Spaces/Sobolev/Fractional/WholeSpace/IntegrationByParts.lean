/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.L2Representative
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Integration by parts for fractional Sobolev functions

For `u ∈ H^s` with `s ≥ 1`, both `u` and its directional derivative
`∂_{m} u ∈ H^{s-1}` are represented by `L²` functions
(`SobolevSpace.Fractional.toL2Fun`).  We show that those two `L²`
functions satisfy the classical integration-by-parts identity against Schwartz
test functions:

`∫ (∂_{m} φ) · u = - ∫ φ · (∂_{m} u)`.

That identity is precisely the content of "`∂_{m} u` is the weak derivative of
`u`", so it is the bridge from the Fourier-side fractional scale to the
weak-derivative formulation used by the integer-order graph space
`SobolevSpace.GraphSpace`.

## Proof

The proof is short, with three ingredients: the
distributional derivative pairs as `⟨∂ u, φ⟩ = ⟨u, -∂ φ⟩`
(Mathlib's `lineDerivOp_apply_apply`), an `L²` function pairs by integration
(`Lp.toTemperedDistribution_apply`), and both `u` and `∂_{m} u` are equal to
their `L²` representatives as distributions (`toDistr_eq_toL2Fun`).

## Bridge to the integer scale

The Schwartz identity specializes to Mathlib's
canonical compactly supported smooth test functions
`𝓓((⊤ : Opens (ℝ^n)), ℝ)`. The remaining passage from complex-valued
representatives to real-valued weak derivatives is carried out in
`Fractional.WholeSpace.WeakDerivative`.
-/

@[expose] public section

open TemperedDistribution MeasureTheory
open TopologicalSpace
open scoped BesselPotentialSpace Distributions ENNReal LineDeriv SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

open BesselPotentialSpace

/-- Pairing an `L²` representative against a Schwartz function is integration. -/
theorem toL2Fun_pairing (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) (φ : 𝓢(ℝ^n, ℂ)) :
    (toDistr u) φ = ∫ x, φ x • (toL2Fun hs u : ℝ^n → ℂ) x := by
  rw [toDistr_eq_toL2Fun hs u, MeasureTheory.Lp.toTemperedDistribution_apply]

/-- Integration by parts. For `u ∈ H^s` with `s ≥ 1`, the `L²`
representatives of `u` and of `∂_{m} u` satisfy the weak-derivative identity
against Schwartz test functions. -/
theorem integral_lineDeriv_smul_toL2Fun (hs : (1 : ℝ) ≤ s) (m : ℝ^n)
    (u : H^{s}(ℝ^n)) (φ : 𝓢(ℝ^n, ℂ)) :
    ∫ x, φ x • (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
        (lineDerivLinear n s m u) : ℝ^n → ℂ) x
      = - ∫ x, (∂_{m} φ) x
          • (toL2Fun (by linarith : (0 : ℝ) ≤ s) u : ℝ^n → ℂ) x := by
  have h0 : (0 : ℝ) ≤ s := by linarith
  have h1 : (0 : ℝ) ≤ s - 1 := by linarith
  -- Pair the derivative against `φ` and unfold the distributional derivative.
  have hpair := toL2Fun_pairing h1 (lineDerivLinear n s m u) φ
  rw [toDistr_lineDerivLinear, lineDerivOp_apply_apply] at hpair
  -- The right-hand side is the pairing of `u` against `-∂φ`.
  have hneg : (toDistr u) (-∂_{m} φ) = - ((toDistr u) (∂_{m} φ)) := by
    simp
  rw [hneg, toL2Fun_pairing h0 u (∂_{m} φ)] at hpair
  exact hpair.symm

/-- The same identity written as the sign-normalised weak-derivative statement
`∫ (∂φ) · u = (-1) ∫ φ · (∂u)`, matching the shape of
`SobolevSpace.HasWeakDerivativeOn` at order one. -/
theorem integral_smul_toL2Fun_lineDeriv (hs : (1 : ℝ) ≤ s) (m : ℝ^n)
    (u : H^{s}(ℝ^n)) (φ : 𝓢(ℝ^n, ℂ)) :
    ∫ x, (∂_{m} φ) x • (toL2Fun (by linarith : (0 : ℝ) ≤ s) u : ℝ^n → ℂ) x
      = (-1 : ℂ) * ∫ x, φ x • (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
          (lineDerivLinear n s m u) : ℝ^n → ℂ) x := by
  rw [integral_lineDeriv_smul_toL2Fun hs m u φ]
  ring

/-! ## Against compactly supported smooth test functions

`SobolevSpace.HasWeakDerivativeOn` quantifies over
`𝓓((⊤ : Opens (ℝ^n)), ℝ)`. Every such real-valued test function complexifies to a
Schwartz function (`testFunctionToSchwartz`), so the Schwartz identity
`integral_lineDeriv_smul_toL2Fun` applies to it. -/

/-- A real compactly supported smooth test function, complexified into a Schwartz function. -/
noncomputable def testFunctionToSchwartz
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    𝓢(ℝ^n, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (φ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) (by simp))
    (Complex.ofRealCLM.contDiff.comp φ.contDiff)

/-- The Schwartz embedding of a real test function is its pointwise complexification. -/
@[simp] theorem testFunctionToSchwartz_apply
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (x : ℝ^n) : testFunctionToSchwartz φ x = ((φ x : ℝ) : ℂ) := rfl

/-- Integration by parts against a compactly supported smooth real test function. -/
theorem integral_lineDeriv_smul_toL2Fun_testFunction (hs : (1 : ℝ) ≤ s) (m : ℝ^n)
    (u : H^{s}(ℝ^n)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∫ x, ((φ x : ℝ) : ℂ) • (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
        (lineDerivLinear n s m u) : ℝ^n → ℂ) x
      = - ∫ x, (∂_{m} (testFunctionToSchwartz φ)) x
          • (toL2Fun (by linarith : (0 : ℝ) ≤ s) u : ℝ^n → ℂ) x := by
  simpa using integral_lineDeriv_smul_toL2Fun hs m u (testFunctionToSchwartz φ)

/-! ## Matching `partialDeriv`

`HasWeakDerivativeOn` is phrased with `iteratedPartialDeriv`, built from
`partialDeriv i f x = fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))`.  Mathlib's line
derivative on Schwartz functions is the same object, and complexification
commutes with it. -/

/-- Mathlib's line derivative on a Schwartz function is the Fréchet derivative in
that direction. -/
theorem lineDerivOp_schwartz_apply (φ : 𝓢(ℝ^n, ℂ)) (m x : ℝ^n) :
    (∂_{m} φ) x = fderiv ℝ φ x m := rfl

/-- Complexification commutes with differentiation: the line derivative of a
complexified test function is the complexified `partialDeriv`. -/
theorem lineDerivOp_testFunctionToSchwartz
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (i : Fin n) (x : ℝ^n) :
    (∂_{EuclideanSpace.single i (1 : ℝ)} (testFunctionToSchwartz φ)) x
      = (((∂[i] (φ : ℝ^n → ℝ)) x : ℝ) : ℂ) := by
  have hdiff : DifferentiableAt ℝ (fun y : ℝ^n ↦ (φ y : ℝ)) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hcomp : fderiv ℝ (fun y : ℝ^n ↦ ((φ y : ℝ) : ℂ)) x
      = Complex.ofRealCLM.comp (fderiv ℝ (fun y : ℝ^n ↦ (φ y : ℝ)) x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (testFunctionToSchwartz φ) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [show ((testFunctionToSchwartz φ : ℝ^n → ℂ)) = fun y ↦ ((φ y : ℝ) : ℂ) from rfl,
    hcomp]
  rfl

/-- The weak-derivative identity in the shape `HasWeakDerivativeOn` expects.

For `u ∈ H^s` with `s ≥ 1`, the `L²` representatives of `u` and of its `i`-th
derivative satisfy `∫ (∂ᵢφ) · u = - ∫ φ · (∂ᵢ u)` for every compactly supported
smooth real test function `φ`, with `∂ᵢ` given by `partialDeriv`.

Only the passage from complex to real scalars separates this from
`SobolevSpace.HasWeakDerivativeOn Set.univ [i]`. -/
theorem integral_partialDeriv_smul_toL2Fun (hs : (1 : ℝ) ≤ s) (i : Fin n)
    (u : H^{s}(ℝ^n)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∫ x, (((∂[i] (φ : ℝ^n → ℝ)) x : ℝ) : ℂ)
        • (toL2Fun (by linarith : (0 : ℝ) ≤ s) u : ℝ^n → ℂ) x
      = - ∫ x, ((φ x : ℝ) : ℂ) • (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
          (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u) : ℝ^n → ℂ) x := by
  have h := integral_lineDeriv_smul_toL2Fun_testFunction hs (EuclideanSpace.single i (1 : ℝ)) u φ
  simp only [lineDerivOp_testFunctionToSchwartz] at h
  rw [h]
  ring

end SobolevSpace.Fractional
