/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeWeakFormulation
public import PDE.Hyperbolic.FirstOrder.L2Uniqueness
import PDE.Hyperbolic.FirstOrder.SpacetimeConverse

/-!
# Uniqueness from smooth spacetime tests

Passing from smooth spacetime tests to H¹ and endpoint time tests puts the problem
in the Bochner L² uniqueness theorem. Equality is in the Bochner L² space, not at every point of
arbitrary representatives.

`exists_symmetric_spacetime_cauchy_l2_unique` combines the L² Cauchy construction with both
formulation directions. It keeps the continuous representative, its initial value, and the
energy bound, and its class is unique among Bochner L² solutions of all smooth spacetime tests.
Both theorems assume symmetric coefficient matrices and uniform bounds on
`coefficientDerivativeBound` and `coefficientGradientBound`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "ν" => volume.restrict (Ioc a b)

/-- Two Bochner L² solutions with the same forcing and prescribed initial boundary term
agree if they satisfy the equation against all smooth compactly supported spacetime
tests before the terminal time. The symmetric W¹,∞ coefficients have continuous base
rows on Icc and uniform spatial derivative bounds, as in the uniqueness theorem. -/
theorem eq_of_symmetric_spacetime_weak_equations
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (u v f : Lp H 2 ν) (x : H)
    (hu : IsSpacetimeTransportWeakSolution A u f x a b)
    (hv : IsSpacetimeTransportWeakSolution A v f x a b) :
    u = v := by
  classical
  let CN : ℝ≥0 := ⟨C, hC⟩
  have hentry (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ CN :=
    (coefficientDerivativeBound_entry_le (A t) j p q).trans (hdiv t ht)
  exact eq_of_symmetric_transport_weak_equations A hA hab hsym hC hL hdiv hgrad u v f x
    (fun φ τ ↦ IsSpacetimeTransportWeakSolution.timeTest hab A hA CN hentry
      (Lp.memLp u) (Lp.memLp f) hu φ τ)
    (fun φ τ ↦ IsSpacetimeTransportWeakSolution.timeTest hab A hA CN hentry
      (Lp.memLp v) (Lp.memLp f) hv φ τ)

/-- The L² Cauchy construction satisfies every smooth compactly supported spacetime
transport test before the terminal time, with the prescribed initial boundary term.
Its continuous representative has the initial value and energy bound below. Every Bochner
L² solution satisfying these full spacetime identities represents the same class.

The coefficient assumptions are those of the Cauchy construction: symmetric W¹,∞ rows,
continuous base rows on Icc, and uniform spatial derivative bounds. -/
theorem exists_symmetric_spacetime_cauchy_l2_unique
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (x : H) (f : Lp H 2 ν) :
    ∃ (u : ℝ → H) (hu : MemLp u 2 ν),
      ContinuousOn u (Icc a b) ∧
      u a = x ∧
      (∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
        (‖x‖ ^ 2 + ‖f‖ ^ 2) * Real.exp ((C + 1) * (t - a))) ∧
      (∀ (φ : PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))) (τ : TimeTest a b),
        Integrable (fun t ↦ transportTestFunctional (A t) φ (u t) * τ.toFun t) ν ∧
        -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
          (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
            (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) +
              ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a) ∧
      IsSpacetimeTransportWeakSolution A u f x a b ∧
      ∀ v : Lp H 2 ν,
        IsSpacetimeTransportWeakSolution A v f x a b → v = hu.toLp u := by
  classical
  obtain ⟨u, hu, hucont, hux, huenergy, huweak, huunique⟩ :=
    exists_symmetric_cauchy_l2_unique A hA hab hsym hC hL hdiv hgrad x f
  let CN : ℝ≥0 := ⟨C, hC⟩
  have hentry (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ CN :=
    (coefficientDerivativeBound_entry_le (A t) j p q).trans (hdiv t ht)
  have hfull : IsSpacetimeTransportWeakSolution A u f x a b :=
    isSpacetimeTransportWeakSolution_of_timeTest hab A hA CN hentry
      hu (Lp.memLp f) x (fun φ τ ↦ (huweak φ τ).2)
  refine ⟨u, hu, hucont, hux, huenergy, huweak, hfull, fun v hv ↦ ?_⟩
  exact huunique v (fun φ τ ↦ IsSpacetimeTransportWeakSolution.timeTest
    hab A hA CN hentry (Lp.memLp v) (Lp.memLp f) hv φ τ)

end PDE.Hyperbolic.FirstOrder
