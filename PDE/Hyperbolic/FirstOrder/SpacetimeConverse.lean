/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeTestRegularity
public import PDE.Hyperbolic.FirstOrder.MovingTestLimits
import PDE.Hyperbolic.FirstOrder.MollifiedMovingTests

/-!
# From separated weak tests to all smooth spacetime tests

The TimeTest × H¹ identity determines the identity for every smooth compactly supported
spacetime test whose support lies strictly before the terminal time. The test's
H¹ slice is continuous, and its time derivative differentiates the base L² curve.
Pairing the constructed mollified representative with this curve gives an identity at
each positive scale. Uniform H¹ contraction and dominated convergence remove that scale.

The state and forcing need only belong to Bochner L². Their chosen representatives are
replaced by L² classes during regularization and returned by almost-everywhere equality.
The prescribed initial datum is the limit of its mollified pairing.

Spatial integrals here use the Sobolev-row L² pairings. Product-measure integrals are
in `SpacetimeProductFormulation`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace NNReal Topology Distributions

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- The separated weak identity implies the full smooth spacetime-test identity,
including the prescribed initial boundary term. The coefficient base rows are continuous
on the interval, and only the displayed spatial derivative bounds are used. -/
theorem isSpacetimeTransportWeakSolution_of_timeTest (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u f : ℝ → H} (hu : MemLp u 2 ν) (hf : MemLp f 2 ν) (x : H)
    (hweak : ∀ (ψ : V) (τ : TimeTest a b), -(∫ t, inner ℝ (u t) (transportBaseCLM ψ) *
      τ.derivFun t ∂ν) = (∫ t, transportTestFunctional (A t) ψ (u t) * τ.toFun t ∂ν) +
      (∫ t, inner ℝ (f t) (transportBaseCLM ψ) * τ.toFun t ∂ν) + inner ℝ x (transportBaseCLM ψ) *
      τ.toFun a) :
    IsSpacetimeTransportWeakSolution A u f x a b := by
  let U : Lp H 2 ν := hu.toLp u
  let F : Lp H 2 ν := hf.toLp f
  have hUu (G : ℝ → H → ℝ) : ∫ t, G t (U t) ∂ν = ∫ t, G t (u t) ∂ν :=
    integral_congr_ae (hu.coeFn_toLp.mono fun t ht ↦ congrArg (G t) ht)
  have hFf (G : ℝ → H → ℝ) : ∫ t, G t (F t) ∂ν = ∫ t, G t (f t) ∂ν :=
    integral_congr_ae (hf.coeFn_toLp.mono fun t ht ↦ congrArg (G t) ht)
  have hweakLp (ψ : V) (τ : TimeTest a b) :
      -(∫ t, inner ℝ (U t) (transportBaseCLM ψ) * τ.derivFun t ∂ν) =
        (∫ t, transportTestFunctional (A t) ψ (U t) * τ.toFun t ∂ν) +
        (∫ t, inner ℝ (F t) (transportBaseCLM ψ) * τ.toFun t ∂ν) +
        inner ℝ x (transportBaseCLM ψ) * τ.toFun a := by
    rw [hUu fun t v ↦ inner ℝ v (transportBaseCLM ψ) * τ.derivFun t,
      hUu fun t v ↦ transportTestFunctional (A t) ψ v * τ.toFun t,
      hFf fun t v ↦ inner ℝ v (transportBaseCLM ψ) * τ.toFun t]
    exact hweak ψ τ
  intro Φ hΦ
  let φ : ℝ → V := spacetimeTestH1Slice Φ
  let dφ : ℝ → V := spacetimeTestH1Slice (fun p ↦ TestFunction.lineDerivCLM ℝ (1, 0) (Φ p))
  let B : V →L[ℝ] H := transportBaseCLM
  have hφ : ContinuousOn φ (Icc a b) := (continuous_spacetimeTestH1Slice Φ).continuousOn
  have hdφ : ContinuousOn dφ (Icc a b) := (continuous_spacetimeTestH1Slice
      (fun p ↦ TestFunction.lineDerivCLM ℝ (1, 0) (Φ p))).continuousOn
  have hderiv (t : ℝ) (_ht : t ∈ Icc a b) : HasDerivAt (fun s ↦ B (φ s)) (B (dφ t)) t :=
    hasDerivAt_transportBase_spacetimeTestH1Slice Φ t
  have hterminal : B (φ b) = 0 :=
    (congrArg B (spacetimeTestH1Slice_eq_zero_of_support_before Φ b hΦ)).trans B.map_zero
  let ε : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let S (k : ℕ) : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) (hε k)
  have hmoll (k : ℕ) : -(∫ t, inner ℝ (U t) (B (S k (B (dφ t)))) ∂ν) =
        (∫ t, transportTestFunctional (A t) (S k (B (φ t))) (U t) ∂ν) +
        (∫ t, inner ℝ (F t) (B (S k (B (φ t)))) ∂ν) + inner ℝ x (B (S k (B (φ a)))) :=
    integral_mollified_moving_test_of_weak_equation (hε k) A hA hab L hL U F x
      hweakLp (fun t ↦ B (φ t)) (fun t ↦ B (dφ t))
      (B.continuous.comp_continuousOn hdφ) hderiv hterminal
  have htime := tendsto_integral_inner_mollified_test
    (standardMollifier n) ε hε hε0 (Lp.memLp U) dφ hdφ
  have htransport := tendsto_integral_transport_mollified_test
    ε hε hε0 hab.le A hA L hL (Lp.memLp U) φ hφ
  have hforcing := tendsto_integral_inner_mollified_test
    (standardMollifier n) ε hε hε0 (Lp.memLp F) φ hφ
  have hinitial : Tendsto (fun k ↦ inner ℝ x (B (S k (B (φ a))))) atTop (𝓝 (inner ℝ x (B (φ a)))) :=
    tendsto_const_nhds.inner (B.continuous.continuousAt.tendsto.comp
      (tendsto_mollifierProductH1CLM_base (standardMollifier n) ε hε hε0 (φ a)))
  have hid : -(∫ t, inner ℝ (U t) (B (dφ t)) ∂ν) =
      (∫ t, transportTestFunctional (A t) (φ t) (U t) ∂ν) +
      (∫ t, inner ℝ (F t) (B (φ t)) ∂ν) + inner ℝ x (B (φ a)) :=
    tendsto_nhds_unique htime.neg (((htransport.add hforcing).add hinitial).congr'
      (Eventually.of_forall fun k ↦ (hmoll k).symm))
  rwa [hUu fun t v ↦ inner ℝ v (B (dφ t)), hUu fun t v ↦ transportTestFunctional (A t) (φ t) v,
    hFf fun t v ↦ inner ℝ v (B (φ t))] at hid

end PDE.Hyperbolic.FirstOrder
