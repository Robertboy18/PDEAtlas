/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Completeness of Sobolev graph spaces

The graph-space model `WkpSpaceOn n k p Ω` is the subspace of the finite product
`WkpAmbientOn n k p Ω = PiLp p (fun _ : DerivIndex n k => Lp ℝ p μΩ)` cut out by the
weak-derivative identities

`∫ U₀ · ∂^α φ = (-1)^|α| ∫ U_α · φ` for all `|α| ≤ k` and all test functions `φ` supported in `Ω`.

This constraint set is closed in the ambient product, so `WkpSpaceOn n k p Ω` is complete for every
`1 ≤ p ≤ ∞` and every subset `Ω` of `ℝ^n`; no regularity of `Ω` is used. For open `Ω` this is the
classical statement that `W^{k,p}(Ω)` is a Banach space (Evans §5.2.3, Theorem 2).

## Main results

* `isClosed_WkpSubmoduleOn`: the weak-derivative graph submodule is closed in the ambient bundle.
* `completeSpace_WkpSpaceOn`: `WkpSpaceOn n k p Ω` is complete.

## How it works

We write each identity as the vanishing of a continuous linear functional on the ambient product:
`φ` and `∂^α φ` are continuous with compact support, hence lie in `L^{p'}(Ω)` for the Hölder
conjugate `p'`, and pairing an `Lᵖ` coordinate against them is continuous by Mathlib's
`ContinuousLinearMap.lpPairing`. The constraint set is then an intersection of closed hyperplanes,
hence closed (`isClosed_WkpSubmoduleOn`), and a closed subspace of the complete space
`WkpAmbientOn n k p Ω` is complete. Since the derivatives are part of the data, the step of Evans's
proof that passes to the limit in the defining identity (claim (8)) becomes this closedness.

## Implementation notes

The test functions are placed in `Lp ℝ q μΩ` with `q = ENNReal.conjExponent p`, and the Hölder
conjugacy instance is derived locally so that Mathlib's `lpPairing` applies for every `p ≥ 1`,
including `p = 1` (where `q = ∞`) and `p = ∞` (where `q = 1`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 2, pp. 262-263.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Sobolev

namespace GraphSpace

section CompleteSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μΩ" => domainMeasure n Ω
local notation "q" => ENNReal.conjExponent p

private noncomputable def toLpOfContCompact (r : ℝ≥0∞) (f : ℝ^n → ℝ)
    (hf : Continuous f) (hcs : HasCompactSupport f) : MeasureTheory.Lp ℝ r μΩ :=
  (hf.memLp_of_hasCompactSupport (μ := μΩ) (p := r) hcs).toLp f

private theorem toLpOfContCompact_ae (r : ℝ≥0∞) (f : ℝ^n → ℝ)
    (hf : Continuous f) (hcs : HasCompactSupport f) :
    (toLpOfContCompact (n := n) (Ω := Ω) r f hf hcs : ℝ^n → ℝ) =ᵐ[μΩ] f :=
  (hf.memLp_of_hasCompactSupport (μ := μΩ) (p := r) hcs).coeFn_toLp

private noncomputable def pairingWith (ψ : MeasureTheory.Lp ℝ q μΩ) :
    MeasureTheory.Lp ℝ p μΩ →L[ℝ] ℝ :=
  (ContinuousLinearMap.lpPairing μΩ p q (ContinuousLinearMap.mul ℝ ℝ)).flip ψ

private theorem pairingWith_apply (ψ : MeasureTheory.Lp ℝ q μΩ) (f : MeasureTheory.Lp ℝ p μΩ) :
    pairingWith (n := n) (p := p) (Ω := Ω) ψ f =
      ContinuousLinearMap.lpPairing μΩ p q (ContinuousLinearMap.mul ℝ ℝ) f ψ := by
  simp [pairingWith]

private theorem pairingWith_eq_integral
    (ψ : MeasureTheory.Lp ℝ q μΩ) (f : MeasureTheory.Lp ℝ p μΩ) :
    pairingWith (n := n) (p := p) (Ω := Ω) ψ f = ∫ x, (f x) * (ψ x) ∂ μΩ := by
  -- `lpPairing` is defined by integrating the pointwise bilinear pairing.
  simpa [pairingWith_apply] using
    (ContinuousLinearMap.lpPairing_eq_integral (B := ContinuousLinearMap.mul ℝ ℝ) (f := f) (g := ψ))

private noncomputable def φLp (φΩ : TestFunctionOn n Ω) : MeasureTheory.Lp ℝ q μΩ :=
  toLpOfContCompact (n := n) (Ω := Ω) (r := q) φΩ.1.toFun
    φΩ.1.contDiff.continuous φΩ.1.hasCompactSupport

private noncomputable def dαφLp (a : DerivIndex n k) (φΩ : TestFunctionOn n Ω) :
    MeasureTheory.Lp ℝ q μΩ :=
  toLpOfContCompact (n := n) (Ω := Ω) (r := q)
      (iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun)
      (PDE.contDiff_top_iteratedPartialDeriv (n := n) φΩ.1.contDiff a.toList).continuous
      (iteratedPartialDeriv_hasCompactSupport (n := n) (φ := φΩ.1) (α := a.toList))

private noncomputable def constraintCLM (a : DerivIndex n k) (φΩ : TestFunctionOn n Ω) :
    WkpAmbientOn n k p Ω →L[ℝ] ℝ :=
  let term1 :=
    (pairingWith (n := n) (p := p) (Ω := Ω)
        (dαφLp (n := n) (k := k) (p := p) (Ω := Ω) a φΩ)).comp
      (PiLp.proj (𝕜 := ℝ) (p := p) (β := fun _ : DerivIndex n k ↦ DerivLp n p Ω)
        (baseIndex n k))
  let term2 :=
    (pairingWith (n := n) (p := p) (Ω := Ω)
        (φLp (n := n) (p := p) (Ω := Ω) φΩ)).comp
      (PiLp.proj (𝕜 := ℝ) (p := p)
        (β := fun _ : DerivIndex n k ↦ DerivLp n p Ω) a)
  term1 - ((-1 : ℝ) ^ a.toList.length) • term2

private theorem constraintCLM_apply (a : DerivIndex n k) (φΩ : TestFunctionOn n Ω)
    (U : WkpAmbientOn n k p Ω) :
    constraintCLM (n := n) (k := k) (p := p) (Ω := Ω) a φΩ U =
      (∫ x, (U (baseIndex n k)) x * iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun x ∂ μΩ)
        - ((-1 : ℝ) ^ a.toList.length) *
          (∫ x, (U a) x * φΩ.1.toFun x ∂ μΩ) := by
  classical
  -- Each dual pairing is integration against the corresponding test function.
  have h1 :
      pairingWith (n := n) (p := p) (Ω := Ω) (dαφLp (n := n) (k := k) (p := p) (Ω := Ω) a φΩ)
            (U (baseIndex n k))
        =
      ∫ x, (U (baseIndex n k)) x * iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun x ∂ μΩ := by
    have hψ :
        (dαφLp (n := n) (k := k) (p := p) (Ω := Ω) a φΩ : ℝ^n → ℝ)
          =ᵐ[μΩ] fun x ↦
              iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun x :=
      toLpOfContCompact_ae (n := n) (Ω := Ω)
        (r := q)
        (f := iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun)
        (hf := (PDE.contDiff_top_iteratedPartialDeriv
          (n := n) φΩ.1.contDiff a.toList).continuous)
        (hcs := (iteratedPartialDeriv_hasCompactSupport (n := n) (φ := φΩ.1) (α := a.toList)))
    -- start from the `Lp` integral, then replace `ψ` by the test function a.e.
    calc
      pairingWith (n := n) (p := p) (Ω := Ω) (dαφLp (n := n) (k := k) (p := p) (Ω := Ω) a φΩ)
          (U (baseIndex n k))
          = ∫ x, (U (baseIndex n k)) x *
              (dαφLp (n := n) (k := k) (p := p) (Ω := Ω) a φΩ) x ∂ μΩ :=
                pairingWith_eq_integral (n := n) (p := p) (Ω := Ω)
                  (ψ := dαφLp (n := n) (k := k) (p := p) (Ω := Ω) a φΩ)
                  (f := U (baseIndex n k))
      _ = ∫ x, (U (baseIndex n k)) x *
              iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun x ∂ μΩ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hψ] with x hx
            simp [hx]
  -- `term2`
  have h2 :
      pairingWith (n := n) (p := p) (Ω := Ω) (φLp (n := n) (p := p) (Ω := Ω) φΩ) (U a)
        =
      ∫ x, (U a) x * φΩ.1.toFun x ∂ μΩ := by
    have hψ :
        (φLp (n := n) (p := p) (Ω := Ω) φΩ : ℝ^n → ℝ)
          =ᵐ[μΩ] fun x ↦ φΩ.1.toFun x :=
      toLpOfContCompact_ae (n := n) (Ω := Ω)
        (r := q)
        (f := φΩ.1.toFun)
        (hf := φΩ.1.contDiff.continuous)
        (hcs := φΩ.1.hasCompactSupport)
    calc
      pairingWith (n := n) (p := p) (Ω := Ω) (φLp (n := n) (p := p) (Ω := Ω) φΩ) (U a)
          = ∫ x, (U a) x * (φLp (n := n) (p := p) (Ω := Ω) φΩ) x ∂ μΩ :=
                pairingWith_eq_integral (n := n) (p := p) (Ω := Ω)
                  (ψ := φLp (n := n) (p := p) (Ω := Ω) φΩ) (f := U a)
      _ = ∫ x, (U a) x * φΩ.1.toFun x ∂ μΩ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hψ] with x hx
            simp [hx]
  simp [constraintCLM, h1, h2, smul_eq_mul]

private theorem isWkpOn_iff_forall_constraints (U : WkpAmbientOn n k p Ω) :
    IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω) U
      ↔ ∀ a : DerivIndex n k, ∀ φΩ : TestFunctionOn n Ω,
          constraintCLM (n := n) (k := k) (p := p) (Ω := Ω) a φΩ U = 0 := by
  constructor
  · intro hU a φΩ
    have hEq := hU a φΩ.1 φΩ.2
    have hC := constraintCLM_apply (n := n) (k := k) (p := p) (Ω := Ω) (a := a) (φΩ := φΩ) U
    -- The weak-derivative identity says exactly that this constraint vanishes.
    have : (∫ x, (U (baseIndex n k)) x * iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun x ∂ μΩ)
        - ((-1 : ℝ) ^ a.toList.length) *
          (∫ x, (U a) x * φΩ.1.toFun x ∂ μΩ) = 0 :=
      sub_eq_zero.mpr hEq
    simpa [hC] using this
  · intro hU a
    refine ⟨memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out,
      memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out, ?_⟩
    intro φ hφsupp
    let φΩ : TestFunctionOn n Ω := ⟨φ, hφsupp⟩
    have h0 := hU a φΩ
    have hC := constraintCLM_apply (n := n) (k := k) (p := p) (Ω := Ω) (a := a) (φΩ := φΩ) U
    -- Vanishing of the constraint recovers the distributional derivative identity.
    have :
        (∫ x, (U (baseIndex n k)) x * iteratedPartialDeriv (n := n) a.toList φ.toFun x ∂ μΩ)
          =
        (-1 : ℝ) ^ a.toList.length *
          (∫ x, (U a) x * φ.toFun x ∂ μΩ) := by
      have h0' :
          (∫ x, (U (baseIndex n k)) x * iteratedPartialDeriv (n := n) a.toList φ.toFun x ∂ μΩ)
            - ((-1 : ℝ) ^ a.toList.length) *
              (∫ x, (U a) x * φ.toFun x ∂ μΩ) = 0 := by
        simpa [φΩ, hC] using h0
      exact sub_eq_zero.mp h0'
    simpa [HasWeakDerivativeOn, φΩ] using this

/-- The weak-derivative constraints form a closed subspace of the ambient finite `L^p`
product. -/
theorem isClosed_WkpSubmoduleOn (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Set (ℝ^n)) :
    IsClosed ((wkpSubmoduleOn n k p Ω : Submodule ℝ (WkpAmbientOn n k p Ω)) : Set (WkpAmbientOn n k
      p Ω)) := by
  classical
  -- use the characterization as an intersection of closed sets
  have :
      ((wkpSubmoduleOn n k p Ω : Submodule ℝ (WkpAmbientOn n k p Ω)) : Set (WkpAmbientOn n k p Ω))
        =
        (⋂ a : DerivIndex n k,
          ⋂ φΩ : TestFunctionOn n Ω,
            {U : WkpAmbientOn n k p Ω |
              constraintCLM (n := n) (k := k) (p := p) (Ω := Ω) a φΩ U = 0}) := by
    ext U
    simp [wkpSubmoduleOn, isWkpOn_iff_forall_constraints (n := n) (k := k) (p := p) (Ω := Ω)]
  -- each set `{U | constraintCLM ... U = 0}` is closed
  rw [this]
  refine isClosed_iInter ?_
  intro a
  refine isClosed_iInter ?_
  intro φΩ
  have hcont :
      Continuous fun U : WkpAmbientOn n k p Ω ↦
      constraintCLM (n := n) (k := k) (p := p) (Ω := Ω) a φΩ U :=
    (constraintCLM (n := n) (k := k) (p := p) (Ω := Ω) a φΩ).continuous
  simpa using isClosed_eq hcont continuous_const

/-- The Sobolev graph space `W^{k,p}(Ω)` is complete for every `p ≥ 1` and every `Ω ⊆ ℝ^n`. For
open `Ω`, this is the completeness part of Evans §5.2.3, Theorem 2. -/
instance completeSpace_WkpSpaceOn (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Set (ℝ^n)) :
    CompleteSpace (W^{k,p}(Ω)) := by
  -- a closed subspace of a complete space is complete
  have hclosed := isClosed_WkpSubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω)
  exact hclosed.completeSpace_coe

end CompleteSpace

end GraphSpace

end SobolevSpace
