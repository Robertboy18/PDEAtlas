/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
public import PDE.Spaces.Sobolev.Foundations.VectorValued.WeakDerivatives

/-!
# Closedness of Banach-valued spatial weak derivatives in `L^p`

For a fixed real test, its pairing with a Banach-valued function is a continuous linear
map on `Lp`, supplied by Mathlib's Bochner-valued Hölder pairing. Both sides of the
weak-derivative identity therefore pass to `L^p` limits.

The result applies to every `1 ≤ p ≤ ∞` on any open Euclidean domain, without a finite-volume
or finite-dimensional-codomain hypothesis. The proof uses no extension operator,
approximation theorem, or completeness of the Sobolev space.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SobolevSpace.VectorValued

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def testPairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ψ : Lp ℝ (ENNReal.conjExponent p) μ) : Lp F p μ →L[ℝ] F :=
  ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip.lpPairing
    μ p (ENNReal.conjExponent p)).flip ψ

private theorem testPairing_toLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ψ : X → ℝ} (hψ : MemLp ψ (ENNReal.conjExponent p) μ) {f : X → F}
    (hf : MemLp f p μ) :
    testPairing μ (hψ.toLp ψ) (hf.toLp f) = ∫ x, ψ x • f x ∂μ := by
  rw [testPairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae (hψ.coeFn_toLp.smul hf.coeFn_toLp)

/-- Pairing with a conjugate-exponent real function is continuous under Banach-valued
`L^p` convergence. The convergence is measured by `eLpNorm` of the representatives. -/
theorem tendsto_integral_smul_of_tendsto_eLpNorm {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {l : Filter ι} {ψ : X → ℝ}
    (hψ : MemLp ψ (ENNReal.conjExponent p) μ) {f : ι → X → F} {f₀ : X → F}
    (hf : ∀ j, MemLp (f j) p μ) (hf₀ : MemLp f₀ p μ)
    (hlim : Tendsto (fun j ↦ eLpNorm (f j - f₀) p μ) l (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x, ψ x • f j x ∂μ) l (𝓝 (∫ x, ψ x • f₀ x ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf f₀ hf₀).2 hlim
  simpa only [Function.comp_def, testPairing_toLp hψ] using
    ((testPairing μ (hψ.toLp ψ)).continuous.tendsto _).comp hLp

/-- Simultaneous `L^p` limits of a function and one of its weak derivatives still satisfy
the weak-derivative relation. Both limits and every approximant belong to the `Lp`
class, and the exponent can be either endpoint `1` or `∞`. -/
theorem hasWeakDerivativeOn_of_tendsto_eLpNorm {Ω : Opens ℝ^n} {α : List (Fin n)}
    {ι : Type*} {l : Filter ι} [NeBot l] {f g : ℝ^n → F} {fSeq gSeq : ι → ℝ^n → F}
    (hfSeq : ∀ j, MemLp (fSeq j) p (domainMeasure n Ω))
    (hgSeq : ∀ j, MemLp (gSeq j) p (domainMeasure n Ω))
    (hf : MemLp f p (domainMeasure n Ω)) (hg : MemLp g p (domainMeasure n Ω))
    (hweak : ∀ j, HasWeakDerivativeOn Ω α (fSeq j) (gSeq j))
    (hf_lim : Tendsto (fun j ↦ eLpNorm (fSeq j - f) p (domainMeasure n Ω)) l (𝓝 0))
    (hg_lim : Tendsto (fun j ↦ eLpNorm (gSeq j - g) p (domainMeasure n Ω)) l (𝓝 0)) :
    HasWeakDerivativeOn Ω α f g := by
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable Fact.out),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable Fact.out), ?_⟩
  intro φ
  have hdφ : MemLp (iteratedPartialDeriv α φ.toFun) (ENNReal.conjExponent p)
      (domainMeasure n Ω) :=
    (iteratedPartialDerivTest α φ).contDiff.continuous.memLp_of_hasCompactSupport
      (iteratedPartialDerivTest α φ).hasCompactSupport
  have hφ : MemLp (φ : ℝ^n → ℝ) (ENNReal.conjExponent p) (domainMeasure n Ω) :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hleft := tendsto_integral_smul_of_tendsto_eLpNorm hdφ hfSeq hf hf_lim
  have hright := (tendsto_integral_smul_of_tendsto_eLpNorm hφ hgSeq hg hg_lim).const_smul
    ((-1 : ℝ) ^ α.length)
  exact tendsto_nhds_unique hleft
    (hright.congr (fun j ↦ (hweak j).integral_identity φ |>.symm))

/-- Weak differentiation has a closed graph in the product of the two Banach-valued
`Lp` spaces. This statement uses Mathlib's almost-everywhere quotient and norm topology. -/
theorem isClosed_hasWeakDerivativeOn (Ω : Opens ℝ^n) (α : List (Fin n)) :
    IsClosed {u : Lp F p (domainMeasure n Ω) × Lp F p (domainMeasure n Ω) |
      HasWeakDerivativeOn Ω α u.1 u.2} := by
  apply isSeqClosed_iff_isClosed.mp
  intro u u₀ hu hlim
  apply hasWeakDerivativeOn_of_tendsto_eLpNorm (p := p) (l := atTop)
    (fun j ↦ Lp.memLp (u j).1) (fun j ↦ Lp.memLp (u j).2)
    (Lp.memLp u₀.1) (Lp.memLp u₀.2) hu
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim.fst_nhds
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim.snd_nhds

end SobolevSpace.VectorValued
