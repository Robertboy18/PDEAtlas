/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Identifying representatives by Schwartz tests

Equality against Schwartz functions identifies locally integrable functions
almost everywhere, and continuous functions pointwise. No global growth bound
is needed: compactly supported smooth tests already suffice.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} {u v : E → F}

namespace PDE

/-- Schwartz-test equality identifies locally integrable representatives
without a growth assumption. -/
theorem ae_eq_of_integral_schwartz_smul_eq
    (hu : LocallyIntegrable u μ) (hv : LocallyIntegrable v μ)
    (h : ∀ φ : 𝓢(E, ℂ), (∫ x, φ x • u x ∂μ) = ∫ x, φ x • v x ∂μ) :
    u =ᵐ[μ] v := by
  apply ae_eq_of_integral_contDiff_smul_eq hu hv
  intro ψ hψ hcs
  have hcs' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hcs.comp_left rfl
  have hψ' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have htest := h (hcs'.toSchwartzMap hψ')
  change (∫ x, (ψ x : ℂ) • u x ∂μ) = ∫ x, (ψ x : ℂ) • v x ∂μ at htest
  simpa only [Complex.coe_smul] using htest

end PDE

/-- Continuous representatives with equal Schwartz tests agree at every point. -/
theorem Continuous.eq_of_integral_schwartz_smul_eq
    [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hu : Continuous u) (hv : Continuous v)
    (h : ∀ φ : 𝓢(E, ℂ), (∫ x, φ x • u x ∂μ) = ∫ x, φ x • v x ∂μ) :
    u = v :=
  Measure.eq_of_ae_eq
    (PDE.ae_eq_of_integral_schwartz_smul_eq hu.locallyIntegrable hv.locallyIntegrable h) hu hv
