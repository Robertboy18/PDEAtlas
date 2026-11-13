/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Evaluating a regular distribution on its domain

Mathlib defines a regular distribution using an integral over the ambient
space. The test function vanishes outside its domain, so the same pairing is
a set integral over that domain. Local integrability is sufficient.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {k : ℕ∞}

/-- A regular distribution is evaluated by integrating over the open domain
containing the test support. -/
theorem ofFun_apply_eq_setIntegral {f : E → F}
    (hf : LocallyIntegrableOn f (Ω : Set E) μ) (φ : 𝓓^{k}(Ω, ℝ)) :
    ofFun Ω f μ k φ = ∫ x in (Ω : Set E), φ x • f x ∂μ := by
  rw [ofFun_apply hf]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport
    (fun h ↦ hx (φ.tsupport_subset h)), zero_smul]

/-- Scalar evaluation with the coefficient written before the test function,
as in the usual weak derivative identity. -/
theorem ofFun_apply_eq_setIntegral_mul {f : E → ℝ}
    (hf : LocallyIntegrableOn f (Ω : Set E) μ) (φ : 𝓓^{k}(Ω, ℝ)) :
    ofFun Ω f μ k φ = ∫ x in (Ω : Set E), f x * φ x ∂μ := by
  simpa only [smul_eq_mul, mul_comm] using ofFun_apply_eq_setIntegral hf φ

end Distribution
