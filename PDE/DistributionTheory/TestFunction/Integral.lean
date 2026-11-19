/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Integration and normalization of compact tests

Integration is linear on smooth compact tests. Every nonempty open subset
of a finite-dimensional real normed space supports a test of integral one
for a locally finite measure positive on nonempty open sets.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped Distributions

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsLocallyFiniteMeasure μ]

/-- Integration as a linear functional on compact tests. -/
def integralLinearMap : 𝓓((⊤ : Opens E), ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, φ x ∂μ
  map_add' φ ψ := integral_add
    (φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
    (ψ.contDiff.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport)
  map_smul' c φ := integral_smul c φ

/-- The integral functional evaluates to the Lebesgue integral. -/
@[simp]
theorem integralLinearMap_apply (φ : 𝓓((⊤ : Opens E), ℝ)) :
    integralLinearMap μ φ = ∫ x, φ x ∂μ :=
  rfl

omit [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] in
/-- A locally integrable coefficient defines an algebraic functional on compact tests. -/
def integralMulLinearMap (f : E → ℝ) (hf : LocallyIntegrable f μ) :
    𝓓((⊤ : Opens E), ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, f x * φ x ∂μ
  map_add' φ ψ := by
    simp only [add_apply, mul_add]
    exact integral_add
      (hf.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport)
      (hf.integrable_smul_right_of_hasCompactSupport ψ.contDiff.continuous ψ.hasCompactSupport)
  map_smul' c φ := by
    change (∫ x, f x * (c * φ x) ∂μ) = c * ∫ x, f x * φ x ∂μ
    calc
      _ = ∫ x, c * (f x * φ x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x ↦ mul_left_comm _ _ _)
      _ = _ := integral_const_mul _ _

omit [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] in
/-- Evaluation of a coefficient functional is its integral pairing. -/
@[simp]
theorem integralMulLinearMap_apply (f : E → ℝ) (hf : LocallyIntegrable f μ)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    integralMulLinearMap μ f hf φ = ∫ x, f x * φ x ∂μ :=
  rfl

/-- A nonempty open set supports a normalized nonnegative compact test. -/
theorem exists_integral_eq_one [μ.IsOpenPosMeasure] {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ φ : 𝓓((⊤ : Opens E), ℝ),
      tsupport φ ⊆ U ∧ (∫ x, φ x ∂μ) = 1 ∧ ∀ x, 0 ≤ φ x := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x :=
    ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨⟨b.normed μ, b.contDiff_normed, b.hasCompactSupport_normed,
    subset_univ _⟩, ?_, b.integral_normed, b.nonneg_normed⟩
  change tsupport (b.normed μ) ⊆ U
  rw [b.tsupport_normed_eq]
  exact (closedBall_subset_ball (half_lt_self hr)).trans hsub

end TestFunction
