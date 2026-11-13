/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Geometry
import PDE.Analysis.Calculus.LocalExtension
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Test-function traces on affine interfaces

Compactly supported spacetime test functions restrict to compactly supported,
integrable functions on every affine interface. A fixed smooth bump also gives
a nonnegative test function with strictly positive interface integral.
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.AffineInterface

noncomputable section

open MeasureTheory
open PDE.Common
open TopologicalSpace

open scoped Distributions Topology
open PDE.Analysis (standardBump)

/-- Restricting a compactly supported spacetime test function to an affine
interface still gives a compactly supported function of time. -/
theorem hasCompactSupport_interface_trace (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) (s : ℝ) :
    HasCompactSupport (fun t : ℝ ↦ φ (interface s t)) := by
  rw [show (fun t : ℝ ↦ φ (interface s t)) =
    (φ : ℝ^2 → ℝ) ∘ interface s by rfl]
  exact φ.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_interface s)

/-- The trace of a compactly supported spacetime test function on an affine
interface is integrable. -/
theorem integrable_interface_trace (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) (s : ℝ) :
    Integrable (fun t : ℝ ↦ φ (interface s t)) volume := by
  exact (φ.contDiff.continuous.comp (continuous_interface s)).integrable_of_hasCompactSupport
      (hasCompactSupport_interface_trace φ s)

/-- The fixed bump as a global `C¹` test function. -/
private noncomputable def unitBumpTestFunction :
    𝓓^{1}((⊤ : Opens ℝ^2), ℝ) :=
  _root_.TestFunction.mk
    (standardBump 2 : ℝ^2 → ℝ)
    (ContDiffBump.contDiff (standardBump 2))
    (ContDiffBump.hasCompactSupport (standardBump 2))
    (Set.subset_univ _)

/-- Every affine interface admits a nonnegative test function whose trace has
strictly positive integral. -/
theorem exists_testFunction_nonneg_integral_interface_pos (s : ℝ) :
    ∃ φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ), (∀ p : ℝ^2, 0 ≤ φ p) ∧ 0 < ∫ t : ℝ,
      φ (interface s t) ∂volume := by
  let φ := unitBumpTestFunction
  have hφ_nonneg : ∀ p : ℝ^2, 0 ≤ φ p := by
    intro p
    change 0 ≤ standardBump 2 p
    exact ContDiffBump.nonneg (standardBump 2)
  refine ⟨φ, hφ_nonneg, ?_⟩
  have hcontinuous : Continuous (fun t : ℝ ↦ φ (interface s t)) :=
    φ.contDiff.continuous.comp (continuous_interface s)
  have hzero : φ (interface s 0) = 1 := by
    change standardBump 2 (interface s 0) = 1
    have hinterface : interface s 0 = 0 := by
      ext i
      fin_cases i <;> simp [interface]
    rw [hinterface]
    apply ContDiffBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self (by simp [standardBump])
  have hnonzero : φ (interface s 0) ≠ 0 := by
    rw [hzero]
    norm_num
  exact hcontinuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hasCompactSupport_interface_trace φ s) (fun t ↦ hφ_nonneg (interface s t)) hnonzero

end

end PDE.Hyperbolic.ConservationLaw.AffineInterface
