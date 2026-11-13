/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall
import Mathlib.Analysis.Convex.Integral

/-!
# Integration of weakly Sobolev-bounded L² families

An L²-integrable family with uniformly bounded Hᵏ graphs has a
Sobolev graph for its integral. Closedness of the bounded graph image in L²
and Jensen's theorem construct the derivative coordinates without requiring
strong measurability of the family in the Hᵏ norm.

This is useful for the time integral in the flow Jacobian: the input
topology is L², while the highest spatial derivative is only uniformly
bounded. A common support enclosure is preserved by the same construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace SobolevSpace.GraphSpace

/-- The L² image of a bounded Sobolev graph ball is convex. -/
theorem convex_hkBaseBall (n k : ℕ) (Ω : Set (ℝ^n)) (B : ℝ) :
    Convex ℝ (hkBaseBall n k Ω B) := by
  intro f hf g hg a b ha hb hab
  obtain ⟨U, hU, rfl⟩ := hf
  obtain ⟨V, hV, rfl⟩ := hg
  refine ⟨a • U + b • V, ?_, by simp⟩
  calc
    ‖a • U + b • V‖ ≤ ‖a • U‖ + ‖b • V‖ := norm_add_le _ _
    _ = a * ‖U‖ + b * ‖V‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * B + b * B := add_le_add
      (mul_le_mul_of_nonneg_left hU ha) (mul_le_mul_of_nonneg_left hV hb)
    _ = B := by rw [← add_mul, hab, one_mul]

/-- Integrating in L² constructs the weak derivative graph of the integral
and bounds its norm by the measure of the parameter space times the input
graph budget. No Hᵏ-valued integrability assumption is required. -/
theorem integral_mem_hkBaseBall
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {n k : ℕ} {Ω : Set (ℝ^n)} {B : ℝ} {f : α → DerivLp n 2 Ω}
    (hf : Integrable f μ) (hbound : ∀ᵐ t ∂μ, f t ∈ hkBaseBall n k Ω B) :
    (∫ t, f t ∂μ) ∈ hkBaseBall n k Ω (μ.real univ * B) := by
  by_cases hμ : μ = 0
  · subst μ
    refine ⟨0, ?_, ?_⟩ <;> simp
  have : NeZero μ := ⟨hμ⟩
  obtain ⟨U, hU, hbase⟩ := (convex_hkBaseBall n k Ω B).average_mem
    (isClosed_hkBaseBall n k Ω B) hbound hf
  refine ⟨μ.real univ • U, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact mul_le_mul_of_nonneg_left hU measureReal_nonneg
  · rw [map_smul, hbase, measure_smul_average]

/-- A common almost-everywhere support enclosure survives integration
together with the Sobolev graph bound. -/
theorem integral_mem_supportedHkBaseBall
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {n k : ℕ} {Ω K : Set (ℝ^n)} {B : ℝ} {f : α → DerivLp n 2 Ω}
    (hf : Integrable f μ) (hbound : ∀ᵐ t ∂μ, f t ∈ supportedHkBaseBall n k Ω K B) :
    (∫ t, f t ∂μ) ∈ supportedHkBaseBall n k Ω K (μ.real univ * B) := by
  refine ⟨integral_mem_hkBaseBall hf (hbound.mono fun _ h ↦ h.1), ?_⟩
  change LpToLpRestrictCLM (ℝ^n) ℝ ℝ (domainMeasure n Ω) 2 Kᶜ (∫ t, f t ∂μ) = 0
  rw [← (LpToLpRestrictCLM (ℝ^n) ℝ ℝ (domainMeasure n Ω) 2 Kᶜ).integral_comp_comm hf]
  exact integral_eq_zero_of_ae (hbound.mono fun _ h ↦ h.2)

end SobolevSpace.GraphSpace
