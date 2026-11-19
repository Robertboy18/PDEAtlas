/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.OrderZero
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Zero extension of Banach-valued derivative coordinates

The indicator extension acts on each Lᵖ coordinate and preserves the
full derivative-family norm, for every order and both exponent endpoints.
The supported-smooth closure and zero-trace theorems use this same map to prove
that the extended coordinates satisfy the global weak derivative identities.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace GeometricExtension

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend every derivative coordinate by the indicator of the original domain. -/
def zeroExtendAmbient :
    WkpAmbientOn n k p Ω F →L[ℝ] WkpAmbientOn n k p ⊤ F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n univ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦ zeroOrderExtensionLp.comp
      (PiLp.proj p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω)) a))

/-- Coordinate projection commutes with the Lᵖ zero extension. -/
@[simp] theorem zeroExtendAmbient_apply (U : WkpAmbientOn n k p Ω F)
    (a : DerivIndex n k) :
    zeroExtendAmbient U a = zeroOrderExtensionLp (U a) :=
  rfl

/-- Each extended coordinate is represented by the corresponding indicator. -/
theorem zeroExtendAmbient_apply_ae (U : WkpAmbientOn n k p Ω F)
    (a : DerivIndex n k) :
    (zeroExtendAmbient U a : ℝ^n → F) =ᵐ[volume]
      (Ω : Set ℝ^n).indicator (U a : ℝ^n → F) := by
  rw [zeroExtendAmbient_apply]
  simpa only [domainMeasure, Measure.restrict_univ] using
    zeroOrderExtensionLp_apply_ae (U a)

/-- Restricting each extended coordinate recovers the original Lᵖ class. -/
theorem restrict_zeroExtendAmbient (U : WkpAmbientOn n k p Ω F)
    (a : DerivIndex n k) :
    Lp.restrictionCLMOfLE (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
      (zeroExtendAmbient U a) = U a :=
  restrict_zeroOrderExtensionLp (U a)

/-- The full derivative-family norm is preserved, including at exponent infinity. -/
theorem norm_zeroExtendAmbient (U : WkpAmbientOn n k p Ω F) :
    ‖zeroExtendAmbient U‖ = ‖U‖ := by
  apply le_antisymm
  · exact PiLp.norm_mono _ _ fun a ↦ norm_zeroOrderExtensionLp_le (U a)
  · apply PiLp.norm_mono _ _
    intro a
    rw [← restrict_zeroExtendAmbient U a]
    exact Lp.norm_restrictionCLMOfLE_apply_le _ _

end SobolevSpace.VectorValued
