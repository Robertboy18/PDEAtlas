/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.WkpExtensionByZero
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# The gradient of a zero extension

Zero extension preserves the full Euclidean gradient norm, not just the norms of
its individual coordinates. The coordinate identities identify the extended
gradient with the indicator extension of the original vector field; the exact
`Lᵖ` norm identity then follows from Mathlib's formula for an indicator.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.ZeroTrace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Zero extension of the scalar Sobolev function extends its vector-valued weak
gradient by zero. This includes the endpoint exponent `∞`. -/
theorem wkpGradientCLM_zeroExtendWkp0_ae (hΩ : MeasurableSet Ω)
    (u : W₀^{1,p}(Ω)) :
    (∇ (zeroExtendWkp0 hΩ u) : ℝ^n → ℝ^n) =ᵐ[volume]
      Ω.indicator (∇ (u : W^{1,p}(Ω)) : ℝ^n → ℝ^n) := by
  have hlocal := wkpGradientCLM_apply_ae (u : W^{1,p}(Ω))
  change ∀ᵐ x ∂volume.restrict Ω, _ at hlocal
  have hlocal' := (ae_restrict_iff' hΩ).mp hlocal
  have hglobal := wkpGradientCLM_apply_ae (zeroExtendWkp0 hΩ u)
  simp only [domainMeasure, Measure.restrict_univ] at hglobal
  have hrows : ∀ᵐ x ∂volume, ∀ i : Fin n,
      wkpCoordinateCLM (singleDerivIndex n i) (zeroExtendWkp0 hΩ u) x =
        Ω.indicator
          (wkpCoordinateCLM (singleDerivIndex n i) (u : W^{1,p}(Ω)) : ℝ^n → ℝ)
          x := ae_all_iff.mpr fun i ↦
    zeroExtendWkp0_coordinate_apply_ae hΩ u (singleDerivIndex n i)
  filter_upwards [hlocal', hglobal, hrows] with x hl hg hr
  apply PiLp.ext
  intro i
  rw [hg i]
  change wkpCoordinateCLM (singleDerivIndex n i) (zeroExtendWkp0 hΩ u) x = _
  rw [hr i]
  by_cases hx : x ∈ Ω
  · simpa only [indicator_of_mem hx, wkpCoordinateCLM_apply] using (hl hx i).symm
  · simp only [indicator_of_notMem hx, PiLp.zero_apply]

/-- Zero extension preserves the Euclidean weak-gradient norm at every Sobolev
exponent, including `∞`. -/
theorem norm_wkpGradientCLM_zeroExtendWkp0 (hΩ : MeasurableSet Ω)
    (u : W₀^{1,p}(Ω)) :
    ‖∇ (zeroExtendWkp0 hΩ u)‖ =
      ‖∇ (u : W^{1,p}(Ω))‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  simp only [domainMeasure, Measure.restrict_univ]
  rw [eLpNorm_congr_ae (wkpGradientCLM_zeroExtendWkp0_ae hΩ u),
    eLpNorm_indicator_eq_eLpNorm_restrict hΩ.nullMeasurableSet]

end SobolevSpace.GraphSpace.ZeroTrace
