/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue

/-!
# Identifying the normalized Hilbert velocity

The spectral relation determines a velocity derivative only almost everywhere.
For a differentiable velocity, its locally integrable derivative recovers every
increment by the fundamental theorem of calculus. Fixing the value at zero then
identifies the velocity with the principal-value primitive.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis

/-- A differentiable velocity with the spectral Hilbert derivative and value
zero at the origin is the normalized principal-value velocity. Compact
Lipschitz vorticity is enough; its endpoint derivative may jump. -/
theorem IsHilbertPair.eq_hilbertPVVelocity_of_normalized
    {ω u : ℝ → ℝ} {K : ℝ≥0}
    (hpair : IsHilbertPair ω (deriv u)) (hu : Differentiable ℝ u)
    (hω : LipschitzWith K ω) (hc : HasCompactSupport ω) (hu0 : u 0 = 0) :
    u = hilbertPVVelocity ω := by
  have hae := hpair.ae_eq_right (.of_lipschitzWith_compactSupport hω hc)
  funext x
  have hint : IntervalIntegrable (deriv u) volume 0 x :=
    ((hpair.memLp_right.locallyIntegrable (by norm_num)).integrableOn_isCompact
      isCompact_uIcc).intervalIntegrable
  calc
    u x = ∫ y in (0 : ℝ)..x, deriv u y := by
      simpa only [hu0, sub_zero] using
        (intervalIntegral.integral_deriv_eq_sub (fun y _ ↦ hu y) hint).symm
    _ = hilbertPVVelocity ω x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hae] with y hy _
      exact hy

end PDE.Analysis
