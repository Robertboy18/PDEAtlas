/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.WeightedCancellation
public import PDE.Analysis.Calculus.OriginQuotient

/-!
# Cubic Hilbert cancellation from the origin jet

Compact Lipschitz odd input with zero origin slope has the singular quotient
needed for the cancellation. Local C² regularity at zero is enough; corners
at the support endpoints are allowed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

noncomputable section

namespace PDE.Analysis


/-- The cubic-weight cancellation is absolutely integrable and vanishes for compact
Lipschitz odd input with a vanishing origin slope and local C² regularity. -/
theorem origin_cubic_cancellation_of_contDiffAt
    {L : ℝ} {omega : ℝ → ℝ} {K : ℝ≥0}
    (homega : LipschitzWith K omega) (hcompact : HasCompactSupport omega)
    (hodd : Function.Odd omega) (hsupport : ∀ y, L ≤ y → omega y = 0)
    (hregular : ContDiffAt ℝ 2 omega 0) (hderivzero : deriv omega 0 = 0) :
    IntegrableOn (fun x ↦ (hilbertPV omega x - hilbertPV omega 0) * omega x / x ^ 3)
        (Ioo 0 L) ∧
      (∫ x in Ioo 0 L, (hilbertPV omega x - hilbertPV omega 0) * omega x / x ^ 3) = 0 := by
  have hsecond := Calculus.memLp_div_sq_of_contDiffAt homega.continuous hcompact
    hregular hodd.map_zero hderivzero 2
  exact ⟨(integrable_hilbertPV_sub_zero_mul_div_cube homega hcompact hsecond).integrableOn,
    integral_Ioo_hilbertPV_sub_zero_mul_div_cube homega hcompact hodd hsupport hsecond⟩

end PDE.Analysis
