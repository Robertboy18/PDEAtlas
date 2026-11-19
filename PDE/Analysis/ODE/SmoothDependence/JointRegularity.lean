/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PartialRegularity

/-!
# Joint regularity from the derivatives of a flow

On an open cylinder, initial-state and time derivatives of class `Cⁿ` give a
jointly `Cⁿ⁺¹` flow. Its differential sends `(h, τ)` to
`variation(q,t) h + τ • v(flow(q,t))`. We apply the general partial-regularity
theorem to the state derivative and to the linear map given by the time derivative.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- State and time derivatives of class `Cⁿ` give joint `Cⁿ⁺¹` regularity.
The differential sends `(h, τ)` to `variation(q,t) h + τ • v(flow(q,t))`. -/
theorem contDiffOn_succ_flow_of_partial_derivatives (n : ℕ)
    (v : E → E) (flow : E × ℝ → E) (variation : E × ℝ → (E →L[ℝ] E))
    (U : Set E) (I : Set ℝ) (hU : IsOpen U) (hI : IsOpen I)
    (hv : ContDiff ℝ n v)
    (hflow : ContDiffOn ℝ n flow (U ×ˢ I))
    (hvariation : ContDiffOn ℝ n variation (U ×ˢ I))
    (hspace : ∀ q ∈ U, ∀ t ∈ I,
      HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q)
    (htime : ∀ q ∈ U, ∀ t ∈ I,
      HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t) :
    ContDiffOn ℝ (n + 1) flow (U ×ˢ I) := by
  let velocity : E × ℝ → ℝ →L[ℝ] E :=
    fun qt ↦ ContinuousLinearMap.toSpanSingleton ℝ (v (flow qt))
  have hvelocity : ContDiffOn ℝ n velocity (U ×ˢ I) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).contDiff.comp_contDiffOn
      (hv.comp_contDiffOn hflow)
  exact contDiffOn_succ_of_partial_derivatives (hU.prod hI) hvariation hvelocity
    (fun qt hqt ↦ hspace qt.1 hqt.1 qt.2 hqt.2)
    (fun qt hqt ↦ (htime qt.1 hqt.1 qt.2 hqt.2).hasFDerivAt)

end

end PDE.Analysis.ODE
