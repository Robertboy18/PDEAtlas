/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Basic

/-!
# Equivalent forms of superlinear growth

For a continuous function on a proper normed group, tending to infinity after division
by the norm is equivalent to the affine lower bounds used by the Hopf–Lax construction.
The bound outside a ball follows from the limit; compactness controls the remainder.

This identifies the growth conditions (12) and (19) of Evans, §3.3.2, with `Superlinear`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2, conditions (12) and (19).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi.HopfLax

open Filter Bornology

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- For continuous functions on a proper normed group, the quotient by the norm
tends to infinity at spatial infinity exactly when every affine norm lower bound
is available. The quotient at the origin does not affect this limit. -/
theorem superlinear_iff_tendsto_div_norm {H : E → ℝ} (hcont : Continuous H) :
    Superlinear H ↔ Tendsto (fun p ↦ H p / ‖p‖) (cobounded E) atTop := by
  constructor
  · intro hH
    refine tendsto_atTop.2 fun A ↦ ?_
    obtain ⟨B, hB⟩ := hH (A + 1)
    filter_upwards [eventually_cobounded_le_norm (max 1 B)] with p hp
    have hnorm : 0 < ‖p‖ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hp)
    apply (le_div_iff₀ hnorm).2
    have hlarge : B ≤ ‖p‖ := (le_max_right _ _).trans hp
    nlinarith [hB p]
  · intro hH A
    have htail : ∀ᶠ p in cobounded E, A * ‖p‖ ≤ H p := by
      filter_upwards [hH.eventually_ge_atTop A, eventually_cobounded_le_norm 1] with p hp hn
      exact (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hn)).1 hp
    obtain ⟨R, _, hR⟩ :=
      (Metric.hasBasis_cobounded_compl_closedBall (0 : E)).eventually_iff.mp htail
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) R).bddAbove_image
      ((continuous_const.mul continuous_norm).sub hcont).continuousOn
    refine ⟨max 0 B, fun p ↦ ?_⟩
    by_cases hp : p ∈ Metric.closedBall (0 : E) R
    · have hb : A * ‖p‖ - H p ≤ B := hB ⟨p, hp, rfl⟩
      linarith [le_max_right (0 : ℝ) B]
    · exact (sub_le_self _ (le_max_left (0 : ℝ) B)).trans (hR hp)

end HamiltonJacobi.HopfLax
