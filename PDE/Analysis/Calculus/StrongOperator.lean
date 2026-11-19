/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strongly continuous operator actions

A family of operators that is continuous at every fixed vector and locally bounded
in operator norm acts jointly continuously on time and vector. Continuity in
operator norm is not needed; this covers strongly continuous semigroups and
families built from dilations.

For a moving vector `u(t)`, split the difference quotient of `A(t)u(t)` into the
change of the operator at the fixed vector `u(x)` and the operator applied to the
difference quotient of `u`. Joint continuity of the action passes the second term
to its limit. This product rule therefore applies to strongly continuous semigroups
whose generators need not be bounded.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Strong continuity and a locally uniform operator bound give joint continuity of
the action `(t, x) ↦ L t x`. -/
theorem continuous_apply_prod_of_eventually_norm_le {X : Type*} [TopologicalSpace X]
    {L : X → E →L[𝕜] F} (hL : ∀ x, Continuous fun t ↦ L t x)
    (hbdd : ∀ t₀, ∃ C, ∀ᶠ t in 𝓝 t₀, ‖L t‖ ≤ C) :
    Continuous fun p : X × E ↦ L p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨C, hC⟩ := hbdd p.1
  change Tendsto (fun q : X × E ↦ L q.1 q.2) (𝓝 p) (𝓝 (L p.1 p.2))
  have hsmall : Tendsto (fun q : X × E ↦ L q.1 (q.2 - p.2)) (𝓝 p) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun q : X × E ↦ C * ‖q.2 - p.2‖) ?_ ?_
    · filter_upwards [continuous_fst.continuousAt.eventually hC] with q hq
      exact (L q.1).le_of_opNorm_le hq _
    · have hcont : Continuous (fun q : X × E ↦ C * ‖q.2 - p.2‖) :=
        (continuous_snd.sub continuous_const).norm.const_mul C
      simpa only [sub_self, norm_zero, mul_zero] using hcont.tendsto p
  have horbit : Tendsto (fun q : X × E ↦ L q.1 p.2) (𝓝 p) (𝓝 (L p.1 p.2)) :=
    (hL p.2).continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add horbit

/-- Strong continuity and a uniform operator bound give joint continuity of the
action `(t, x) ↦ L t x`. -/
theorem continuous_apply_prod_of_norm_le {X : Type*} [TopologicalSpace X]
    {L : X → E →L[𝕜] F} {C : ℝ} (hL : ∀ x, Continuous fun t ↦ L t x)
    (hLC : ∀ t, ‖L t‖ ≤ C) :
    Continuous fun p : X × E ↦ L p.1 p.2 :=
  continuous_apply_prod_of_eventually_norm_le hL fun _ ↦ ⟨C, Eventually.of_forall hLC⟩

/-- Differentiate an operator action using joint continuity and the derivative at
the fixed vector, without requiring an operator-norm derivative. -/
theorem hasDerivWithinAt_clm_apply_of_continuousAt
    {A : 𝕜 → E →L[𝕜] F} {u : 𝕜 → E} {u' : E} {v : F} {s : Set 𝕜} {x : 𝕜}
    (hA : ContinuousAt (fun p : 𝕜 × E ↦ A p.1 p.2) (x, u'))
    (hfixed : HasDerivWithinAt (fun t ↦ A t (u x)) v s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun t ↦ A t (u t)) (v + A x u') s x := by
  have htime : Tendsto (fun t : 𝕜 ↦ t) (𝓝[s \ {x}] x) (𝓝 x) :=
    nhdsWithin_le_nhds
  have hmoving := hA.tendsto.comp
    (htime.prodMk_nhds (hasDerivWithinAt_iff_tendsto_slope.mp hu))
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  refine ((hasDerivWithinAt_iff_tendsto_slope.mp hfixed).add hmoving).congr'
    (Eventually.of_forall fun t ↦ ?_)
  change (t - x)⁻¹ • (A t (u x) - A x (u x)) +
    A t ((t - x)⁻¹ • (u t - u x)) =
      (t - x)⁻¹ • (A t (u t) - A x (u x))
  rw [map_smul, map_sub]
  module

end PDE.Analysis
