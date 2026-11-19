/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Continuity of Sobolev inclusions

If every base representative in `W^{k,p}(Ω)` belongs to `L^q(Ω)`, with `p,q ≥ 1`,
the inclusion is automatically continuous. Both spaces are complete, and convergence
in either norm implies convergence in measure of the base representative. Uniqueness
of that limit closes the graph.

The construction uses Mathlib's `LpSubmodule` to retain the same almost-everywhere
equivalence class at the new exponent. The analytic membership theorem remains an
explicit input; no bound is assumed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace
open scoped ENNReal Topology Sobolev

variable {n k : ℕ} {p q : ℝ≥0∞} {Ω : Set (ℝ^n)}
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A set-theoretic Sobolev inclusion into `L^q`, for `p,q ≥ 1`, is bounded.
The closed graph theorem supplies continuity from the membership statement. -/
def embeddingCLMOfMemLp
    (hmem : ∀ U : W^{k,p}(Ω),
      MemLp (baseRepresentative U) q (domainMeasure n Ω)) :
    W^{k,p}(Ω) →L[ℝ] Lp ℝ q (domainMeasure n Ω) :=
  let base := wkpBaseCoordinateCLM (n := n) (m := k) (p := p) (Ω := Ω)
  let inclusion : W^{k,p}(Ω) →ₗ[ℝ] Lp ℝ q (domainMeasure n Ω) :=
    LinearMap.codRestrict (Lp.LpSubmodule ℝ ℝ q (domainMeasure n Ω))
      ((Lp.LpSubmodule ℝ ℝ p (domainMeasure n Ω)).subtype.comp base.toLinearMap)
      (fun U ↦ Lp.mem_Lp_iff_memLp.mpr (hmem U))
  ContinuousLinearMap.ofSeqClosedGraph (g := inclusion) (by
    intro u x y hux huy
    have hbase := tendstoInMeasure_of_tendsto_Lp
      ((base.continuous.tendsto x).comp hux)
    have htarget := tendstoInMeasure_of_tendsto_Lp huy
    exact Lp.ext (tendstoInMeasure_ae_unique htarget hbase))

/-- Changing the exponent retains the original base representative. -/
@[simp]
theorem embeddingCLMOfMemLp_apply
    (hmem : ∀ U : W^{k,p}(Ω),
      MemLp (baseRepresentative U) q (domainMeasure n Ω))
    (U : W^{k,p}(Ω)) :
    (embeddingCLMOfMemLp hmem U : ℝ^n → ℝ) = baseRepresentative U :=
  rfl

/-- The operator norm bounds the `L^q` seminorm of every base representative. -/
theorem eLpNorm_le_embeddingCLMOfMemLp
    (hmem : ∀ U : W^{k,p}(Ω),
      MemLp (baseRepresentative U) q (domainMeasure n Ω))
    (U : W^{k,p}(Ω)) :
    eLpNorm (baseRepresentative U) q (domainMeasure n Ω) ≤
      ENNReal.ofReal (‖embeddingCLMOfMemLp hmem‖ * ‖U‖) := by
  have hbound := ENNReal.ofReal_le_ofReal ((embeddingCLMOfMemLp hmem).le_opNorm U)
  simpa only [Lp.norm_def, embeddingCLMOfMemLp_apply,
    ENNReal.ofReal_toReal (hmem U).eLpNorm_ne_top] using hbound

/-- Any such inclusion has a single positive norm bound, independent of the function. -/
theorem exists_pos_eLpNorm_bound_of_memLp
    (hmem : ∀ U : W^{k,p}(Ω),
      MemLp (baseRepresentative U) q (domainMeasure n Ω)) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,p}(Ω),
      eLpNorm (baseRepresentative U) q (domainMeasure n Ω) ≤
        ENNReal.ofReal (C * ‖U‖) := by
  refine ⟨‖embeddingCLMOfMemLp hmem‖ + 1, by positivity, fun U ↦ ?_⟩
  exact (eLpNorm_le_embeddingCLMOfMemLp hmem U).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg U)))

end SobolevSpace.Inequalities
