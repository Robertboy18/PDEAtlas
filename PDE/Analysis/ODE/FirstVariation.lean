/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The first-variation ODE

For an autonomous ODE

`q' = v(q)`,

the derivative of the flow with respect to its initial state, when it
exists, satisfies

`J' = Dv(q) ∘ J`, `J(0) = id`.

We solve the coupled `(q,J)` ODE directly.  If `v` is `C²`, then the
coupled vector field is `C¹`, so Mathlib's Picard–Lindelöf theorem gives a
jointly continuous local family with a common lifespan, satisfying the
initial condition and both differential equations.  Identifying `J` with
the derivative of the `q`-flow is the smooth-dependence theorem
(`PDE.Analysis.ODE.SmoothDependence`), which needs a Taylor-remainder
argument.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- State space for an integral curve together with its first variation. -/
private abbrev FirstVariationState (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :=
  E × (E →L[ℝ] E)

/-- The coupled vector field for a trajectory and its first variation. -/
def firstVariationVectorField (v : E → E) :
    (E × (E →L[ℝ] E)) → E × (E →L[ℝ] E) :=
  fun qJ ↦ (v qJ.1, (fderiv ℝ v qJ.1).comp qJ.2)

/-- The first-variation field loses one derivative because it contains `Dv`. -/
theorem contDiff_firstVariationVectorField_succ
    (n : ℕ) (v : E → E) (hv : ContDiff ℝ (n + 1) v) :
    ContDiff ℝ n (firstVariationVectorField v) := by
  have hq : ContDiff ℝ n (fun qJ : FirstVariationState E ↦ qJ.1) :=
    contDiff_fst
  have hJ : ContDiff ℝ n (fun qJ : FirstVariationState E ↦ qJ.2) :=
    contDiff_snd
  have hDv : ContDiff ℝ n (fun qJ : FirstVariationState E ↦ fderiv ℝ v qJ.1) :=
    (hv.fderiv_right (m := n) le_rfl).comp hq
  exact ((hv.of_le (by simp)).comp hq).prodMk (hDv.clm_comp hJ)

/-- A local family of trajectories together with solutions of the
first-variation equation.

The initial matrix is the identity for every initial state in the ball.
All trajectories and matrices share the same symmetric time interval. -/
theorem exists_local_firstVariation_family
    [CompleteSpace E]
    (v : E → E) (hv : ContDiff ℝ 2 v) (q0 : E) :
    ∃ r : ℝ, 0 < r ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ flow : E × ℝ → E,
          ∃ variation : E × ℝ → (E →L[ℝ] E),
            ContinuousOn flow
              (closedBall q0 r ×ˢ Icc (-ε) ε) ∧
            ContinuousOn variation
              (closedBall q0 r ×ˢ Icc (-ε) ε) ∧
            ∀ q ∈ closedBall q0 r,
              flow (q, 0) = q ∧
              variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
              ∀ s ∈ Ioo (-ε) ε,
                HasDerivAt (fun τ ↦ flow (q, τ))
                  (v (flow (q, s))) s ∧
                HasDerivAt (fun τ ↦ variation (q, τ))
                  ((fderiv ℝ v (flow (q, s))).comp
                    (variation (q, s))) s := by
  set I : E → E × (E →L[ℝ] E) := fun q ↦ (q, ContinuousLinearMap.id ℝ E)
  obtain ⟨ε, hε, a, R, L, K, hR, hpl⟩ := IsPicardLindelof.of_contDiffAt_one (x₀ := I q0)
    (contDiff_firstVariationVectorField_succ 1 v hv).contDiffAt
  obtain ⟨augFlow, haugFlow, hcontinuous⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at haugFlow hcontinuous
  have hI : ∀ q ∈ closedBall q0 (R / 2), I q ∈ closedBall (I q0) R := fun q hq ↦ by
    simpa [I, Prod.dist_eq, max_eq_left dist_nonneg] using
      (mem_closedBall.1 hq).trans (half_le_self hR.le)
  have hc : ContinuousOn (fun qs : E × ℝ ↦ augFlow (I qs.1, qs.2))
      (closedBall q0 (R / 2) ×ˢ Icc (-ε) ε) :=
    hcontinuous.comp (by fun_prop : Continuous fun qs : E × ℝ ↦ (I qs.1, qs.2)).continuousOn
      fun qs hqs ↦ ⟨hI _ hqs.1, hqs.2⟩
  refine ⟨R / 2, half_pos hR, ε, hε, fun qs ↦ (augFlow (I qs.1, qs.2)).1,
    fun qs ↦ (augFlow (I qs.1, qs.2)).2, hc.fst, hc.snd, fun q hq ↦ ?_⟩
  obtain ⟨hzero, hderiv⟩ := haugFlow _ (hI q hq)
  refine ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero, fun s hs ↦ ?_⟩
  have h := (hderiv s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  exact ⟨(ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt s h,
    (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt s h⟩

end

end PDE.Analysis.ODE
