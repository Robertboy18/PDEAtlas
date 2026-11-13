/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrated equations under uniform limits

Uniform convergence preserves a linear integrated evolution equation when the
state space embeds continuously into the space where the equation is tested.
The approximating trajectories need only be differentiable after that map.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution

open MeasureTheory
open scoped Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A uniform limit preserves a linear integrated evolution equation.
The approximants are differentiated only after applying `L`; this allows the
state topology to be stronger than the topology of the equation. -/
theorem integral_eq_sub_of_uniform_limit
    (L M : E →L[ℝ] F) {z : ℕ → ℝ → E} {u : ℝ → E} {a b : ℝ}
    (hcont : ∀ n, ContinuousOn (z n) (Icc a b))
    (hu : TendstoUniformlyOn z u atTop (Icc a b))
    (hderiv : ∀ n t, t ∈ Icc a b →
      HasDerivAt (fun s ↦ L (z n s)) (M (z n t)) t) :
    ∀ t ∈ Icc a b, (∫ s in a..t, M (u s)) = L (u t) - L (u a) := by
  intro t ht
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hMcont (n : ℕ) : ContinuousOn (fun s ↦ M (z n s)) (uIcc a t) :=
    M.continuous.comp_continuousOn ((hcont n).mono hsub)
  have hMuniform : TendstoUniformlyOn (fun n s ↦ M (z n s))
      (fun s ↦ M (u s)) atTop (uIcc a t) :=
    M.uniformContinuous.comp_tendstoUniformlyOn (hu.mono hsub)
  have hint := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (Eventually.of_forall hMcont) hMuniform
  have hright :=
    (L.continuous.continuousAt.tendsto.comp (hu.tendsto_at ht)).sub
      (L.continuous.continuousAt.tendsto.comp
        (hu.tendsto_at (left_mem_Icc.mpr (ht.1.trans ht.2))))
  apply tendsto_nhds_unique hint
  apply hright.congr'
  filter_upwards [] with n
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ hderiv n s (hsub hs))
    (hMcont n).intervalIntegrable).symm

end PDE.Analysis.Evolution
