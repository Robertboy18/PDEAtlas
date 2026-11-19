/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Absolute-continuity calculus for evolution equations

Operations on absolutely continuous Banach-valued curves. The results are
independent of any evolution equation: they apply a curve of continuous
linear maps to a curve of vectors and form finite sums.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

/--
Applying an absolutely continuous curve of continuous linear maps to an
absolutely continuous vector curve preserves absolute continuity.

This is the Banach-valued product rule at the level of absolute continuity.
The proof uses boundedness of both curves on the compact interval and the
operator estimates

`‖c(s)(u(s)-u(t))‖ ≤ ‖c(s)‖ ‖u(s)-u(t)‖`,

`‖(c(s)-c(t))u(t)‖ ≤ ‖c(s)-c(t)‖ ‖u(t)‖`.
-/
theorem AbsolutelyContinuousOnInterval.clm_apply
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : ℝ → E →L[ℝ] F} {u : ℝ → E} {a b : ℝ}
    (hc : AbsolutelyContinuousOnInterval c a b)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ c t (u t)) a b := by
  obtain ⟨C, hC⟩ := hc.exists_bound
  obtain ⟨D, hD⟩ := hu.exists_bound
  unfold AbsolutelyContinuousOnInterval at hc hu ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using (hu.const_mul C).add (hc.const_mul D))
  · exact .of_forall fun _ ↦ Finset.sum_nonneg fun i hi ↦ dist_nonneg
  rw [Filter.eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i hi
  simp only [_root_.AbsolutelyContinuousOnInterval.disjWithin, mem_ofPred_eq] at hnI
  calc dist (c (I i).1 (u (I i).1)) (c (I i).2 (u (I i).2))
      ≤ dist (c (I i).1 (u (I i).1)) (c (I i).1 (u (I i).2)) +
          ‖(c (I i).1 - c (I i).2) (u (I i).2)‖ := by
        rw [sub_apply, ← dist_eq_norm]; exact dist_triangle _ _ _
    _ ≤ C * dist (u (I i).1) (u (I i).2) + D * dist (c (I i).1) (c (I i).2) := by
      rw [dist_eq_norm (c _), mul_comm D]
      gcongr
      · exact ((c _).dist_le_opNorm _ _).trans (by gcongr; exact hC _ (hnI.1 i hi).1)
      · exact (c _ - c _).le_of_opNorm_le_of_le le_rfl (hD _ (hnI.1 i hi).2)

/-- A finite sum of absolutely continuous curves is absolutely continuous. -/
theorem AbsolutelyContinuousOnInterval.finset_sum
    {E ι : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (s : Finset ι) {f : ι → ℝ → E}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (LipschitzWith.const (0 : E)).lipschitzOnWith.absolutelyContinuousOnInterval
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).fun_add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

end PDE.Analysis.Evolution
