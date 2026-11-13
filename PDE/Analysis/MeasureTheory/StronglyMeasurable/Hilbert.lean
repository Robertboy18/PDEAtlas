/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Scalar measurability in a separable Hilbert space

An orthonormal family in a separable Hilbert space is countable, since small balls
about its members are disjoint. Expanding in a Hilbert basis then shows that scalar
measurability implies strong measurability.
-/

@[expose] public section

open Filter MeasureTheory TopologicalSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthonormal family in a separable real Hilbert space has countable index set. -/
theorem Orthonormal.countable_index [SeparableSpace E]
    {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v) : Countable ι := by
  have hd : Pairwise (Function.onFun Disjoint (fun i ↦ Metric.ball (v i) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have heq : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hv.norm_eq_one, hv.norm_eq_one, hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  exact hd.countable_of_isOpen_disjoint
    (fun _ ↦ Metric.isOpen_ball) (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))

namespace MeasureTheory

/-- Scalar measurability implies strong measurability for a separable real Hilbert space. -/
theorem aestronglyMeasurable_of_forall_inner
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [CompleteSpace E] [SeparableSpace E] {f : α → E}
    (hf : ∀ v : E, AEStronglyMeasurable (fun t ↦ inner ℝ v (f t)) μ) :
    AEStronglyMeasurable f μ := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℝ) (E := E)
  have : Countable s := b.orthonormal.countable_index
  apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun I : Finset s ↦ fun t ↦ ∑ i ∈ I, b.repr (f t) i • b i)
  · intro I
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    simpa only [b.repr_apply_apply] using (hf (b i)).smul_const (b i)
  · exact Eventually.of_forall fun t ↦ b.hasSum_repr (f t)

end MeasureTheory

namespace ContinuousLinearMap

/-- Measurable evaluations determine a strongly measurable dual-valued map on a separable
real Hilbert space, by Riesz representation and scalar Hilbert-space measurability. -/
theorem aestronglyMeasurable_dual_of_forall_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [CompleteSpace E] [SeparableSpace E] {f : α → StrongDual ℝ E}
    (hf : ∀ v : E, AEStronglyMeasurable (fun t ↦ f t v) μ) :
    AEStronglyMeasurable f μ := by
  have h : AEStronglyMeasurable
      (fun t ↦ (InnerProductSpace.toDual ℝ E).symm (f t)) μ := by
    apply MeasureTheory.aestronglyMeasurable_of_forall_inner
    intro v
    apply (hf v).congr
    filter_upwards with t
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (InnerProductSpace.toDual ℝ E).continuous.comp_aestronglyMeasurable h

end ContinuousLinearMap
