/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Infinity.WeakGradient
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum

/-!
# Banach-valued W¹,∞ representatives

A Sobolev graph element gives locally integrable functions and bounded weak derivative
rows. The bounded-gradient theorem constructs a globally Lipschitz representative.
Full support of volume upgrades the essential base bound to an everywhere bound,
so the resulting bounded continuous function has exactly the base coordinate's L∞ norm.

The Lipschitz constant is the sum of the first-coordinate norms. The argument works
in dimension zero and for any complete real normed codomain.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem ae_norm_coordinate_le (U : W^{1,∞}(ℝ^n; F)) (a : DerivIndex n 1) :
    ∀ᵐ x ∂volume, ‖U.val a x‖ ≤ ‖U.val a‖ := by
  have hfinite : eLpNormEssSup (U.val a) (domainMeasure n (⊤ : Opens ℝ^n)) ≠ ∞ := by
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable (U.val a))]
    exact Lp.eLpNorm_ne_top _
  have hbound := ae_le_eLpNormEssSup (f := U.val a) (μ := domainMeasure n (⊤ : Opens ℝ^n))
  have h : ∀ᵐ x ∂domainMeasure n (⊤ : Opens ℝ^n), ‖U.val a x‖ ≤ ‖U.val a‖ := by
    filter_upwards [hbound] with x hx
    simpa only [toReal_enorm, Lp.norm_def,
      eLpNorm_exponent_top (Lp.aestronglyMeasurable (U.val a))] using
      ENNReal.toReal_mono hfinite hx
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using h

/-- Every Banach-valued W¹,∞ class has a Lipschitz representative. Its constant
uses the derivative-row norms and is zero in dimension zero. -/
theorem WkpSpaceOn.exists_lipschitzWith_baseRepresentative (U : W^{1,∞}(ℝ^n; F)) :
    ∃ f : ℝ^n → F,
      LipschitzWith (∑ j : Fin n, ‖U.val (singleDerivIndex n j)‖₊) f ∧
      f =ᵐ[volume] (U.val (baseIndex n 1) : ℝ^n → F) := by
  apply exists_lipschitzWith_ae_eq_of_weak_derivative_bound
    (locallyIntegrableOn_univ.mp (U.property (baseIndex n 1)).locallyIntegrable_f)
    (fun j ↦ (U.val (singleDerivIndex n j) : ℝ^n → F))
    (fun j ↦ ?_) (fun j ↦ ‖U.val (singleDerivIndex n j)‖₊)
    (fun j ↦ ae_norm_coordinate_le U (singleDerivIndex n j))
  simpa only [singleDerivIndex_toList] using U.property (singleDerivIndex n j)

/-- The Lipschitz representative is bounded by the L∞ base norm. No continuity
of the original `Lp` representative is assumed. -/
theorem exists_boundedContinuous_lipschitz_representative (U : W^{1,∞}(ℝ^n; F)) :
    ∃ f : ℝ^n →ᵇ F,
      LipschitzWith (∑ j : Fin n, ‖U.val (singleDerivIndex n j)‖₊) f ∧
      (f : ℝ^n → F) =ᵐ[volume] (U.val (baseIndex n 1) : ℝ^n → F) ∧
      ‖f‖ ≤ ‖U.val (baseIndex n 1)‖ := by
  obtain ⟨f, hLip, heq⟩ := WkpSpaceOn.exists_lipschitzWith_baseRepresentative U
  have hbound : ∀ x, ‖f x‖ ≤ ‖U.val (baseIndex n 1)‖ := by
    have hae : ∀ᵐ x ∂volume, ‖f x‖ ≤ ‖U.val (baseIndex n 1)‖ := by
      filter_upwards [heq, ae_norm_coordinate_le U (baseIndex n 1)] with x hx hb
      simpa only [hx] using hb
    have hdense := (volume : Measure (ℝ^n)).dense_of_ae hae
    intro x
    exact (isClosed_le hLip.continuous.norm continuous_const).closure_subset (hdense x)
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hLip.continuous
    ‖U.val (baseIndex n 1)‖ hbound, hLip, heq, ?_⟩
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hLip.continuous
    (norm_nonneg _) hbound

/-- The unique bounded continuous representative of a Banach-valued W¹,∞ class.
It is obtained from almost-everywhere convergence of uniformly Lipschitz mollifications. -/
def lipschitzRepresentative (U : W^{1,∞}(ℝ^n; F)) : ℝ^n →ᵇ F :=
  (exists_boundedContinuous_lipschitz_representative U).choose

/-- The endpoint representative agrees almost everywhere with the base coordinate. -/
theorem lipschitzRepresentative_ae (U : W^{1,∞}(ℝ^n; F)) :
    (lipschitzRepresentative U : ℝ^n → F) =ᵐ[volume]
      (U.val (baseIndex n 1) : ℝ^n → F) :=
  (exists_boundedContinuous_lipschitz_representative U).choose_spec.2.1

/-- The sum of the L∞ derivative-row norms is a Lipschitz constant. -/
theorem lipschitzWith_lipschitzRepresentative (U : W^{1,∞}(ℝ^n; F)) :
    LipschitzWith (∑ j : Fin n, ‖U.val (singleDerivIndex n j)‖₊)
      (lipschitzRepresentative U) :=
  (exists_boundedContinuous_lipschitz_representative U).choose_spec.1

/-- The uniform norm is exactly the base coordinate's essential supremum. -/
theorem norm_lipschitzRepresentative_eq (U : W^{1,∞}(ℝ^n; F)) :
    ‖lipschitzRepresentative U‖ = ‖U.val (baseIndex n 1)‖ := by
  apply le_antisymm (exists_boundedContinuous_lipschitz_representative U).choose_spec.2.2
  apply Lp.norm_top_le_of_ae_bound (norm_nonneg _)
  have heq : (lipschitzRepresentative U : ℝ^n → F) =ᵐ[domainMeasure n (⊤ : Opens ℝ^n)]
      (U.val (baseIndex n 1) : ℝ^n → F) := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      lipschitzRepresentative_ae U
  filter_upwards [heq] with x hx
  rw [← hx]
  exact (lipschitzRepresentative U).norm_coe_le_norm x

/-- The representative map is bounded by the unchanged Sobolev graph norm. -/
theorem norm_lipschitzRepresentative_le (U : W^{1,∞}(ℝ^n; F)) :
    ‖lipschitzRepresentative U‖ ≤ ‖U‖ := by
  rw [norm_lipschitzRepresentative_eq]
  exact norm_coordinate_le (baseIndex n 1) U

/-- A bound involving only the graph norm, with the dimension-zero constant still zero. -/
theorem lipschitzWith_lipschitzRepresentative_norm (U : W^{1,∞}(ℝ^n; F)) :
    LipschitzWith (n * ‖U‖₊) (lipschitzRepresentative U) := by
  apply (lipschitzWith_lipschitzRepresentative U).weaken
  calc
    ∑ j : Fin n, ‖U.val (singleDerivIndex n j)‖₊ ≤ ∑ _ : Fin n, ‖U‖₊ :=
      Finset.sum_le_sum fun j _ ↦ norm_coordinate_le (singleDerivIndex n j) U
    _ = n * ‖U‖₊ := by simp

/-- A continuous representative of the same class agrees everywhere with the endpoint
representative. In particular, classical continuous functions are preserved. -/
theorem lipschitzRepresentative_eq (U : W^{1,∞}(ℝ^n; F)) {f : ℝ^n → F}
    (hf : Continuous f) (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f) :
    (lipschitzRepresentative U : ℝ^n → F) = f :=
  Measure.eq_of_ae_eq ((lipschitzRepresentative_ae U).trans hbase)
    (lipschitzRepresentative U).continuous hf

end SobolevSpace.VectorValued
