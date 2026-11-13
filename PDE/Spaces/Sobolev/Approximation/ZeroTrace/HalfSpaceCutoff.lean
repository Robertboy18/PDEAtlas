/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.ZeroTrace.BoundedMultiplier
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TestFunctions
import PDE.Spaces.Sobolev.Boundary.Trace.HalfLine.ZeroTrace

/-!
# Bounded multiplication by the normal half-space cutoff

The cutoff `cutoffAway δ` has bounded first derivatives for each fixed
positive `δ`. Its derivative bound follows from the compactly supported
derivative of the one-dimensional smooth transition. Thus it acts continuously
on `W^{1,p}` even though it is not compactly supported in tangential directions.
-/

@[expose] public section

open PDE (coordinateLine iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.HalfSpace

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ} [Fact (0 < n)]

/-- The derivative is zero tangentially and is the rescaled transition derivative normally. -/
theorem partialDeriv_cutoffAway (δ : ℝ) (i : Fin n) (x : ℝ^n) :
    (∂[i] (cutoffAway (n := n) δ)) x =
      if i = PDE.Common.lastIndex (n := n) then
        (1 / δ) * deriv Real.smoothTransition
          ((x (PDE.Common.lastIndex (n := n)) - δ) / δ)
      else 0 := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine i x
    ((contDiff_cutoffAway δ).differentiable (by simp)).differentiableAt]
  split_ifs with hi
  · subst i
    have hinner := ((hasDerivAt_id (x (PDE.Common.lastIndex (n := n)))).sub_const δ).div_const δ
    have hsm : Differentiable ℝ Real.smoothTransition :=
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)
    have hc := (hsm _).hasDerivAt.comp _ hinner
    have heq : (cutoffAway (n := n) δ ∘ coordinateLine (PDE.Common.lastIndex (n := n)) x) =
        fun s ↦ Real.smoothTransition ((s - δ) / δ) := by
      funext s
      simp [cutoffAway, PDE.coordinateLine_apply_same]
    rw [heq]
    simpa only [Function.comp_def, id_eq, mul_comm] using hc.deriv
  · have heq : (cutoffAway (n := n) δ ∘ coordinateLine i x) =
        fun _ : ℝ ↦ Real.smoothTransition
          ((x (PDE.Common.lastIndex (n := n)) - δ) / δ) := by
      funext s
      simp [cutoffAway, coordinateLine, Ne.symm hi]
    rw [heq, deriv_const]

/-- The cutoff is essentially bounded on every measurable domain. -/
theorem cutoffAway_memLp_top (δ : ℝ) (Ω : Set (ℝ^n)) :
    MemLp (cutoffAway (n := n) δ) ∞ (domainMeasure n Ω) := by
  apply memLp_top_of_bound (contDiff_cutoffAway δ).continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, cutoffAway, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _

/-- Every coordinate derivative of a fixed normal cutoff is essentially bounded. -/
theorem partialDeriv_cutoffAway_memLp_top (δ : ℝ) (Ω : Set (ℝ^n)) (i : Fin n) :
    MemLp (iteratedPartialDeriv [i] (cutoffAway (n := n) δ)) ∞
      (domainMeasure n Ω) := by
  obtain ⟨D, hD0, hD⟩ := Trace.HalfLine.exists_smoothTransition_deriv_bound
  have hc : Continuous (iteratedPartialDeriv [i] (cutoffAway (n := n) δ)) :=
    (PDE.contDiff_top_iteratedPartialDeriv (contDiff_cutoffAway δ) [i]).continuous
  apply memLp_top_of_bound hc.aestronglyMeasurable (|1 / δ| * D)
  filter_upwards with x
  simp only [iteratedPartialDeriv, partialDeriv_cutoffAway]
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  · simpa only [norm_zero] using mul_nonneg (abs_nonneg (1 / δ)) hD0

/-- Multiplication by the normal cutoff as a bounded Sobolev operator. -/
def cutoffAwayCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] (δ : ℝ) (Ω : Set (ℝ^n)) :
    W^{1,p}(Ω) →L[ℝ] W^{1,p}(Ω) :=
  GraphSpace.boundedMultiplierCLM (cutoffAway_memLp_top δ Ω)
    (partialDeriv_cutoffAway_memLp_top δ Ω) (contDiff_cutoffAway δ)

/-- The normal cutoff multiplies the underlying Sobolev function pointwise. -/
theorem cutoffAwayCLM_base_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (δ : ℝ) (Ω : Set (ℝ^n)) (U : W^{1,p}(Ω)) :
    GraphSpace.baseRepresentative (cutoffAwayCLM δ Ω U)
      =ᵐ[domainMeasure n Ω] fun x ↦
        cutoffAway (n := n) δ x * GraphSpace.baseRepresentative U x :=
  GraphSpace.boundedMultiplierCLM_base_ae (cutoffAway_memLp_top δ Ω)
    (partialDeriv_cutoffAway_memLp_top δ Ω) (contDiff_cutoffAway δ) U

end SobolevSpace.HalfSpace
