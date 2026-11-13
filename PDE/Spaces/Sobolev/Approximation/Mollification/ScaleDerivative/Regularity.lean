/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Joint regularity of scaled mollification

On each bounded interval of positive scales, the scaled kernels have a common compact
support. Parameter-dependent convolution therefore makes a locally integrable function
with values in a real normed space smooth jointly in scale and position. No common support
over all positive scales is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Convolution Topology

namespace SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The scaled kernel is smooth jointly in its positive scale and position. -/
theorem contDiffOn_scaled (μ : Mollifier n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ^n ↦ scaled μ q.1 q.2)
      (Ioi 0 ×ˢ univ) := by
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ^n ↦ q.1⁻¹)
      (Ioi 0 ×ˢ univ) :=
    contDiff_fst.contDiffOn.inv fun q hq ↦ ne_of_gt hq.1
  apply ((hi.pow n).mul (μ.smooth.comp_contDiffOn (hi.smul contDiff_snd.contDiffOn))).congr
  intro q hq
  rw [scaled_of_pos μ hq.1]
  rfl

/-- Bounded positive scales have a common compact kernel support. -/
theorem exists_compact_scaled_support (μ : Mollifier n) (T : ℝ) :
    ∃ k : Set (ℝ^n), IsCompact k ∧
      ∀ t y, t ∈ Ioo 0 T → y ∉ k → scaled μ t y = 0 := by
  obtain ⟨R₀, hR₀⟩ := μ.compactSupport.isBounded.subset_closedBall (0 : ℝ^n)
  let R := max R₀ 0
  have hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨Metric.closedBall 0 (T * R), isCompact_closedBall _ _, ?_⟩
  intro t y ht hy
  apply Function.notMem_support.mp
  intro hys
  apply hy
  exact (Metric.closedBall_subset_closedBall
    (mul_le_mul_of_nonneg_right ht.2.le (le_max_right _ _)))
    (support_scaled_subset_closedBall μ ht.1 hR hys)

/-- Mollification of locally Bochner integrable data is smooth jointly at every positive scale. -/
theorem contDiffOn_mollifyVector_scale (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ^n ↦ mollifyVector μ q.1 g q.2) (Ioi 0 ×ˢ univ) := by
  intro q hq
  obtain ⟨k, hk, hks⟩ := exists_compact_scaled_support μ (q.1 + 1)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun r : ℝ × ℝ^n ↦ mollifyVector μ r.1 g r.2)
      (Ioo 0 (q.1 + 1) ×ˢ univ) :=
    contDiffOn_convolution_left_with_param (ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure (ℝ^n)))
      isOpen_Ioo hk hks hg
      ((contDiffOn_scaled μ).mono (prod_mono Ioo_subset_Ioi_self Subset.rfl))
  exact (hs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
    ⟨⟨hq.1, lt_add_one _⟩, mem_univ _⟩)).contDiffWithinAt

end SobolevSpace.Approximation
