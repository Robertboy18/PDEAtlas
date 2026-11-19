/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral
import PDE.Analysis.Topology.CompactFamilyBound

/-!
# Almost-everywhere differentiation of a compactly indexed integral

Continuous extensions of a derivative family can be used at boundary indices even when
the actual parameter derivative is only known at almost every index. Compactness supplies
the local dominating bound; no derivative at an exceptional boundary index is required.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

variable {T E F : Type*} [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace T] [OpensMeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure T} [IsFiniteMeasure μ]
  {f : E → T → F} {D : E → T → E →L[ℝ] F}

section SetIntegral

variable {X G H : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {ν : Measure X} {s : Set X}
  {g : G → X → H} {g' : G → X → G →L[ℝ] H}

namespace PDE

/-- Continuous closure data differentiate a parameterized integral on a relatively
compact measurable domain. Actual derivatives are needed only in the domain. -/
theorem hasFDerivAt_setIntegral_of_compact_closure
    (hs : MeasurableSet s) (hcompact : IsCompact (closure s)) (hfinite : ν s ≠ ⊤)
    (hg : ContinuousOn g.uncurry (univ ×ˢ closure s))
    (hg' : ContinuousOn g'.uncurry (univ ×ˢ closure s))
    (hd : ∀ t ∈ s, ∀ x, HasFDerivAt (fun y ↦ g y t) (g' x t) x) (x : G) :
    HasFDerivAt (fun y ↦ ∫ t in s, g y t ∂ν) (∫ t in s, g' x t ∂ν) x := by
  let : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hfinite.lt_top⟩
  have hslice (y : G) : ContinuousOn (g y) (closure s) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht ↦ ⟨mem_univ _, ht⟩)
  have hslice' (y : G) : ContinuousOn (g' y) (closure s) :=
    hg'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht ↦ ⟨mem_univ _, ht⟩)
  obtain ⟨U, hU, B, _, hB⟩ := hg'.exists_bound_nhds_of_isCompact isOpen_univ hcompact (mem_univ x)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    hU
  · exact Eventually.of_forall fun y ↦
      ((hslice y).integrableOn_of_subset_isCompact hcompact hs subset_closure
        hfinite).aestronglyMeasurable
  · exact (hslice x).integrableOn_of_subset_isCompact hcompact hs subset_closure hfinite
  · exact ((hslice' x).integrableOn_of_subset_isCompact hcompact hs subset_closure
      hfinite).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs] with t ht y hy
    exact hB y hy t (subset_closure ht)
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem hs] with t ht y _
    exact hd t ht y

end PDE

end SetIntegral
