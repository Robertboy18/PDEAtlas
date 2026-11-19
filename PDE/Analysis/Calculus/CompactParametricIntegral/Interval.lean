/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral.AlmostEverywhere

/-!
# Integrals with finite-time continuous closure data

Compact spatial closure and a compact parameter interval give a common integrable
bound. Differentiation uses actual derivatives only at spatial interior indices
and at interior times; values outside this finite cylinder are unrestricted.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {s : Set X} {a b : ℝ} {f D : ℝ → X → E}

namespace PDE

/-- Continuous closure values give a continuous integral on a finite time interval. -/
theorem continuousOn_setIntegral_of_compact_interval
    (hs : MeasurableSet s) (hK : IsCompact (closure s)) (hfinite : μ s ≠ ⊤)
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ closure s)) :
    ContinuousOn (fun t ↦ ∫ x in s, f t x ∂μ) (Icc a b) := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hfinite.lt_top⟩
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hf
  apply continuousOn_of_dominated
  · intro t ht
    exact (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨ht, hx⟩) |>.integrableOn_of_subset_isCompact hK hs subset_closure
        hfinite).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem hs] with x hx
    exact hB (t, x) ⟨ht, subset_closure hx⟩
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem hs] with x hx
    exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht ↦ ⟨ht, subset_closure hx⟩)

/-- Differentiate a finite-time integral from continuous closure jets.
No derivative at a spatial boundary point or a time endpoint is required. -/
theorem hasDerivAt_setIntegral_of_compact_interval
    (hs : MeasurableSet s) (hK : IsCompact (closure s)) (hfinite : μ s ≠ ⊤)
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ closure s))
    (hD : ContinuousOn D.uncurry (Icc a b ×ˢ closure s))
    (hd : ∀ x ∈ s, ∀ t ∈ Ioo a b, HasDerivAt (fun r ↦ f r x) (D t x) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r ↦ ∫ x in s, f r x ∂μ) (∫ x in s, D t x ∂μ) t := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hfinite.lt_top⟩
  have hint {g : ℝ → X → E}
      (hg : ContinuousOn g.uncurry (Icc a b ×ˢ closure s))
      {r : ℝ} (hr : r ∈ Icc a b) : IntegrableOn (g r) s μ :=
    (hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨hr, hx⟩)).integrableOn_of_subset_isCompact hK hs subset_closure hfinite
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hD
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioo.mem_nhds ht) ?_ (hint hf (Ioo_subset_Icc_self ht))
    (hint hD (Ioo_subset_Icc_self ht)).aestronglyMeasurable ?_ (integrable_const B) ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (hint hf (Ioo_subset_Icc_self hr)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs] with x hx r hr
    exact hB (r, x) ⟨Ioo_subset_Icc_self hr, subset_closure hx⟩
  · filter_upwards [ae_restrict_mem hs] with x hx r hr
    exact hd x hx r hr

end PDE
