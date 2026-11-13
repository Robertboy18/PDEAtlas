/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import PDE.Analysis.Topology.CompactFamilyBound

/-!
# Differentiating a compactly indexed integral

For a family `f x t`, differentiability in `x` and joint continuity of its
derivative suffice to differentiate the integral over a compact index space.
Compactness of the index space bounds the derivative family locally in `x`.
This supplies Mathlib's integrable bound even for infinite-dimensional parameters.

The index need not have a vector space structure: a compact time interval with
its restricted measure is one example. No differentiability in that index is
required, and the values may lie in a Banach space.
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

namespace PDE

/-- A continuous family remains continuous after integration over a compact
index space. Local compactness of the parameter space is unnecessary. -/
theorem continuous_integral_of_compact
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {g : X → T → F} (hg : Continuous g.uncurry) :
    Continuous (fun x ↦ ∫ t, g x t ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨U, hU, B, _, hB⟩ :=
    hg.continuousOn.exists_bound_nhds_of_isCompact isOpen_univ isCompact_univ (mem_univ x)
  apply continuousAt_of_dominated
  · exact Eventually.of_forall fun y ↦
      (hg.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
  · filter_upwards [hU] with y hy
    exact Eventually.of_forall fun t ↦ hB y hy t (mem_univ _)
  · exact integrable_const B
  · exact Eventually.of_forall fun t ↦
      (hg.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- A continuous derivative extension on a compact index space suffices when it is
the actual parameter derivative almost everywhere for the integrating measure. -/
theorem hasFDerivAt_integral_of_compact_ae
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ᵐ t ∂μ, ∀ x, HasFDerivAt (fun y ↦ f y t) (D x t) x) (x : E) :
    HasFDerivAt (fun y ↦ ∫ t, f y t ∂μ) (∫ t, D x t ∂μ) x := by
  obtain ⟨U, hU, B, _, hB⟩ :=
    hD.continuousOn.exists_bound_nhds_of_isCompact isOpen_univ isCompact_univ (mem_univ x)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    hU
  · exact Eventually.of_forall fun y ↦
      (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
  · have hc : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
  · exact Eventually.of_forall fun t y hy ↦ hB y hy t (mem_univ _)
  · exact integrable_const B
  · exact hd.mono fun t ht y _ ↦ ht y

/-- A jointly continuous derivative can be integrated over a compact index space.
The local domination comes from compactness and finiteness of the measure. -/
theorem hasFDerivAt_integral_of_compact
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ x t, HasFDerivAt (fun y ↦ f y t) (D x t) x) (x : E) :
    HasFDerivAt (fun y ↦ ∫ t, f y t ∂μ) (∫ t, D x t ∂μ) x := by
  exact hasFDerivAt_integral_of_compact_ae hf hD
    (Eventually.of_forall fun t y ↦ hd y t) x

/-- Integrating a family with a jointly continuous spatial derivative preserves
`C¹` regularity. The index variable only needs continuity. -/
theorem contDiff_one_integral_of_compact
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ x t, HasFDerivAt (fun y ↦ f y t) (D x t) x) :
    ContDiff ℝ 1 (fun x ↦ ∫ t, f x t ∂μ) := by
  have hi := hasFDerivAt_integral_of_compact (μ := μ) hf hD hd
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun x ↦ (hi x).differentiableAt, ?_⟩
  have hc : Continuous (fun x ↦ ∫ t, D x t ∂μ) :=
    continuous_integral_of_compact hD
  simpa only [funext fun x ↦ (hi x).fderiv] using hc

end PDE
