/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation under locally uniform compact support

A common compact support and continuity of the actual time derivative give the
local domination needed to differentiate the integral. The values may lie in a
real normed space. The derivative vanishes outside the support by uniqueness of
the derivative of a locally zero function.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

namespace PDE

/-- A locally common compact support supplies domination for differentiating
a continuous family with a jointly continuous time derivative. -/
theorem hasDerivAt_integral_of_locally_uniform_compact_support
    {f D : ℝ → X → E} {I : Set ℝ} {K : Set X}
    (hI : IsOpen I) (hK : IsCompact K)
    (hf : ContinuousOn f.uncurry (I ×ˢ univ))
    (hD : ContinuousOn D.uncurry (I ×ˢ univ))
    (hd : ∀ t ∈ I, ∀ x, HasDerivAt (fun s ↦ f s x) (D t x) t)
    (hs : ∀ t ∈ I, ∀ x ∉ K, f t x = 0)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s ↦ ∫ x, f s x ∂μ) (∫ x, D t x ∂μ) t := by
  have hfc (s : ℝ) (hsI : s ∈ I) : Continuous (f s) :=
    continuousOn_univ.mp (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ ↦ ⟨hsI, mem_univ x⟩))
  obtain ⟨δ, hδ, hδI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds ht)
  let J := Ioo (t - δ / 2) (t + δ / 2)
  have hJI : Icc (t - δ / 2) (t + δ / 2) ⊆ I := by
    intro s hsI
    apply hδI
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
  have hJ : J ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hcompact := (isCompact_Icc (a := t - δ / 2) (b := t + δ / 2)).prod hK
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hD.mono (fun p hp ↦ ⟨hJI hp.1, mem_univ _⟩))
  let ν := μ.restrict K
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (hK.measure_lt_top (μ := μ)).ne
  have hderiv : HasDerivAt (fun s ↦ ∫ x, f s x ∂ν) (∫ x, D t x ∂ν) t := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := ν) (F := f) (F' := D) (bound := fun _ ↦ M) hJ ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [hI.mem_nhds ht] with s hsI
      exact (hfc s hsI).aestronglyMeasurable
    · exact (hfc t ht).continuousOn.integrableOn_compact hK
    · exact (hD.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ ↦ ⟨ht, mem_univ x⟩)).aestronglyMeasurable hK.measurableSet
    · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      intro s hsJ
      exact hM (s, x) ⟨⟨hsJ.1.le, hsJ.2.le⟩, hx⟩
    · exact integrable_const M
    · exact Eventually.of_forall fun x s hsJ ↦ hd s (hJI ⟨hsJ.1.le, hsJ.2.le⟩) x
  have hDzero (x : X) (hx : x ∉ K) : D t x = 0 := by
    have heq : (fun s ↦ f s x) =ᶠ[𝓝 t] fun _ ↦ (0 : E) := by
      filter_upwards [hI.mem_nhds ht] with s hsI using hs s hsI x hx
    exact (hd t ht x).unique ((hasDerivAt_const t 0).congr_of_eventuallyEq heq)
  have heqD : (∫ x, D t x ∂ν) = ∫ x, D t x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hDzero
  rw [heqD] at hderiv
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hsI
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs s hsI)).symm

end PDE
