/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTraceNormalized

/-!
# Closing a half-open time slab

Compact uniform terminal convergence fills a missing time slice and gives joint
continuity on the closed slab. This also applies to the spatial derivative traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio.Iteration

/-- Filling a left terminal limit closes a continuous half-open curve. -/
theorem continuousOn_update_terminal {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {v : E} {a T : ℝ} (haT : a < T)
    (hf : ContinuousOn f (Ico a T)) (hlim : Tendsto f (𝓝[<] T) (𝓝 v)) :
    ContinuousOn (Function.update f T v) (Icc a T) := by
  classical
  intro t ht
  by_cases heq : t = T
  · subst t
    rwa [continuousWithinAt_update_same, Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT haT]
  · have hlt : t < T := lt_of_le_of_ne ht.2 heq
    have hmem : Ico a T ∈ 𝓝[Icc a T] t := by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hlt)] with s hs hsT
      exact ⟨hs.1, hsT⟩
    apply ((hf t ⟨ht.1, hlt⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
    · filter_upwards [hmem] with s hs
      exact Function.update_of_ne hs.2.ne _ _
    · exact Function.update_of_ne heq _ _

/-- Replace just the missing terminal spatial slice. -/
def closeTimeSlice (T : ℝ) (w : ℝ → ℝ → ℝ) (v : ℝ → ℝ) (x t : ℝ) : ℝ :=
  Function.update (fun s ↦ w x s) T (v x) t

/-- The closed slice is the prescribed terminal trace. -/
@[simp] theorem closeTimeSlice_terminal (T : ℝ) (w : ℝ → ℝ → ℝ)
    (v : ℝ → ℝ) (x : ℝ) : closeTimeSlice T w v x T = v x := by
  simp [closeTimeSlice]

/-- All other slices retain their original values. -/
theorem closeTimeSlice_of_ne {T t : ℝ} (w : ℝ → ℝ → ℝ)
    (v : ℝ → ℝ) (x : ℝ) (ht : t ≠ T) :
    closeTimeSlice T w v x t = w x t :=
  Function.update_of_ne ht _ _

/-- Spatial differentiation commutes with filling the terminal slice. -/
theorem deriv_closeTimeSlice (T : ℝ) (w : ℝ → ℝ → ℝ)
    (v : ℝ → ℝ) (t : ℝ) :
    deriv (fun x ↦ closeTimeSlice T w v x t) =
      fun x ↦ closeTimeSlice T (fun y s ↦ deriv (fun z ↦ w z s) y) (deriv v) x t := by
  by_cases ht : t = T
  · subst t
    simp
  · simp only [closeTimeSlice_of_ne _ _ _ ht]

/-- If `w(·, t) → v` uniformly on compact sets as `t → T⁻` and `v` is continuous, then
filling the terminal slice with `v` gives a field jointly continuous on `ℝ × [a, T]`. -/
theorem continuous_closeTimeSlice {w : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {a T : ℝ}
    (haT : a < T)
    (hw : Continuous (fun p : ℝ × Ico a T ↦ w p.1 p.2))
    (hv : Continuous v)
    (hlim : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun t x ↦ w x t) v (𝓝[<] T) K) :
    Continuous (fun p : ℝ × Icc a T ↦ closeTimeSlice T w v p.1 p.2) := by
  classical
  have hs (t : Ico a T) : Continuous (fun x ↦ w x t) :=
    hw.comp (continuous_id.prodMk continuous_const)
  let f : ℝ → C(ℝ, ℝ) := fun t ↦
    if ht : t ∈ Ico a T then ⟨fun x ↦ w x t, hs ⟨t, ht⟩⟩ else ⟨v, hv⟩
  have hf : ContinuousOn f (Ico a T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    simpa only [Set.domRestrict, f, dite_eq_left (Subtype.prop _),
      ContinuousMap.coe_mk, Function.uncurry_def, Function.comp_def, Prod.swap] using
      hw.comp continuous_swap
  have hflim : Tendsto f (𝓝[<] T) (𝓝 (⟨v, hv⟩ : C(ℝ, ℝ))) := by
    apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
    intro K hK
    apply (hlim K hK).congr
    filter_upwards [Ioo_mem_nhdsLT haT] with t ht
    intro x _
    simp only [f, dite_eq_left (Ioo_subset_Ico_self ht), ContinuousMap.coe_mk]
  have hc := continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_update_terminal haT hf hflim)
  apply (continuous_eval.comp ((hc.comp continuous_snd).prodMk continuous_fst)).congr
  intro p
  by_cases ht : (p.2 : ℝ) = T
  · simp [ht]
  · have hi : (p.2 : ℝ) ∈ Ico a T := ⟨p.2.property.1, lt_of_le_of_ne p.2.property.2 ht⟩
    simp only [Function.comp_apply, Set.domRestrict, Function.update_of_ne ht, f,
      dite_eq_left hi,
      ContinuousMap.coe_mk, closeTimeSlice_of_ne _ _ _ ht]

/-- An L²-continuous bounded H² graph has jointly continuous principal-value
velocity and velocity derivative. -/
theorem continuous_hilbertPV_and_velocity_of_h2_base
    {X : Type*} [TopologicalSpace X] {B : NNReal}
    {f : X → DerivLp 1 2 univ} (hf : Continuous f)
    (hbound : ∀ t, f t ∈ hkBaseBall 1 2 univ B)
    {w : X → ℝ → ℝ} (hw : ∀ t, ContDiff ℝ 1 (w t))
    (hs : ∀ t, HasCompactSupport (w t))
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (f t) : ℝ → ℝ) =ᵐ[volume] w t) :
    Continuous (fun p : ℝ × X ↦ hilbertPV (w p.2) p.1) ∧
      Continuous (fun p : ℝ × X ↦ hilbertPVVelocity (w p.2) p.1) := by
  have hh (t : X) := continuous_hilbertPV_of_contDiff_one_compactSupport (hw t) (hs t)
  have hu (t : X) : Continuous (hilbertPVVelocity (w t)) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport (hw t) (hs t) x).continuousAt
  have hhC : Continuous (fun t : X ↦ (⟨hilbertPV (w t), hh t⟩ : C(ℝ, ℝ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr fun K hK ↦
      tendstoUniformlyOn_hilbertPV_of_h2_base hbound (hbound t) (hf.tendsto t)
        hw hs (hw t) (hs t) hrep (hrep t) hK
  have huC : Continuous (fun t : X ↦ (⟨hilbertPVVelocity (w t), hu t⟩ : C(ℝ, ℝ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
    intro K hK
    have heq (s : X) := hilbertPVVelocity_eq_l2Primitive_of_ae (hw s) (hs s) (hrep s)
    simpa only [ContinuousMap.coe_mk, heq] using
      tendstoUniformlyOn_normalized_hilbert_velocity (hf.tendsto t) hK
  exact ⟨continuous_eval.comp ((hhC.comp continuous_snd).prodMk continuous_fst),
    continuous_eval.comp ((huC.comp continuous_snd).prodMk continuous_fst)⟩

end DeGregorio.Iteration
