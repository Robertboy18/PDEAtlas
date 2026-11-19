/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakJet
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.RescaledTraceBounds

/-!
# Weak continuity of the H² trajectory and its highest derivative

A continuous L² base trajectory in a bounded H² ball determines a unique
weakly continuous H² graph. Its highest derivative consequently has weak L²
continuity.

For the normalized equation, the PDE supplies L² base continuity through
the time-derivative majorant. Thus the weak continuity needed for transport
energy traces is derived from local supported H² control.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A continuous base curve in a bounded H² ball lifts to a weakly
continuous H² graph. The graph is determined by its base coordinate. -/
theorem exists_weaklyContinuous_h2_graph
    {T : Type*} [TopologicalSpace T] {F : T → DerivLp 1 2 univ} {B : NNReal}
    (hF : Continuous F) (hbound : ∀ t, F t ∈ hkBaseBall 1 2 univ B) :
    ∃ W : T → W^{2,2}(ℝ^1),
      (∀ t, ‖W t‖ ≤ B ∧ wkpBaseCoordinateCLM (W t) = F t) ∧
      Continuous (fun t ↦ toWeakSpace ℝ (W^{2,2}(ℝ^1)) (W t)) := by
  have hex (t : T) : ∃ W : W^{2,2}(ℝ^1),
      ‖W‖ ≤ B ∧ wkpBaseCoordinateCLM W = F t := hbound t
  choose W hWnorm hWbase using hex
  refine ⟨W, fun t ↦ ⟨hWnorm t, hWbase t⟩, ?_⟩
  have hb : Bornology.IsBounded (range W) :=
    isBounded_iff_forall_norm_le.mpr ⟨B, by
      rintro _ ⟨t, rfl⟩
      exact hWnorm t⟩
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_weak_hk_of_base isOpen_univ W (W t) hb
  simpa only [hWbase, Function.comp_def, toWeakSpaceCLM_eq_toWeakSpace] using
    ((toWeakSpaceCLM ℝ (DerivLp 1 2 univ)).continuous.comp hF).tendsto t

/-- The weak second derivative of a bounded H² base curve has weak L²
continuity. It is constructed from the graph derivative coordinate, with
the same norm bound. -/
theorem exists_weaklyContinuous_secondDerivative
    {T : Type*} [TopologicalSpace T] {F : T → DerivLp 1 2 univ} {B : NNReal}
    (hF : Continuous F) (hbound : ∀ t, F t ∈ hkBaseBall 1 2 univ B)
    {w : T → ℝ → ℝ} (hw : ∀ t, Continuous (w t))
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] w t) :
    ∃ r : T → Lp ℝ 2 (volume : Measure ℝ),
      (∀ t, ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (w t) (deriv (w t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (w t)) (r t)) ∧
      ∀ ℓ : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] ℝ, Continuous (fun t ↦ ℓ (r t)) := by
  obtain ⟨W, hW, hWcont⟩ := exists_weaklyContinuous_h2_graph hF hbound
  let D : W^{2,2}(ℝ^1) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    (realLineCoordinateCLM (singleDerivIndex 1 0)).comp (partialDerivCLM 0)
  refine ⟨fun t ↦ D (W t), fun t ↦ ?_, fun ℓ ↦ ?_⟩
  · have hrepW : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (W t)) : ℝ → ℝ)
        =ᵐ[volume] w t := (hW t).2 ▸ hrep t
    have heq : realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) =
        w t :=
      (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) (hw t)).mp
        ((realLineRepresentative_lowerOrder_ae (W t)).symm.trans hrepW)
    have hq : realLineRepresentative (∂[0] (W t)) = deriv (w t) := by
      rw [← heq]
      exact (deriv_realLineRepresentative_lowerOrder (W t)).symm
    refine ⟨(norm_realLineCoordinateCLM_le _ _).trans
      ((norm_partialDeriv_le 0 (W t)).trans (hW t).1), ?_, ?_⟩
    · exact (exists_weak_secondDerivative_of_h2 (W t) (hw t) hrepW).choose_spec.2.2.1
    · exact hq ▸ hasWeakTimeDerivativeOn_realLineRepresentative (∂[0] (W t))
  · rw [continuous_iff_continuousAt]
    intro t
    exact WeakCompactness.tendsto_evaluation (hWcont.tendsto t) (ℓ.comp D)

end DeGregorio.Iteration

namespace DeGregorio

/-- On a normalized rescaled trajectory, local uniform supported H² control
constructs its weakly continuous second derivative. The PDE supplies the continuity
of the L² base. -/
theorem IsClassicalRescaledSolutionOn.exists_weaklyContinuous_secondDerivative
    {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R) :
    ∃ r : Ioo a T → Lp ℝ 2 (volume : Measure ℝ),
      (∀ t, ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t)) ∧
      ∀ ℓ : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] ℝ, Continuous (fun t ↦ ℓ (r t)) := by
  obtain ⟨C, hC⟩ :=
    hsol.exists_lipschitzOnWith_base_of_supported_h2 hR hK hbound hrep hzero hnormalized
  exact Iteration.exists_weaklyContinuous_secondDerivative
    (continuousOn_iff_continuous_domRestrict.mp hC.continuousOn)
    (fun t : Ioo a T ↦ (hbound t t.property).1)
    (fun t : Ioo a T ↦ continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt t.property).continuousAt)
    (fun t : Ioo a T ↦ hrep t t.property)

end DeGregorio
