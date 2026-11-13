/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakTimeTransport
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Hilbert
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Bochner evolution of the weak second derivative

Weak continuity supplies scalar measurability, and separability of L² supplies
Bochner measurability. A bound on a compact time interval then gives Bochner L².
The highest velocity derivative is the concrete real Hilbert transform of the
second vorticity derivative, so its choice and measurability are also fixed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped ENNReal Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A bounded weakly continuous Hilbert-space curve is Bochner L² on a
finite interval. -/
theorem memLp_Ioc_of_weaklyContinuous_of_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {r : ℝ → E} {a b B : ℝ}
    (hr : ∀ ℓ : E →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (r t)) (Icc a b))
    (hbound : ∀ t ∈ Icc a b, ‖r t‖ ≤ B) :
    MemLp r 2 (volume.restrict (Ioc a b)) := by
  have hm : AEStronglyMeasurable r (volume.restrict (Ioc a b)) := by
    apply aestronglyMeasurable_of_forall_inner
    intro v
    exact ((hr (innerSL ℝ v)).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  exact MemLp.of_bound hm B
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hbound t (Ioc_subset_Icc_self ht))

end DeGregorio.Iteration

namespace DeGregorio

/-- On a locally H²-bounded normalized interval, the equation gives a Bochner L² second
derivative and its Hilbert-transform velocity derivative on every closed interior slab.
Its weak evolution against compact `C²` tests follows from the PDE. -/
theorem IsClassicalRescaledSolutionOn.exists_bochner_secondDerivative_evolution
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
    ∃ r : ℝ → Lp ℝ 2 (volume : Measure ℝ),
      (∀ t ∈ Ioo a T, ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t)) ∧
      (∀ ℓ : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] ℝ,
        ContinuousOn (fun t ↦ ℓ (r t)) (Ioo a T)) ∧
      (∀ c d : ℝ, Icc c d ⊆ Ioo a T →
        MemLp r 2 (volume.restrict (Ioc c d)) ∧
        MemLp (fun t ↦ realHilbertTransformL2 (r t)) 2 (volume.restrict (Ioc c d))) ∧
      ∀ t ∈ Ioo a T, ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        HasDerivAt (fun τ ↦ ∫ x, r τ x * ψ x)
          ((∫ x, (ρ t * x + fields.velocity x t) * r t x * deriv ψ x) +
            ∫ x, (realHilbertTransformL2 (r t) x * fields.vorticity x t +
              deriv (deriv (fun y ↦ fields.velocity y t)) x *
                deriv (fun y ↦ fields.vorticity y t) x) * ψ x) t := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℝ 2 (volume : Measure ℝ)) :=
    Lp.SecondCountableTopology
  obtain ⟨r, hr, hc, he⟩ :=
    hsol.exists_weak_secondDerivative_evolution hR hK hbound hrep hzero hnormalized
  refine ⟨r, hr, hc, ?_, ?_⟩
  · intro c d hcd
    have hmem : MemLp r 2 (volume.restrict (Ioc c d)) :=
      Iteration.memLp_Ioc_of_weaklyContinuous_of_bound
      (fun ℓ ↦ (hc ℓ).mono hcd) (fun t ht ↦ (hr t (hcd ht)).1)
    exact ⟨hmem, hmem.continuousLinearMap_comp realHilbertTransformL2⟩
  · intro t ht ψ hψ hψc
    obtain ⟨s, hrs, htest⟩ := he t ht
    apply (htest ψ hψ hψc).congr_deriv
    congr 1
    apply integral_congr_ae
    filter_upwards [hrs.ae_eq_right (isHilbertPair_realHilbertTransformL2 (r t))]
      with x hx
    rw [hx]

end DeGregorio
