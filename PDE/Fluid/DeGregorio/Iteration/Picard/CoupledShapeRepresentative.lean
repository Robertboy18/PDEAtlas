/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Convergence
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative.Trace

/-!
# The coupled output and its closed Sobolev traces

The fixed point identifies the Hilbert input with the same continuous vorticity
representative, including both endpoints. Restricting its constructed H² graphs
gives the bounded H¹ family and L² continuity used by the shape and limit theorems.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}

/-- The fixed point closes the spectral Hilbert relation at every
closed-slab time, including the endpoint traces. -/
theorem IsHkFrozenOutput.hilbert_pair_self_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsHilbertPair (fun x ↦ w x t) (fun x ↦ c x t) := by
  have hp := h.hilbert_pair t
  rw [projIcc_of_mem hT ht] at hp
  exact hp.congr_ae (h.representative ⟨t, ht⟩) EventuallyEq.rfl

/-- The constructed output has spatial C¹ regularity up to both endpoint times. -/
theorem IsHkFrozenOutput.contDiff_vorticity_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ 1 (fun x ↦ w x t) :=
  (contDiff_and_bounds_of_hkBaseBall (F ⟨t, ht⟩).property.1
    (h.continuous.comp (continuous_id.prodMk continuous_const))
    (h.representative ⟨t, ht⟩)).1

/-- The support enclosure in the construction gives a single compact set for
all slices, including the endpoint times. -/
theorem IsHkFrozenOutput.tsupport_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    tsupport (fun x ↦ w x t) ⊆ Icc (-R) R := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (h.support x t ht (lt_of_not_ge fun habs ↦ hnot (abs_le.mp habs)))

/-- At the fixed point the continuous coefficient is the principal-value
Hilbert transform of the output itself, pointwise on the whole closed slab. -/
theorem IsHkFrozenOutput.coefficient_eq_hilbertPV_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun x ↦ c x t) = hilbertPV (fun x ↦ w x t) :=
  (h.hilbert_pair_self_on_Icc ht).eq_hilbertPV
    (h.coefficient_continuous.comp (continuous_id.prodMk continuous_const))
    (h.contDiff_vorticity_on_Icc ht)
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (h.tsupport_on_Icc ht))

/-- The constructed normalized velocity is the principal-value
velocity of its own output representative, including both endpoint times. -/
theorem IsHkFrozenOutput.velocity_eq_hilbertPVVelocity_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun x ↦ hkCurveHilbertVelocity hT F x t) = hilbertPVVelocity (fun x ↦ w x t) := by
  have hp := h.hilbert_pair t
  have hae := (isHilbertPair_realHilbertTransformL2
    (oneDimensionalPushforwardL2 (F (projIcc 0 T hT t)).val)).ae_eq_right hp
  funext x
  unfold hkCurveHilbertVelocity l2Primitive hilbertPVVelocity
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hae] with y hy _
  exact hy.trans (congrFun (h.coefficient_eq_hilbertPV_on_Icc ht) y)

/-- The constructed H² base curve admits bounded H¹ graphs with the given
pointwise representative and a continuous L² base coordinate. -/
theorem IsHkFrozenOutput.exists_h1_trace
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) :
    ∃ g : Icc (0 : ℝ) T → W^{1,2}((Set.univ : Set (ℝ^1))),
      (∀ t, ‖g t‖ ≤ B) ∧
      (∀ t, realLineRepresentative (g t) = fun x ↦ w x t) ∧
      (∀ t, realLineCoordinateCLM (baseIndex 1 1) (g t) =
        oneDimensionalPushforwardL2 (F t).val) ∧
      Continuous (fun t ↦ realLineCoordinateCLM (baseIndex 1 1) (g t)) := by
  have hex (t : Icc (0 : ℝ) T) := (F t).property.1
  choose W hW hbase using hex
  let g (t : Icc (0 : ℝ) T) := lowerOrderCLM (by decide : 1 ≤ 2) (W t)
  have hgbase (t : Icc (0 : ℝ) T) :
      realLineCoordinateCLM (baseIndex 1 1) (g t) =
        oneDimensionalPushforwardL2 (F t).val := by
    apply congrArg oneDimensionalPushforwardL2
    change (g t : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) = (F t).val
    simpa only [g, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
      wkpBaseCoordinateCLM_apply] using hbase t
  refine ⟨g, fun t ↦ (norm_lowerOrderCLM_apply_le _ (W t)).trans (hW t),
    ?_, hgbase, ?_⟩
  · intro t
    apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative (g t))
      (h.continuous.comp (continuous_id.prodMk continuous_const))).mp
    have ha := realLineCoordinate_ae_representative (g t)
    rw [hgbase t] at ha
    exact ha.symm.trans (h.representative t)
  · simp_rw [hgbase]
    exact oneDimensionalPushforwardL2.continuous.comp
      (continuous_subtype_val.comp F.continuous)

/-- Substituting the identified velocity gives the physical classical equation
with the principal-value velocity of the output itself. -/
theorem IsHkFrozenOutput.isClassicalSolutionOn_hilbertPVVelocity
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) :
    IsClassicalSolutionOn 1
      ⟨w, fun x t ↦ hilbertPVVelocity (fun y ↦ w y t) x⟩ (Ioo 0 T) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x t ht
    exact h.isClassicalSolutionOn.regularity.vorticity_differentiableAt ht
  · intro x t ht
    change DifferentiableAt ℝ (hilbertPVVelocity (fun y ↦ w y t)) x
    rw [← h.velocity_eq_hilbertPVVelocity_on_Icc (Ioo_subset_Icc_self ht)]
    exact (h.velocity_derivative x t).differentiableAt
  · intro x t ht
    change deriv (w x) t + 1 * hilbertPVVelocity (fun y ↦ w y t) x *
      deriv (fun y ↦ w y t) x =
        deriv (hilbertPVVelocity (fun y ↦ w y t)) x * w x t
    rw [← h.velocity_eq_hilbertPVVelocity_on_Icc (Ioo_subset_Icc_self ht)]
    exact h.isClassicalSolutionOn.transport ht
  · intro t ht
    change IsHilbertPair (fun x ↦ w x t) (deriv (hilbertPVVelocity (fun y ↦ w y t)))
    rw [← h.velocity_eq_hilbertPVVelocity_on_Icc (Ioo_subset_Icc_self ht)]
    exact h.isClassicalSolutionOn.biotSavart ht

end DeGregorio.Iteration
