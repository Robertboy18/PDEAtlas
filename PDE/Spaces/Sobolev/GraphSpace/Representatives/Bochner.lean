/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative

/-!
# Joint representatives of Bochner Sobolev curves

All weak coordinates of a countable family of Bochner Hᵏ curves admit jointly
measurable L² representatives. Countable intersection gives one exceptional
set for every component and derivative. The section representatives retain
the distributional derivatives of the Sobolev graph.

The parameter measure is arbitrary, and the spatial set need not be bounded.
No joint measurability of canonical Lp evaluation is asserted or needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
  {n k : ℕ} {Ω : Set ℝ^n}

/-- A countable family of Bochner Sobolev curves has joint L² representatives
of all weak coordinates, retaining the sectionwise distributional identities. -/
theorem exists_joint_weakCoordinates
    (U : ι → Lp (W^{k,2}(Ω)) 2 μ) :
    ∃ r : ι → DerivIndex n k → α × ℝ^n → ℝ,
      (∀ i a, StronglyMeasurable (r i a) ∧
        MemLp (r i a) 2 (μ.prod (domainMeasure n Ω))) ∧
      (∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ i a,
        r i a (t, x) = wkpCoordinateCLM a (U i t) x) ∧
      (∀ᵐ t ∂μ, ∀ i a, HasWeakDerivativeOn Ω a.toList
        (fun x ↦ r i (baseIndex n k) (t, x)) (fun x ↦ r i a (t, x))) := by
  have h (i : ι) (a : DerivIndex n k) :=
    ((wkpCoordinateCLM a).comp_memLp (U i)).exists_jointRepresentative
  choose r hrmeas hrLp hr using h
  have hrep : ∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ i a,
      r i a (t, x) = wkpCoordinateCLM a (U i t) x := by
    filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hr i)] with t ht
    exact ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (ht i)
  refine ⟨r, fun i a ↦ ⟨hrmeas i a, hrLp i a⟩, hrep, ?_⟩
  filter_upwards [hrep] with t ht
  intro i a
  apply ((U i t).property a).congr_ae
  · exact ht.mono fun x hx ↦ (hx i (baseIndex n k)).symm
  · exact ht.mono fun x hx ↦ (hx i a).symm

end SobolevSpace.GraphSpace
