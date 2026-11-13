/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.ClosedSlab
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Spaces.Sobolev.GraphSpace.Norms.EssentialSupremum
import PDE.FDeriv.Calculus

/-!
# Bounded spacetime fields as curves in W¹∞

A C² field on a closed time slab with bounded values and first two
differentials determines a Lipschitz curve in the W¹∞ graph.
Its weak spatial rows are the spatial derivatives of the field.
The construction uses only regularity within the slab, including at its
endpoints; outside the time interval the curve is assigned zero.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

namespace SobolevSpace.GraphSpace

open MeasureTheory Set PDE.Common
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} {a b : ℝ}

/-- Bounded C² spacetime coefficients give W¹∞ spatial slices with
a derived Lipschitz bound in time and a derived uniform graph-norm bound. -/
theorem exists_lipschitz_wkpSpace_top_timeSlices
    (hab : a < b) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiffOn ℝ 2 f {p | p 0 ∈ Icc a b}) (M : ℝ≥0)
    (hzero : ∀ p, p 0 ∈ Icc a b → ‖f p‖ ≤ M)
    (hone : ∀ p, p 0 ∈ Icc a b →
      ‖fderivWithin ℝ f {q | q 0 ∈ Icc a b} p‖ ≤ M)
    (htwo : ∀ p, p 0 ∈ Icc a b →
      ‖iteratedFDerivWithin ℝ 2 f {q | q 0 ∈ Icc a b} p‖ ≤ M) :
    ∃ A : ℝ → W^{1,∞}(ℝ^n),
      LipschitzOnWith M A (Icc a b) ∧
      (∀ t ∈ Icc a b, ‖A t‖ ≤ M) ∧
      (∀ t ∈ Icc a b, (wkpBaseCoordinateCLM (A t) : ℝ^n → ℝ) =ᵐ[volume]
        fun x ↦ f (timeSpaceCons t x)) ∧
      (∀ t ∈ Icc a b, ∀ i,
        (wkpCoordinateCLM (singleDerivIndex n i) (A t) : ℝ^n → ℝ) =ᵐ[volume]
          fun x ↦ fderivWithin ℝ f {p | p 0 ∈ Icc a b}
            (timeSpaceCons t x) (EuclideanSpace.single i.succ 1)) := by
  classical
  let r (t : ℝ) (α : DerivIndex n 1) :=
    iteratedPartialDeriv α.toList (fun x ↦ f (timeSpaceCons t x))
  have hfone : ContDiffOn ℝ 1 f {p | p 0 ∈ Icc a b} := hf.of_le (by norm_num)
  have hpartial (t : ℝ) (ht : t ∈ Icc a b) (i : Fin n) (x : ℝ^n) :
      (∂[i] (fun y ↦ f (timeSpaceCons t y))) x =
        fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)
          (EuclideanSpace.single i.succ 1) := by
    rw [partialDeriv, (hfone.hasFDerivAt_timeSlice ht x).fderiv]
    simp only [ContinuousLinearMap.comp_apply, embedWithTimeZeroCLM_single_one]
  have hrbound (t : ℝ) (ht : t ∈ Icc a b) (α : DerivIndex n 1) (x : ℝ^n) :
      ‖r t α x‖ ≤ M := by
    rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [r, baseIndex_toList, iteratedPartialDeriv] using
        hzero (timeSpaceCons t x) (by simpa using ht)
    · simp only [r, singleDerivIndex_toList, iteratedPartialDeriv, hpartial t ht i x]
      simpa only [PiLp.norm_single, norm_one, mul_one] using
        (fderivWithin ℝ f _ _).le_of_opNorm_le (hone _ (by simpa using ht))
          (EuclideanSpace.single i.succ (1 : ℝ))
  have hrcont (t : ℝ) (ht : t ∈ Icc a b) (α : DerivIndex n 1) :
      Continuous (r t α) := by
    rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [r, baseIndex_toList, iteratedPartialDeriv] using
        (hfone.contDiff_timeSlice ht).continuous
    · simp only [r, singleDerivIndex_toList, iteratedPartialDeriv]
      exact continuous_iff_continuousAt.mpr fun x ↦
        (PDE.contDiffAt_partialDeriv 0 (hfone.contDiff_timeSlice ht).contDiffAt i).continuousAt
  have hrmem (t : ℝ) (ht : t ∈ Icc a b) (α : DerivIndex n 1) :
      MemLp (r t α) ∞ (domainMeasure n univ) :=
    memLp_top_of_bound (hrcont t ht α).aestronglyMeasurable M
      (Filter.Eventually.of_forall (hrbound t ht α))
  let A (t : ℝ) : W^{1,∞}(ℝ^n) := if ht : t ∈ Icc a b then
    mkWkpSpaceOnOfContDiffMemLpFinite (fun x ↦ f (timeSpaceCons t x))
      (hfone.contDiff_timeSlice ht) (hrmem t ht) else 0
  have hrep (t : ℝ) (ht : t ∈ Icc a b) (α : DerivIndex n 1) :
      ((A t).val α : ℝ^n → ℝ) =ᵐ[domainMeasure n univ] r t α := by
    dsimp only [A]
    rw [dite_eq_left ht]
    exact mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
      (fun x ↦ f (timeSpaceCons t x)) (hfone.contDiff_timeSlice ht) (hrmem t ht) α
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · refine lipschitzOnWith_top_of_ae_rows A r hrep fun s hs t ht α ↦ .of_forall fun x ↦ ?_
    rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [r, baseIndex_toList, iteratedPartialDeriv, dist_eq_norm] using
        hfone.norm_timeSlice_sub_le hone hs ht x
    · simp only [r, singleDerivIndex_toList, iteratedPartialDeriv]
      rw [hpartial s hs i x, hpartial t ht i x, ← sub_apply]
      simpa only [PiLp.norm_single, norm_one, mul_one, dist_eq_norm] using
        (_ - _ : ℝ^(n + 1) →L[ℝ] ℝ).le_of_opNorm_le
          (hf.norm_fderivWithin_timeSlice_sub_le hab htwo hs ht x)
          (EuclideanSpace.single i.succ (1 : ℝ))
  · exact fun t ht ↦ norm_top_le_of_ae_rows _ M.coe_nonneg fun α ↦
      (hrep t ht α).mono fun x hx ↦ hx ▸ hrbound t ht α x
  · intro t ht
    simpa only [wkpBaseCoordinateCLM_apply, r, baseIndex_toList, iteratedPartialDeriv,
      domainMeasure, Measure.restrict_univ] using hrep t ht (baseIndex n 1)
  · intro t ht i
    simpa only [wkpCoordinateCLM_apply, r, singleDerivIndex_toList, iteratedPartialDeriv,
      hpartial t ht, domainMeasure, Measure.restrict_univ] using
        hrep t ht (singleDerivIndex n i)

end SobolevSpace.GraphSpace
