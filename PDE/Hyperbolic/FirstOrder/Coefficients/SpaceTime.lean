/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.SpaceTime
import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.TensorTesting

/-!
# Spacetime matrix coefficients

Entrywise C² regularity and bounds on a closed spacetime slab produce the
W¹,∞ coefficient curves used by the transport and diffusion operators.
The values and weak spatial derivatives are identified with the pointwise fields.
Pointwise matrix symmetry therefore becomes equality of the L∞
coefficient classes.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.FirstOrder

open MeasureTheory Set PDE.Common
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal

variable {n m : ℕ} {a b : ℝ}

/-- Closed-slab continuity gives joint measurability of the coefficient
field for the product time-space measure, including the terminal time. -/
theorem aestronglyMeasurable_matrix_timeSpace (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j p q, ContinuousOn (fun y ↦ B j y p q) {y | y 0 ∈ Icc a b}) :
    ∀ j p q, AEStronglyMeasurable (fun z : ℝ × ℝ^n ↦ B j (timeSpaceCons z.1 z.2) p q)
      ((volume.restrict (Ioc a b)).prod volume) := by
  intro j p q
  have hs : MeasurableSet {y : SpaceTime n | y 0 ∈ Ioc a b} :=
    measurableSet_Ioc.preimage (EuclideanSpace.proj 0).continuous.measurable
  have hb : AEStronglyMeasurable (fun y ↦ B j y p q) (volume.restrict {y | y 0 ∈ Ioc a b}) :=
    ((hB j p q).mono (fun _ hy ↦ Ioc_subset_Icc_self hy)).aestronglyMeasurable hs
  simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply] using
    hb.comp_quasiMeasurePreserving
      (Slices.measurePreserving_timeSpaceCons_restrict (n := n) (Ioc a b)).quasiMeasurePreserving

/-- Bounded C² matrices on the closed slab give continuous W¹,∞
curves, with the coefficient values and first spatial derivatives. -/
theorem exists_wkpSpace_matrix_timeSlices (hab : a < b)
    (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j p q, ContDiffOn ℝ 2 (fun y ↦ B j y p q) {y | y 0 ∈ Icc a b}) (M : ℝ≥0)
    (hzero : ∀ j p q y, y 0 ∈ Icc a b → ‖B j y p q‖ ≤ M)
    (hone : ∀ j p q y, y 0 ∈ Icc a b →
      ‖fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b} y‖ ≤ M)
    (htwo : ∀ j p q y, y 0 ∈ Icc a b →
      ‖iteratedFDerivWithin ℝ 2 (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b} y‖ ≤ M) :
    ∃ A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n),
      ContinuousOn A (Icc a b) ∧
      (∀ t ∈ Icc a b, ∀ j p q, ‖A t j p q‖ ≤ M) ∧
      (∀ t ∈ Icc a b, ∀ j p q,
        (wkpBaseCoordinateCLM (A t j p q) : ℝ^n → ℝ) =ᵐ[volume]
          fun x ↦ B j (timeSpaceCons t x) p q) ∧
      (∀ t ∈ Icc a b, ∀ j p q i,
        (wkpCoordinateCLM (singleDerivIndex n i) (A t j p q) : ℝ^n → ℝ) =ᵐ[volume]
          fun x ↦ fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b}
            (timeSpaceCons t x) (EuclideanSpace.single i.succ 1)) := by
  choose A hA hbound hbase hfirst using fun j p q ↦
    exists_lipschitz_wkpSpace_top_timeSlices hab (hB j p q) M
      (hzero j p q) (hone j p q) (htwo j p q)
  refine ⟨fun t j p q ↦ A j p q t, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_pi.mpr fun j ↦ continuousOn_pi.mpr fun p ↦
      continuousOn_pi.mpr fun q ↦ (hA j p q).continuousOn
  · exact fun t ht j p q ↦ hbound j p q t ht
  · exact fun t ht j p q ↦ hbase j p q t ht
  · exact fun t ht j p q i ↦ hfirst j p q t ht i

/-- Pointwise symmetry of matrices gives symmetry of their
coefficient classes, even when the classes were chosen independently. -/
theorem base_timeSlices_symmetric (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j y, y 0 ∈ Icc a b → (B j y).IsSymm) (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hbase : ∀ t ∈ Icc a b, ∀ j p q, (wkpBaseCoordinateCLM (A t j p q) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦
      B j (timeSpaceCons t x) p q) :
    ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p) := by
  intro t ht j p q
  apply Lp.ext
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hbase t ht j p q, hbase t ht j q p] with x hp hq
  rw [hp, hq]
  exact (hB j (timeSpaceCons t x) (by simpa using ht)).apply q p

end PDE.Hyperbolic.FirstOrder
