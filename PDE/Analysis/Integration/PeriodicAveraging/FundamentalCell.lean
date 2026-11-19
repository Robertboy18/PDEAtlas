/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Torus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lifting periodic functions to Euclidean cells

The coordinate quotient from Euclidean space to the unit torus preserves measure
on every half-open unit cell. Its pullback is consequently an `Lᵖ` isometry,
which identifies Haar measure on the torus with Lebesgue measure on a unit cell.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Analysis.PeriodicAveraging

/-- The quotient map from Euclidean space to the unit torus. -/
def toTorus (n : ℕ) : C(ℝ^n, UnitAddTorus (Fin n)) :=
  ⟨fun x i ↦ (x i : UnitAddCircle), continuous_pi fun i ↦
    (AddCircle.continuous_mk' 1).comp (EuclideanSpace.proj (𝕜 := ℝ) i).continuous⟩

/-- A half-open Euclidean unit cell with lower corner `a`. -/
def unitCell {n : ℕ} (a : Fin n → ℝ) : Set (ℝ^n) :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i + 1)}

/-- Unit cells are measurable for Euclidean Lebesgue measure. -/
theorem measurableSet_unitCell {n : ℕ} (a : Fin n → ℝ) :
    MeasurableSet (unitCell a) :=
  (MeasurableSet.univ_pi' fun i ↦ measurableSet_Ioc (a := a i) (b := a i + 1)).preimage
    (PiLp.volume_preserving_ofLp (Fin n)).measurable

/-- The quotient map preserves normalized cell measure. -/
theorem measurePreserving_toTorus {n : ℕ} (a : Fin n → ℝ) :
    MeasurePreserving (toTorus n) (volume.restrict (unitCell a)) (cellMeasure n) := by
  have hp : MeasurePreserving
      (fun x : Fin n → ℝ ↦ fun i ↦ (x i : UnitAddCircle))
      (volume.restrict (Set.pi univ fun i ↦ Ioc (a i) (a i + 1))) (cellMeasure n) := by
    have hi (i : Fin n) : MeasurePreserving (fun x : ℝ ↦ (x : UnitAddCircle))
        (volume.restrict (Ioc (a i) (a i + 1))) AddCircle.haarAddCircle := by
      simpa [volume, AddCircle.haarAddCircle] using AddCircle.measurePreserving_mk 1 (a i)
    convert measurePreserving_pi
      (fun i ↦ volume.restrict (Ioc (a i) (a i + 1)))
      (fun _ : Fin n ↦ AddCircle.haarAddCircle) hi using 1
    · exact Measure.restrict_pi_pi _ _
    · rfl
  have hset : (Set.pi univ fun i ↦ Ioc (a i) (a i + 1)) =
      {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)} := by
    ext x
    simp
  rw [hset] at hp
  have hq := (PiLp.volume_preserving_ofLp (Fin n)).restrict_preimage
    (MeasurableSet.univ_pi' fun i ↦ measurableSet_Ioc (a := a i) (b := a i + 1))
  exact hp.comp hq

/-- Pullback to a fundamental cell, as a linear isometry on `Lᵖ`. -/
def liftLp {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Fin n → ℝ) :
    Lp E p (cellMeasure n) →ₗᵢ[ℝ] Lp E p (volume.restrict (unitCell a)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (toTorus n) (measurePreserving_toTorus a)

/-- The lifted equivalence class is represented by composition with the quotient. -/
theorem liftLp_ae {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : Fin n → ℝ) (u : Lp E p (cellMeasure n)) :
    liftLp p a u =ᵐ[volume.restrict (unitCell a)] fun x ↦ u (toTorus n x) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_toTorus a)

/-- Every periodic `Lᵖ` representative remains in `Lᵖ` on a fundamental cell. -/
theorem memLp_comp_toTorus {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (a : Fin n → ℝ) (u : Lp E p (cellMeasure n)) :
    MemLp (fun x ↦ u (toTorus n x)) p (volume.restrict (unitCell a)) :=
  (Lp.memLp u).comp_measurePreserving (measurePreserving_toTorus a)

end PDE.Analysis.PeriodicAveraging
