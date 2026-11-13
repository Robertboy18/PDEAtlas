/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Weighted.Hilbert

/-!
# Limits in weighted derivative completions

There are finitely many derivative rows through a fixed order. Continuity and convergence
in the completed weighted graph can therefore be checked in each row. A family of row
limits belongs to the completion whenever it is approached by completed jets.
-/

@[expose] public noncomputable section

open Filter MeasureTheory SobolevSpace.GraphSpace
open scoped ENNReal Topology

namespace SobolevSpace.Weighted.CompletedHkSpaceOn

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- A map into the weighted completion is continuous exactly when every derivative row is
continuous in its weighted `L²` space. -/
theorem continuous_iff_coordinate
    {X : Type*} [TopologicalSpace X]
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞) {f : X → CompletedHkSpaceOn n k Ω w} :
    Continuous f ↔ ∀ a, Continuous (fun x ↦ coordinate w a (f x)) := by
  constructor
  · intro h a
    exact (coordinate w a).continuous.comp h
  · intro h
    apply continuous_induced_rng.mpr
    exact (PiLp.continuousLinearEquiv 2 ℝ fun a ↦
      Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a))).symm.continuous.comp
        (continuous_pi h)

/-- If along a nontrivial filter every row `coordinate w a (f j)` of a family `f` in the
completion tends to `row a`, then some `U` in the completion has the rows `row a` and `f`
tends to `U`. No lower or upper comparison between the row measures is required. -/
theorem exists_of_coordinate_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞)
    (f : ι → CompletedHkSpaceOn n k Ω w)
    (row : ∀ a, Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a)))
    (h : ∀ a, Tendsto (fun j ↦ coordinate w a (f j)) l (𝓝 (row a))) :
    ∃ U : CompletedHkSpaceOn n k Ω w,
      (∀ a, coordinate w a U = row a) ∧ Tendsto f l (𝓝 U) := by
  let V : DerivativeL2RowsOn n k Ω w := WithLp.toLp 2 row
  have hV : Tendsto (fun j ↦ (f j).val) l (𝓝 V) :=
    ((PiLp.continuousLinearEquiv 2 ℝ fun a ↦
      Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a))).symm.continuous.tendsto _).comp
        (tendsto_pi_nhds.mpr h)
  have hmem : V ∈ completedHkSubmoduleOn w :=
    isClosed_closure.mem_of_tendsto hV (Eventually.of_forall fun j ↦ (f j).property)
  exact ⟨⟨V, hmem⟩, fun _ ↦ rfl, tendsto_subtype_rng.mpr hV⟩

end SobolevSpace.Weighted.CompletedHkSpaceOn
