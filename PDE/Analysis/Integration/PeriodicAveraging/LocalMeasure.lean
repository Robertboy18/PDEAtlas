/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.FundamentalCell
public import PDE.Analysis.MeasureTheory.Lp.NormDomination

/-!
# Local measure properties of periodic lifts

Overlapping open cells cover Euclidean space. A countable subcover passes
almost-everywhere identities on the torus to their Euclidean lifts. In particular,
the lift is independent of the representative of a periodic function.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Analysis.PeriodicAveraging

/-- The open unit cell with lower corner `a`. -/
def openUnitCell {n : ℕ} (a : Fin n → ℝ) : Set (ℝ^n) :=
  {x | ∀ i, x i ∈ Ioo (a i) (a i + 1)}

/-- Coordinatewise open unit cells are open in Euclidean space. -/
theorem isOpen_openUnitCell {n : ℕ} (a : Fin n → ℝ) :
    IsOpen (openUnitCell a) := by
  simp only [openUnitCell, ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

/-- The open cell is contained in its half-open fundamental cell. -/
theorem openUnitCell_subset_unitCell {n : ℕ} (a : Fin n → ℝ) :
    openUnitCell a ⊆ unitCell a :=
  fun _ hx i ↦ ⟨(hx i).1, (hx i).2.le⟩

/-- Allowing all translates of an open cell covers Euclidean space. -/
theorem iUnion_openUnitCell (n : ℕ) :
    ⋃ a : Fin n → ℝ, openUnitCell a = univ := by
  apply eq_univ_of_forall
  intro x
  refine mem_iUnion.mpr ⟨fun i ↦ x i - 1 / 2, ?_⟩
  intro i
  constructor <;> linarith

/-- Almost-everywhere properties of periodic functions hold for their Euclidean lifts. -/
theorem ae_comp_toTorus {n : ℕ} {p : UnitAddTorus (Fin n) → Prop}
    (hp : ∀ᵐ x ∂cellMeasure n, p x) :
    ∀ᵐ x ∂(volume : Measure (ℝ^n)), p (toTorus n x) := by
  obtain ⟨s, hs, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (openUnitCell (n := n)) isOpen_openUnitCell (by rw [iUnion_openUnitCell])
  have h : ∀ᵐ x ∂volume.restrict (⋃ a ∈ s, openUnitCell a), p (toTorus n x) := by
    apply (ae_restrict_biUnion_iff openUnitCell hs _).mpr
    intro a _ha
    exact ae_restrict_of_ae_restrict_of_subset (openUnitCell_subset_unitCell a)
      ((measurePreserving_toTorus a).quasiMeasurePreserving.ae hp)
  rwa [univ_subset_iff.mp hcover, Measure.restrict_univ] at h

/-- The quotient map pulls null sets on the torus back to Euclidean null sets. -/
theorem quasiMeasurePreserving_toTorus (n : ℕ) :
    QuasiMeasurePreserving (toTorus n) volume (cellMeasure n) := by
  refine ⟨(toTorus n).measurable, Measure.AbsolutelyContinuous.mk fun s hs hzero ↦ ?_⟩
  rw [Measure.map_apply (toTorus n).measurable hs, measure_eq_zero_iff_ae_notMem]
  exact ae_comp_toTorus (measure_eq_zero_iff_ae_notMem.mp hzero)

/-- A nonzero dilation followed by periodic lifting preserves null-set identities. -/
theorem quasiMeasurePreserving_toTorus_smul (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    QuasiMeasurePreserving (fun x : ℝ^n ↦ toTorus n (c • x))
      volume (cellMeasure n) :=
  (quasiMeasurePreserving_toTorus n).comp (Measure.quasiMeasurePreserving_smul volume hc)

/-- Rescaling preserves the essential bound of a periodic field. -/
theorem norm_comp_toTorus_smul_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (u : Lp E ∞ (cellMeasure n)) (c : ℝ) (hc : c ≠ 0) :
    ∀ᵐ x ∂(volume : Measure (ℝ^n)), ‖u (toTorus n (c • x))‖ ≤ ‖u‖ :=
  (quasiMeasurePreserving_toTorus_smul n c hc).ae (Lp.norm_apply_ae_le u)

/-- An essentially bounded periodic field remains globally essentially bounded after rescaling. -/
theorem memLp_top_comp_toTorus_smul {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (u : Lp E ∞ (cellMeasure n)) (c : ℝ) (hc : c ≠ 0) :
    MemLp (fun x : ℝ^n ↦ u (toTorus n (c • x))) ∞ volume :=
  memLp_top_of_bound
    ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_toTorus_smul n c hc))
    ‖u‖ (norm_comp_toTorus_smul_le u c hc)

end PDE.Analysis.PeriodicAveraging
