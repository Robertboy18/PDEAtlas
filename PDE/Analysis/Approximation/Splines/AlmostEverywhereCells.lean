/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.CoxDeBoor
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Interval.Set.Union
public import PDE.Common.Euclidean

/-!
# Almost-everywhere interior cells of finite knot windows

A translated coordinate hits a prescribed knot only on a null affine hyperplane.
An injective change of that coordinate preserves this conclusion without any
Jacobian or smoothness hypothesis. Finite knot windows therefore admit interior
cells almost everywhere on their spans, including when knots are repeated.
Absolute continuity transfers the cover to restricted and weighted measures.
-/

@[expose] public section

namespace CAS.Splines

open Filter MeasureTheory Set

/-- A point in a finite knot span and unequal to its knots lies in an open cell.
Repeated knots contribute empty cells and need no separate case. -/
theorem exists_mem_Ioo_knot_cell (knots : KnotSequence) (count : ℕ) {x : ℝ}
    (hx : x ∈ Icc (knots 0) (knots count))
    (hne : ∀ j : Fin (count + 1), x ≠ knots j) :
    ∃ cell < count, x ∈ Ioo (knots cell) (knots (cell + 1)) := by
  have hright : x < knots count :=
    lt_of_le_of_ne hx.2 (hne ⟨count, by omega⟩)
  obtain ⟨cell, hcell, hmem⟩ := mem_iUnion₂.mp
    (Ico_subset_biUnion_Ico count knots ⟨hx.1, hright⟩)
  have hlt : cell < count := Finset.mem_range.mp hcell
  exact ⟨cell, hlt, lt_of_le_of_ne hmem.1 (hne ⟨cell, by omega⟩).symm, hmem.2⟩

/-- An injectively transformed translated coordinate avoids any finite family of
knot values almost everywhere for every measure absolutely continuous to volume. -/
theorem ae_coordinate_ne_knots {n m : ℕ}
    (ν : Measure (ℝ^n)) (hν : ν ≪ volume)
    (coordinate : ℝ → ℝ) (hinjective : Function.Injective coordinate)
    (i : Fin n) (translation : ℝ) (knots : Fin m → ℝ) :
    ∀ᵐ p : ℝ^n ∂ν, ∀ j, coordinate (p i + translation) ≠ knots j := by
  apply hν.ae_le
  change ∀ᵐ p : ℝ^n ∂volume,
    ∀ j, coordinate (p i + translation) ≠ knots j
  rw [ae_all_iff]
  intro j
  by_cases hex : ∃ a, coordinate a = knots j
  · obtain ⟨a, ha⟩ := hex
    have hbase : ∀ᵐ p : Fin n → ℝ ∂volume, p i ≠ a - translation :=
      Measure.ae_eval_ne (fun _ : Fin n ↦ (volume : Measure ℝ)) i (a - translation)
    have hphysical := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae hbase
    filter_upwards [hphysical] with p hp
    intro h
    apply hp
    exact eq_sub_iff_add_eq.mpr (hinjective (h.trans ha.symm))
  · exact ae_of_all _ fun p h ↦ hex ⟨p i + translation, h⟩

/-- The finite union of transformed knot level sets is null. For identity and
arsinh coordinates each nonempty level set is an affine coordinate hyperplane. -/
theorem measure_coordinate_knots_eq_zero {n m : ℕ}
    (ν : Measure (ℝ^n)) (hν : ν ≪ volume)
    (coordinate : ℝ → ℝ) (hinjective : Function.Injective coordinate)
    (i : Fin n) (translation : ℝ) (knots : Fin m → ℝ) :
    ν {p | ∃ j, coordinate (p i + translation) = knots j} = 0 := by
  have h := ae_coordinate_ne_knots ν hν coordinate hinjective i translation knots
  simpa only [ae_iff, not_forall, not_not] using h

/-- Inside a finite knot span, almost every transformed coordinate lies in an
open cell. The only removed points are the explicit finite knot level sets. -/
theorem ae_mem_Ioo_knot_cell {n : ℕ} (ν : Measure (ℝ^n)) (hν : ν ≪ volume)
    (coordinate : ℝ → ℝ) (hinjective : Function.Injective coordinate)
    (i : Fin n) (translation : ℝ) (knots : KnotSequence) (count : ℕ) :
    ∀ᵐ p : ℝ^n ∂ν,
      coordinate (p i + translation) ∈ Icc (knots 0) (knots count) →
        ∃ cell < count, coordinate (p i + translation) ∈
          Ioo (knots cell) (knots (cell + 1)) := by
  filter_upwards [ae_coordinate_ne_knots ν hν coordinate hinjective i translation
    (fun j : Fin (count + 1) ↦ knots j)] with p hp hspan
  exact exists_mem_Ioo_knot_cell knots count hspan hp

/-- The open pieces of a finite knot span: an interior cell, or the exterior of
the closed span. A finite tensor is identically zero in the exterior when the
span contains all its basis supports. -/
def knotPiece (knots : KnotSequence) (count : ℕ) : Option (Fin count) → Set ℝ
  | none => (Icc (knots 0) (knots count))ᶜ
  | some cell => Ioo (knots cell) (knots (cell + 1))

/-- Every piece is open, so membership supplies ambient neighborhood geometry. -/
theorem isOpen_knotPiece (knots : KnotSequence) (count : ℕ) (piece : Option (Fin count)) :
    IsOpen (knotPiece knots count piece) := by
  cases piece with
  | none => exact isClosed_Icc.isOpen_compl
  | some cell => exact isOpen_Ioo

/-- Every point avoiding the finite knot values belongs to an open piece. This
includes exterior points and degenerate spans with no nonempty interior cell. -/
theorem exists_mem_knotPiece (knots : KnotSequence) (count : ℕ) {x : ℝ}
    (hne : ∀ j : Fin (count + 1), x ≠ knots j) :
    ∃ piece, x ∈ knotPiece knots count piece := by
  by_cases hspan : x ∈ Icc (knots 0) (knots count)
  · obtain ⟨cell, hcell, hx⟩ := exists_mem_Ioo_knot_cell knots count hspan hne
    exact ⟨some ⟨cell, hcell⟩, hx⟩
  · exact ⟨none, hspan⟩

/-- A finite knot partition, completed by its open exterior, covers almost every
transformed coordinate. No smoothness condition at a knot is used. -/
theorem ae_mem_knotPiece {n : ℕ} (ν : Measure (ℝ^n)) (hν : ν ≪ volume)
    (coordinate : ℝ → ℝ) (hinjective : Function.Injective coordinate)
    (i : Fin n) (translation : ℝ) (knots : KnotSequence) (count : ℕ) :
    ∀ᵐ p : ℝ^n ∂ν,
      ∃ piece, coordinate (p i + translation) ∈ knotPiece knots count piece := by
  filter_upwards [ae_coordinate_ne_knots ν hν coordinate hinjective i translation
    (fun j : Fin (count + 1) ↦ knots j)] with p hp
  exact exists_mem_knotPiece knots count hp

/-- Both radial reflections and the translated axial coordinate lie in open
pieces almost everywhere, simultaneously for any finite family of source grids. -/
theorem ae_mem_reflected_tensor_pieces {heads : ℕ}
    (ν : Measure (ℝ^2)) (hν : ν ≪ volume)
    (coordinate : ℝ → ℝ) (hinjective : Function.Injective coordinate) (translation : ℝ)
    (kx ky : Fin heads → KnotSequence) (nx ny : Fin heads → ℕ) :
    ∀ᵐ p : ℝ^2 ∂ν,
      ∃ (positive negative : ∀ h, Option (Fin (nx h))) (axial : ∀ h, Option (Fin (ny h))),
        ∀ h, coordinate (p 0) ∈ knotPiece (kx h) (nx h) (positive h) ∧
          -coordinate (p 0) ∈ knotPiece (kx h) (nx h) (negative h) ∧
          coordinate (p 1 + translation) ∈ knotPiece (ky h) (ny h) (axial h) := by
  have hp : ∀ᵐ p : ℝ^2 ∂ν, ∀ h,
      ∃ piece, coordinate (p 0) ∈ knotPiece (kx h) (nx h) piece := by
    rw [ae_all_iff]
    intro h
    simpa only [add_zero] using
      ae_mem_knotPiece ν hν coordinate hinjective 0 0 (kx h) (nx h)
  have hn : ∀ᵐ p : ℝ^2 ∂ν, ∀ h,
      ∃ piece, -coordinate (p 0) ∈ knotPiece (kx h) (nx h) piece := by
    rw [ae_all_iff]
    intro h
    simpa only [add_zero] using ae_mem_knotPiece ν hν (fun x ↦ -coordinate x)
      (neg_injective.comp hinjective) 0 0 (kx h) (nx h)
  have hy : ∀ᵐ p : ℝ^2 ∂ν, ∀ h,
      ∃ piece, coordinate (p 1 + translation) ∈ knotPiece (ky h) (ny h) piece := by
    rw [ae_all_iff]
    intro h
    exact ae_mem_knotPiece ν hν coordinate hinjective 1 translation (ky h) (ny h)
  filter_upwards [hp, hn, hy] with p hp hn hy
  choose positive hpositive using hp
  choose negative hnegative using hn
  choose axial haxial using hy
  exact ⟨positive, negative, axial, fun h ↦ ⟨hpositive h, hnegative h, haxial h⟩⟩

end CAS.Splines
