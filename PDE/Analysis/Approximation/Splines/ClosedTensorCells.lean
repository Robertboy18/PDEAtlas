/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.AlmostEverywhereCells

/-!
# Closed finite-cell cover for reflected tensor sources

The finite family of open source pieces covers physical volume almost
everywhere. Their closures therefore cover every physical point, including
all intersections of knots. This permits finite source jets to be estimated
on fixed radial segments even when the height itself is an axial knot.
-/

@[expose] public section

namespace CAS.Splines

open MeasureTheory Set

/-- The physical region of a pair of reflected radial pieces and one translated
axial piece. The exterior pieces include the zero extension of a finite tensor. -/
def reflectedTensorPiece (coordinate : ℝ → ℝ) (translation : ℝ)
    (kx ky : KnotSequence) (nx ny : ℕ)
    (positive negative : Option (Fin nx)) (axial : Option (Fin ny)) :
    Set (ℝ^2) :=
  {p | coordinate (p 0) ∈ knotPiece kx nx positive ∧
    -coordinate (p 0) ∈ knotPiece kx nx negative ∧
    coordinate (p 1 + translation) ∈ knotPiece ky ny axial}

/-- A finite family of closed physical piece regions covers every point. This is
stronger than restricting a planar almost-everywhere cover to a line, which
would fail for radial segments lying at axial knots. -/
theorem exists_mem_closure_reflectedTensorPiece
    (coordinate : ℝ → ℝ) (hinjective : Function.Injective coordinate) (translation : ℝ)
    (kx ky : KnotSequence) (nx ny : ℕ) (p : ℝ^2) :
    ∃ positive negative axial,
      p ∈ closure (reflectedTensorPiece coordinate translation kx ky nx ny
        positive negative axial) := by
  have hcover : ∀ᵐ p : ℝ^2 ∂volume, ∃ positive negative axial,
      p ∈ reflectedTensorPiece coordinate translation kx ky nx ny positive negative axial := by
    filter_upwards
      [ae_mem_knotPiece volume Measure.AbsolutelyContinuous.rfl coordinate hinjective 0 0 kx nx,
       ae_mem_knotPiece volume Measure.AbsolutelyContinuous.rfl (fun x ↦ -coordinate x)
         (neg_injective.comp hinjective) 0 0 kx nx,
       ae_mem_knotPiece volume Measure.AbsolutelyContinuous.rfl
         coordinate hinjective 1 translation ky ny] with p hp hn ha
    obtain ⟨positive, hp⟩ := hp
    obtain ⟨negative, hn⟩ := hn
    obtain ⟨axial, ha⟩ := ha
    have hpieces := And.intro hp (And.intro hn ha)
    exact ⟨positive, negative, axial, by simpa [reflectedTensorPiece] using hpieces⟩
  have hdense := (volume : Measure (ℝ^2)).dense_of_ae hcover
  have hunion : {p : ℝ^2 | ∃ positive negative axial,
      p ∈ reflectedTensorPiece coordinate translation kx ky nx ny positive negative axial} =
      ⋃ positive, ⋃ negative, ⋃ axial,
        reflectedTensorPiece coordinate translation kx ky nx ny positive negative axial := by
    ext x
    simp
  have hclosure := hdense.closure_eq
  rw [hunion] at hclosure
  simp only [closure_iUnion_of_finite] at hclosure
  have hmem := mem_univ p
  rw [← hclosure] at hmem
  simpa only [mem_iUnion] using hmem

end CAS.Splines
