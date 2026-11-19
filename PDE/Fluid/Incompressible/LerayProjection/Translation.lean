/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection
public import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Translation invariance of the whole-space Leray projection

Translating a compact smooth scalar test translates its gradient. Translation
is unitary on whole-space `L²`, so both the solenoidal subspace and its orthogonal
complement are invariant. Uniqueness of orthogonal projection then proves that
the actual Leray operator commutes with spatial translations.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

/-- Translation preserves the whole-space Sobolev-domain measure. -/
theorem wholeSpace_translation_measurePreserving (y : ℝ^n) :
    MeasurePreserving (fun x : ℝ^n ↦ x + y)
      (domainMeasure n Set.univ) (domainMeasure n Set.univ) := by
  simpa only [domainMeasure, Measure.restrict_univ] using
    measurePreserving_add_right (volume : Measure (ℝ^n)) y

/-- Spatial translation on the actual whole-space fluid `L²` pivot. -/
def l2Translate (y : ℝ^n) : WholeSpaceL2 n →ₗᵢ[ℝ] WholeSpaceL2 n :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ^n ↦ x + y)
    (wholeSpace_translation_measurePreserving y)

/-- Translation agrees with the translated representative almost everywhere. -/
theorem l2Translate_ae (y : ℝ^n) (u : WholeSpaceL2 n) :
    l2Translate y u =ᵐ[domainMeasure n Set.univ] fun x ↦ u (x + y) :=
  Lp.coeFn_compMeasurePreserving u (wholeSpace_translation_measurePreserving y)

/-- Translations compose by addition of their displacement vectors. -/
theorem l2Translate_add (y z : ℝ^n) (u : WholeSpaceL2 n) :
    l2Translate y (l2Translate z u) = l2Translate (y + z) u := by
  apply Lp.ext
  have hs := (wholeSpace_translation_measurePreserving y).quasiMeasurePreserving.ae
    (l2Translate_ae z u)
  filter_upwards [l2Translate_ae y (l2Translate z u), l2Translate_ae (y + z) u, hs]
    with x hy hyz hz
  rw [hy, hyz, hz, add_assoc]

/-- Zero translation fixes every vector. -/
@[simp]
theorem l2Translate_zero (u : WholeSpaceL2 n) : l2Translate (0 : ℝ^n) u = u := by
  apply Lp.ext
  simpa only [add_zero] using l2Translate_ae (0 : ℝ^n) u

/-- Opposite translations are adjoint in the physical `L²` pairing. -/
theorem inner_l2Translate_left (y : ℝ^n) (u v : WholeSpaceL2 n) :
    inner ℝ (l2Translate y u) v = inner ℝ u (l2Translate (-y) v) := by
  have hv : l2Translate y (l2Translate (-y) v) = v := by
    rw [l2Translate_add, add_neg_cancel, l2Translate_zero]
  calc
    _ = inner ℝ (l2Translate y u) (l2Translate y (l2Translate (-y) v)) := by rw [hv]
    _ = _ := (l2Translate y).inner_map_map _ _

/-- Translate a compact smooth scalar whole-space test. -/
def translatedTest (y : ℝ^n) (φ : TestFunctionOn n Set.univ) :
    TestFunctionOn n Set.univ :=
  ⟨TestFunction.mk (fun x ↦ φ.1.toFun (x + y))
    (φ.1.contDiff.comp (contDiff_id.add contDiff_const))
    (φ.1.hasCompactSupport.comp_homeomorph (Homeomorph.addRight y))
    (Set.subset_univ _), Set.subset_univ _⟩

/-- Translation of a test gradient is the gradient of the translated test. -/
theorem l2Translate_testGradient (y : ℝ^n) (φ : TestFunctionOn n Set.univ) :
    l2Translate y (l2TestGradient φ) = l2TestGradient (translatedTest y φ) := by
  apply Lp.ext
  have hs := (wholeSpace_translation_measurePreserving y).quasiMeasurePreserving.ae
    (l2TestGradient_apply_ae φ)
  filter_upwards [l2Translate_ae y (l2TestGradient φ),
    l2TestGradient_apply_ae (translatedTest y φ), hs] with x ht hg hs
  apply PiLp.ext
  intro i
  rw [ht, hg i, hs i]
  exact (congrFun (PDE.partialDeriv_comp_add_right i φ.1.toFun y) x).symm

/-- Spatial translation preserves distributional solenoidality. -/
theorem l2Translate_mem_solenoidal (y : ℝ^n) {u : WholeSpaceL2 n}
    (hu : u ∈ l2Solenoidal n) : l2Translate y u ∈ l2Solenoidal n := by
  apply (mem_l2Solenoidal_iff_inner _).mpr
  intro φ
  rw [inner_l2Translate_left, l2Translate_testGradient]
  exact (mem_l2Solenoidal_iff_inner _).mp hu _

/-- Translation also preserves the pressure-gradient orthogonal complement. -/
theorem l2Translate_mem_solenoidal_orthogonal (y : ℝ^n) {u : WholeSpaceL2 n}
    (hu : u ∈ (l2Solenoidal n).orthogonal) :
    l2Translate y u ∈ (l2Solenoidal n).orthogonal := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro v hv
  rw [inner_l2Translate_left]
  exact (Submodule.mem_orthogonal' _ _).mp hu _ (l2Translate_mem_solenoidal (-y) hv)

/-- The actual whole-space Leray projection commutes with spatial translation. -/
theorem lerayProjection_l2Translate (y : ℝ^n) (u : WholeSpaceL2 n) :
    lerayProjection n (l2Translate y u) = l2Translate y (lerayProjection n u) := by
  apply (l2Solenoidal n).eq_starProjection_of_mem_orthogonal
    (l2Translate_mem_solenoidal y (lerayProjection_mem n u))
  rw [← map_sub]
  exact l2Translate_mem_solenoidal_orthogonal y
    ((l2Solenoidal n).sub_starProjection_mem_orthogonal u)

end IncompressibleFlow
