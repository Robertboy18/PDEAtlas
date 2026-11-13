/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.FourPlusOne

/-!
# Integration in four-plus-one coordinates

Lebesgue integration on ℝ⁵ in Cartesian and polar coordinates on ℝ⁴ × ℝ.
The polar Jacobian is the cube of the radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv SobolevSpace
open scoped ENNReal RealInnerProductSpace Topology

namespace PDE.Analysis

/-- Whole-space integration in four radial coordinates and one axial coordinate,
with canonical volume normalization.
-/
theorem integral_fourPlusOnePoint
    (g : ℝ^5 → ℝ) :
    (∫ X : ℝ^5, g X) =
      ∫ p : ℝ^4 × ℝ^1,
        g (fourPlusOnePoint p.1 (p.2 0)) := by
  rw [PDE.Analysis.integral_euclideanSum 4 1 g]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [euclideanSumMeasurableEquiv_symm_fourOne]

/-- Fubini form of the four-plus-one decomposition, with the one-dimensional
factor identified canonically with `ℝ`.
-/
theorem integral_fourPlusOnePoint_iterated
    (g : ℝ^5 → ℝ) (hg : Integrable g volume) :
    (∫ X : ℝ^5, g X) =
      ∫ z : ℝ, ∫ y : ℝ^4,
        g (fourPlusOnePoint y z) := by
  let e := PDE.Analysis.euclideanSumMeasurableEquiv 4 1
  let G : ℝ^4 × ℝ^1 → ℝ :=
    fun p ↦ g (e.symm p)
  have hG : Integrable G volume := by
    have hcomp :=
      ((PDE.Analysis.euclideanSumMeasurableEquiv_measurePreserving 4 1).symm e
        |>.integrable_comp_emb e.symm.measurableEmbedding (g := g)).2 hg
    simpa [G, Function.comp_def] using hcomp
  calc
    (∫ X : ℝ^5, g X) = ∫ p, G p := by
      simpa [G] using PDE.Analysis.integral_euclideanSum 4 1 g
    _ = ∫ z : ℝ^1,
        ∫ y : ℝ^4, G (y, z) := by
      change (∫ p, G p ∂(volume.prod volume)) = _
      exact integral_prod_symm G hG
    _ = ∫ z : ℝ^1,
        ∫ y : ℝ^4,
          g (fourPlusOnePoint y (z 0)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      apply integral_congr_ae
      filter_upwards [] with y
      simp [G, e, euclideanSumMeasurableEquiv_symm_fourOne]
    _ = ∫ z : ℝ, ∫ y : ℝ^4,
        g (fourPlusOnePoint y z) := by
      let H : ℝ → ℝ := fun z ↦
        ∫ y : ℝ^4, g (fourPlusOnePoint y z)
      exact ((PiLp.volume_preserving_ofLp (Fin 1)).trans
        (volume_preserving_funUnique (Fin 1) ℝ)).integral_comp
          ((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
            (MeasurableEquiv.funUnique (Fin 1) ℝ)).measurableEmbedding H

/-- Four-dimensional polar integration followed by the axial integral.  This
is the exact `s^3 ds dσ dz` decomposition used in the `S^3` reduction.
-/
theorem integral_fourPlusOnePoint_polar
    (g : ℝ^5 → ℝ) (hg : Integrable g volume) :
    (∫ X : ℝ^5, g X) =
      ∫ z : ℝ, ∫ s in Set.Ioi (0 : ℝ), s ^ 3 *
        ∫ σ : Metric.sphere (0 : ℝ^4) 1,
          g (fourPlusOnePoint
            (s • (σ : ℝ^4)) z)
          ∂(volume : Measure (ℝ^4)).toSphere := by
  let e := PDE.Analysis.euclideanSumMeasurableEquiv 4 1
  let G : ℝ^4 × ℝ^1 → ℝ :=
    fun p ↦ g (e.symm p)
  have hG : Integrable G volume := by
    have hcomp :=
      ((PDE.Analysis.euclideanSumMeasurableEquiv_measurePreserving 4 1).symm e
        |>.integrable_comp_emb e.symm.measurableEmbedding (g := g)).2 hg
    simpa [G, Function.comp_def] using hcomp
  have hsection : ∀ᵐ z : ℝ^1 ∂volume,
      Integrable (fun y : ℝ^4 ↦ G (y, z)) volume :=
    hG.prod_left_ae
  calc
    (∫ X : ℝ^5, g X) =
        ∫ z : ℝ^1,
          ∫ y : ℝ^4, G (y, z) := by
      rw [PDE.Analysis.integral_euclideanSum 4 1 g]
      change (∫ p, G p ∂(volume.prod volume)) = _
      exact integral_prod_symm G hG
    _ = ∫ z : ℝ^1,
        ∫ s in Set.Ioi (0 : ℝ), s ^ 3 *
          ∫ σ : Metric.sphere (0 : ℝ^4) 1,
            g (fourPlusOnePoint
              (s • (σ : ℝ^4)) (z 0))
            ∂(volume : Measure (ℝ^4)).toSphere := by
      apply integral_congr_ae
      filter_upwards [hsection] with z hz
      have hpolar := PDE.Analysis.integral_polar_addHaar_iterated
        (volume : Measure (ℝ^4))
        (fun y : ℝ^4 ↦ G (y, z)) hz
      simpa [G, e, euclideanSumMeasurableEquiv_symm_fourOne,
        smul_eq_mul] using hpolar
    _ = ∫ z : ℝ, ∫ s in Set.Ioi (0 : ℝ), s ^ 3 *
        ∫ σ : Metric.sphere (0 : ℝ^4) 1,
          g (fourPlusOnePoint
            (s • (σ : ℝ^4)) z)
          ∂(volume : Measure (ℝ^4)).toSphere := by
      let H : ℝ → ℝ := fun z ↦
        ∫ s in Set.Ioi (0 : ℝ), s ^ 3 *
          ∫ σ : Metric.sphere (0 : ℝ^4) 1,
            g (fourPlusOnePoint
              (s • (σ : ℝ^4)) z)
            ∂(volume : Measure (ℝ^4)).toSphere
      exact ((PiLp.volume_preserving_ofLp (Fin 1)).trans
        (volume_preserving_funUnique (Fin 1) ℝ)).integral_comp
          ((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
            (MeasurableEquiv.funUnique (Fin 1) ℝ)).measurableEmbedding H

end PDE.Analysis
