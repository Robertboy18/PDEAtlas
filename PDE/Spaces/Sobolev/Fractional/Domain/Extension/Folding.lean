/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Folding across the boundary of a half-space

Replacing the last coordinate by its absolute value contracts Euclidean distances.
It sends Lebesgue measure to twice Lebesgue measure restricted to the open upper
half-space; the boundary hyperplane is null. On pairs, the corresponding factor is four.
These facts supply the change of variables for intrinsic fractional reflection estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.Extension

open SobolevSpace.HalfSpace

variable (n : ℕ) [Fact (0 < n)]

/-- Fold the lower half-space into the upper half-space by even reflection. -/
def foldUpper (x : ℝ^n) : ℝ^n := by
  classical
  exact if x ∈ lower n then reflect n x else x

/-- Folding fixes every point of the upper half-space. -/
theorem foldUpper_of_mem_upper {x : ℝ^n} (hx : x ∈ upper n) :
    foldUpper n x = x := by
  have hnot : x ∉ lower n := by
    change ¬x (PDE.Common.lastIndex (n := n)) < 0
    exact not_lt.mpr (le_of_lt hx)
  simp [foldUpper, hnot]

/-- Folding acts by reflection in the lower half-space. -/
theorem foldUpper_of_mem_lower {x : ℝ^n} (hx : x ∈ lower n) :
    foldUpper n x = reflect n x := by
  simp [foldUpper, hx]

/-- The normal coordinate of a folded point is its absolute value. -/
@[simp]
theorem foldUpper_apply_last (x : ℝ^n) :
    foldUpper n x (PDE.Common.lastIndex (n := n)) =
      |x (PDE.Common.lastIndex (n := n))| := by
  by_cases hx : x ∈ lower n
  · have hx' : x (PDE.Common.lastIndex (n := n)) < 0 := hx
    simp [foldUpper, hx, abs_of_neg hx']
  · have hx' : 0 ≤ x (PDE.Common.lastIndex (n := n)) := le_of_not_gt hx
    simp [foldUpper, hx, abs_of_nonneg hx']

/-- Folding leaves tangential coordinates unchanged. -/
@[simp]
theorem foldUpper_apply_of_ne_last (x : ℝ^n) {i : Fin n}
    (hi : i ≠ PDE.Common.lastIndex (n := n)) :
    foldUpper n x i = x i := by
  by_cases hx : x ∈ lower n <;>
    simp [foldUpper, hx, reflect_apply_of_ne_last n x hi]

/-- Folding contracts the distance between every pair, including pairs on opposite sides. -/
theorem norm_foldUpper_sub_le (x y : ℝ^n) :
    ‖foldUpper n x - foldUpper n y‖ ≤ ‖x - y‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply]
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst i
    simp only [foldUpper_apply_last]
    exact sq_le_sq.mpr (abs_abs_sub_abs_le_abs_sub _ _)
  · simp [foldUpper_apply_of_ne_last n _ hi]

/-- Folding is measurable. -/
theorem measurable_foldUpper : Measurable (foldUpper n) :=
  (measurePreserving_reflect n).measurable.piecewise
    (measurableSet_lower n) measurable_id

/-- Upper and lower restricted volume exhaust ambient volume, since the boundary is null. -/
theorem volume_eq_add_halfSpaces :
    (volume : Measure (ℝ^n)) =
      volume.restrict (upper n) + volume.restrict (lower n) := by
  rw [← Measure.restrict_congr_set (compl_upper_ae_eq_lower n)]
  exact (Measure.restrict_add_restrict_compl (measurableSet_upper n)).symm

/-- The pushforward under folding is twice restricted upper-half-space volume. -/
theorem measurePreserving_foldUpper :
    MeasurePreserving (foldUpper n) (volume : Measure (ℝ^n))
      ((2 : ℝ≥0∞) • volume.restrict (upper n)) := by
  refine ⟨measurable_foldUpper n, ?_⟩
  have hu : (volume.restrict (upper n)).map (foldUpper n) =
      (volume : Measure (ℝ^n)).restrict (upper n) := by
    calc
      _ = (volume.restrict (upper n)).map id := Measure.map_congr <| by
        filter_upwards [ae_restrict_mem (measurableSet_upper n)] with x hx
        exact foldUpper_of_mem_upper n hx
      _ = _ := Measure.map_id
  have hl : (volume.restrict (lower n)).map (foldUpper n) =
      (volume : Measure (ℝ^n)).restrict (upper n) := by
    calc
      _ = (volume.restrict (lower n)).map (reflect n) := Measure.map_congr <| by
        filter_upwards [ae_restrict_mem (measurableSet_lower n)] with x hx
        exact foldUpper_of_mem_lower n hx
      _ = _ := (measurePreserving_reflect_restrict_lower n).map_eq
  calc
    _ = (volume.restrict (upper n)).map (foldUpper n) +
        (volume.restrict (lower n)).map (foldUpper n) := by
      conv_lhs => rw [volume_eq_add_halfSpaces n]
      exact Measure.map_add _ _ (measurable_foldUpper n)
    _ = _ := by rw [hu, hl, two_smul]

/-- Folding both variables multiplies upper-half-space product measure by four. -/
theorem measurePreserving_foldUpper_prod :
    MeasurePreserving (Prod.map (foldUpper n) (foldUpper n))
      ((volume : Measure (ℝ^n)).prod volume)
      ((4 : ℝ≥0∞) •
        ((volume : Measure (ℝ^n)).restrict (upper n)).prod
          (volume.restrict (upper n))) := by
  convert (measurePreserving_foldUpper n).prod (measurePreserving_foldUpper n) using 1
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  norm_num

/-- Change of variables under folding for an almost-everywhere measurable integrand. -/
theorem lintegral_comp_foldUpper (f : ℝ^n → ℝ≥0∞)
    (hf : AEMeasurable f ((volume : Measure (ℝ^n)).restrict (upper n))) :
    ∫⁻ x, f (foldUpper n x) = 2 * ∫⁻ x in upper n, f x := by
  have hmap := (measurePreserving_foldUpper n).map_eq
  have hf' : AEMeasurable f (volume.map (foldUpper n)) := by
    rw [hmap]
    exact hf.smul_measure 2
  rw [← lintegral_map' hf' (measurable_foldUpper n).aemeasurable, hmap,
    lintegral_smul_measure]
  rfl

/-- The double-integral change of variables under folding has multiplicity four. -/
theorem lintegral_comp_foldUpper_prod (f : ℝ^n × ℝ^n → ℝ≥0∞)
    (hf : AEMeasurable f (((volume : Measure (ℝ^n)).restrict (upper n)).prod
      (volume.restrict (upper n)))) :
    ∫⁻ p, f (Prod.map (foldUpper n) (foldUpper n) p)
        ∂((volume : Measure (ℝ^n)).prod volume) =
      4 * ∫⁻ p, f p
        ∂(((volume : Measure (ℝ^n)).restrict (upper n)).prod
          (volume.restrict (upper n))) := by
  have hmap := (measurePreserving_foldUpper_prod n).map_eq
  have hf' : AEMeasurable f
      (((volume : Measure (ℝ^n)).prod volume).map
        (Prod.map (foldUpper n) (foldUpper n))) := by
    rw [hmap]
    exact hf.smul_measure 4
  rw [← lintegral_map' hf' (measurePreserving_foldUpper_prod n).aemeasurable, hmap,
    lintegral_smul_measure]
  rfl

end SobolevSpace.Fractional.Extension
