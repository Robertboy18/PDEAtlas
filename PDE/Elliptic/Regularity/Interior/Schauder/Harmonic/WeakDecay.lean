/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Weyl.Sobolev
public import PDE.Elliptic.Regularity.Interior.Schauder.Harmonic.Oscillation
import PDE.Elliptic.Classical.Harmonic.Derivatives
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative

/-!
# Mean-square gradient decay for weak harmonic fields

The literal weak Dirichlet identity gives a harmonic representative by Weyl's
lemma. Uniqueness of weak derivatives then identifies its classical gradient
with the given Sobolev coordinates. Harmonic mean-square decay therefore holds
for the original gradient classes, without assuming any continuous representative
or additional Sobolev regularity.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Every weak harmonic gradient coordinate has quadratic mean-square
oscillation decay. The constant is independent of the field and both radii.
The weak equation, and not a classical representative, is the input. -/
theorem meanSquare_gradient_oscillation_le_of_dirichlet_eq_zero
    {z : ℝ^n} {R r : ℝ} (U : H¹(ball z R))
    (hweak : ∀ t : H¹₀(ball z R),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i) U, derivCoordCLM i t⟫_ℝ) = 0)
    (hr : 0 < r) (hrR : r ≤ R / 2) (i : Fin n) (c : ℝ) :
    (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
      ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) ≤
      (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2 *
        ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) U x - c‖ ^ 2 := by
  have hR : 0 < R := by linarith
  obtain ⟨u, hu, hbase⟩ := exists_isHarmonicPDE_ae_eq_of_dirichlet_eq_zero
    isOpen_ball U hweak
  have hrep := wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn isOpen_ball U
    (hu.contDiffOn.of_le (by norm_num)) hbase i
  have hharm : LaplacianEquation.IsHarmonicPDE n (∂[i] u) (ball z R) :=
    hu.fderiv_apply isOpen_ball (EuclideanSpace.single i 1)
  have hmem : MemLp (∂[i] u) 2 (volume.restrict (ball z R)) :=
    (Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) U)).ae_eq hrep
  have hsmall := hrep.filter_mono
    (ae_mono (Measure.restrict_mono (ball_subset_ball (hrR.trans (by linarith))) le_rfl))
  have hav : (⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) U y) =
      ⨍ y in ball z r, ∂[i] u y := average_congr hsmall
  have hinner : (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
      ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) =
      ⨍ x in ball z r, ‖∂[i] u x - ⨍ y in ball z r, ∂[i] u y‖ ^ 2 := by
    rw [hav]
    exact average_congr (hsmall.fun_comp (fun t ↦ ‖t - ⨍ y in ball z r, ∂[i] u y‖ ^ 2))
  have houter : (⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) U x - c‖ ^ 2) =
      ⨍ x in ball z R, ‖∂[i] u x - c‖ ^ 2 :=
    average_congr (hrep.fun_comp (fun t ↦ ‖t - c‖ ^ 2))
  rw [hinner, houter]
  exact hharm.meanSquare_oscillation_le hmem hr hrR c

end SobolevSpace.GraphSpace
