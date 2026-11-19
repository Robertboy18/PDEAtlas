/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.Constraints.Determinant.Quartic

/-!
# Determinant-one minimizers with a nonaffine prescribed trace

On the three-dimensional unit ball, the shear supplies a finite admissible
map. The existence theorem therefore gives a determinant-one minimizer
of the signed quartic energy among all maps with this geometric trace.
The minimizer exists for every exponent `3 < q ≤ 4` (`quartic_shear_minimizer`),
and at exponent four also for a strictly negative lower shift
(`positive_quartic_shear_minimizer`).
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.CalculusOfVariations
open SobolevSpace.Boundary.Atlas.UnitBall
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.Examples.Constraints.Determinant

/-- The determinant-one class with the nonaffine shear as boundary trace. -/
def shearClass (q : ℝ) (hq : 1 < q) :
    Set (Fin 3 → W^{1,ENNReal.ofReal q}(domain 3)) := by
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  letI : Boundary.C1ExtensionAtlas 3 (domain 3) :=
    ((hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl).c1ExtensionAtlas
      (isOpen_domain 3) (bounded_domain 3)
  exact {u |
    (Trace.C1.vectorTraceLp q u : ℝ^3 → ℝ^3) =ᵐ[surfaceMeasure (domain 3)] shear ∧
    ∀ᵐ x ∂domainMeasure 3 (domain 3),
      (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex 3 j) (u i) x).det = 1}

/-- The shear itself belongs to this class. -/
theorem shearData_mem_shearClass (q : ℝ) (hq : 1 < q) :
    shearData (ENNReal.ofReal q) ∈ shearClass q hq := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  exact ⟨shearData_trace q, shearData_det_ae _⟩

/-- The signed quartic energy, as an extended-real integral. -/
def shearEnergy (q : ℝ) (hq : 1 < q) (β : ℝ) :
    (Fin 3 → W^{1,ENNReal.ofReal q}(domain 3)) → EReal := by
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  exact vectorWkpIntegral (fun x z ↦ quarticDensity β (Matrix.euclideanEquiv.symm z.2, x))

/-- For `3 < q ≤ 4`, the quartic energy has a minimizer of finite energy among
determinant-one maps with trace `shear`. -/
theorem quartic_shear_minimizer {q : ℝ} (hq : 3 < q) (hq4 : q ≤ 4) (β : ℝ) :
    ∃ u ∈ shearClass q (by linarith),
      IsMinOn (shearEnergy q (by linarith) β) (shearClass q (by linarith)) u ∧
        shearEnergy q (by linarith) β u ≠ ⊤ := by
  have hq1 : 1 < q := by linarith
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  have hcoercive : ∀ x ∈ domain 3, ∀ P : Matrix (Fin 3) (Fin 3) ℝ,
      1 * ‖Matrix.euclideanEquiv P‖ ^ q - (β + 1) ≤ quarticDensity β (P, x) :=
    fun x _ P ↦ quarticDensity_coercive β (by linarith) hq4 x P
  obtain ⟨u, hu, hmin, hfinite, _, _⟩ :=
    exists_minimizer_matrixWkpIntegral_det_eq_one_of_finite_competitor
      (d := 2) (isOpen_domain 3) (bounded_domain 3)
      ((hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl) hq
      ((quarticDensity_contDiff 3 β).of_le (by simp)).contDiffOn
      (fun x _ ↦ quarticDensity_convex β x) (by norm_num : (0 : ℝ) < 1)
      hcoercive shear
      ⟨shearData (ENNReal.ofReal q), shearData_mem_shearClass q hq1,
        quarticDensity_shearData_finite β _⟩
  exact ⟨u, hu, hmin, hfinite⟩

/-- At exponent four, the density `‖P‖⁴ + 2`, with coercivity shift `-2`, has a
minimizer in the shear class. -/
theorem positive_quartic_shear_minimizer :
    ∃ u ∈ shearClass 4 (by norm_num),
      IsMinOn (shearEnergy 4 (by norm_num) (-2)) (shearClass 4 (by norm_num)) u := by
  let : Fact (1 ≤ ENNReal.ofReal 4) := ⟨by norm_num⟩
  exact exists_minimizer_matrixWkpIntegral_of_nonempty_trace_det_eq_one
    (d := 2) (isOpen_domain 3) (bounded_domain 3)
    ((hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl)
    (by norm_num : (3 : ℝ) < 4)
    ((quarticDensity_contDiff 3 (-2)).of_le (by simp)).contDiffOn
    (fun x _ ↦ quarticDensity_convex (-2) x) (by norm_num : (0 : ℝ) < 1)
    (fun x _ P ↦ quarticDensity_coercive_four (-2) x P)
    shear ⟨shearData (ENNReal.ofReal 4), shearData_mem_shearClass 4 (by norm_num)⟩

end PDE.Examples.Constraints.Determinant
