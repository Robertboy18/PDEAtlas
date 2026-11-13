/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.Polyconvexity.Existence.AffineData

/-!
# Polyconvex minimizers with nonzero affine boundary values

The nonconvex quartic determinant energy has a finite minimizer at both real
exponents `4` and `5 / 2`. All additive shifts are allowed. In particular the
shift by ten uses the strictly negative coercivity constant `β = -1` at
exponent four. The boundary class consists of every Sobolev map whose
geometric trace is the affine map, and the minimizer is compared against all
of them, including infinite-energy competitors.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary.Atlas.UnitBall
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open PDE.CalculusOfVariations
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.Examples.Polyconvexity.Existence

/-- For `q = 4` or `q = 5 / 2` and every constant `c`, the energy of `quarticDensity + c`
has a minimizer among maps with trace `affineMap`. Its energy is finite and equals the
Lebesgue integral of the density. -/
theorem exists_quartic_affine_minimizer (q c : ℝ) (hq : q = 4 ∨ q = 5 / 2) :
    let hq1 : 1 < q := by rcases hq with rfl | rfl <;> norm_num
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
    letI : Boundary.C1ExtensionAtlas 2 (domain 2) :=
      ((hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl).c1ExtensionAtlas
        (isOpen_domain 2) (bounded_domain 2)
    let F := fun t ↦ quarticDensity t + c
    let A := {u : Fin 2 → W^{1,ENNReal.ofReal q}(domain 2) |
      (Trace.C1.vectorTraceLp q u : ℝ^2 → ℝ^2)
        =ᵐ[surfaceMeasure (domain 2)] affineMap}
    let I := vectorWkpIntegral (determinantDensity F)
    ∃ u ∈ A, IsMinOn I A u ∧ I u ≠ ⊤ ∧
      Integrable (fun x ↦ determinantDensity F x
        (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure 2 (domain 2)) ∧
      I u = ((∫ x, determinantDensity F x
        (vectorWkpValueCLM u x, ∇ u x)
          ∂domainMeasure 2 (domain 2) : ℝ) : EReal) := by
  have hq2 : (2 : ℝ) < q := by rcases hq with rfl | rfl <;> norm_num
  have hq1 : 1 < q := lt_trans (by norm_num) hq2
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  let hgraph := (hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl
  let : Boundary.C1ExtensionAtlas 2 (domain 2) :=
    hgraph.c1ExtensionAtlas (isOpen_domain 2) (bounded_domain 2)
  let := isFiniteMeasure_domainMeasure_of_isBounded (bounded_domain 2)
  let F := fun t ↦ quarticDensity t + c
  let β : ℝ := if q = 4 then 9 - c else 19 / 2 - c
  have hF : ContDiff ℝ 1 F := quarticDensity_contDiff.add contDiff_const
  have hconvex (x s : ℝ^2) :
      ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦ F ((x, s), R)) :=
    (quarticDensity_convex x s).add_const c
  have hcoercive (x s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ) :
      (1 / 2 : ℝ) * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ F ((x, s), (P, P.det)) := by
    rcases hq with rfl | rfl
    · simp only [β, F, ite_eq_left rfl]
      linarith [quarticDensity_coercive_four x s P]
    · norm_num only [β, F, show (5 / 2 : ℝ) ≠ 4 by norm_num, ite_false]
      linarith [quarticDensity_coercive_five_halves x s P]
  have hae : (fun x ↦ determinantDensity F x
      (vectorWkpValueCLM (affineData (ENNReal.ofReal q)) x,
        ∇ (affineData (ENNReal.ofReal q)) x))
          =ᵐ[domainMeasure 2 (domain 2)] fun _ ↦ 26 + c := by
    filter_upwards [quarticDensity_affineData_ae (ENNReal.ofReal q)] with x hx
    change determinantDensity quarticDensity x
      (vectorWkpValueCLM (affineData (ENNReal.ofReal q)) x,
        ∇ (affineData (ENNReal.ofReal q)) x) + c = 26 + c
    rw [hx]
  have hfinite : vectorWkpIntegral (determinantDensity F)
      (affineData (ENNReal.ofReal q)) ≠ ⊤ := by
    rw [vectorWkpIntegral_eq_integral ((integrable_const (26 + c)).congr hae.symm)]
    exact EReal.coe_ne_top _
  exact exists_minimizer_determinantWkpIntegral_of_finite_competitor
    (isOpen_domain 2) (bounded_domain 2) hgraph hq2 hF.contDiffOn
    (fun x _ s ↦ hconvex x s) (by norm_num : (0 : ℝ) < 1 / 2)
    (fun x _ s P ↦ hcoercive x s P) affineMap
    ⟨affineData (ENNReal.ofReal q), affineData_trace q, hfinite⟩

end PDE.Examples.Polyconvexity.Existence
