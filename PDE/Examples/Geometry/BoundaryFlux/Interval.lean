/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Closure
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.UnitBall
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# One-dimensional Gauss–Green with unit endpoint masses

For the cubic field `x³+x` on the unit interval, zero-dimensional Hausdorff
measure assigns mass one to each endpoint. The intrinsic normals give
outward flux two at each end, and hence total flux four.
-/

@[expose] public noncomputable section

namespace PDE.Examples.BoundaryFlux.Interval

open Set Metric MeasureTheory SobolevSpace Boundary Boundary.Flux Trace.C1
open Geometry.SurfaceMeasure

/-- A point of the one-dimensional Euclidean space. -/
def point (a : ℝ) : ℝ^1 := EuclideanSpace.single 0 a

/-- The frontier of the unit ball in `ℝ^1` consists of the two endpoints. -/
theorem frontier_unitBall :
    frontier (ball (0 : ℝ^1) 1) = {point (-1)} ∪ {point 1} := by
  ext x
  simp only [frontier_ball (0 : ℝ^1) one_ne_zero, mem_sphere, dist_zero_right,
    mem_union, mem_singleton_iff]
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
    simpa only [Fin.sum_univ_one] using EuclideanSpace.real_norm_sq_eq x
  constructor
  · intro hx
    have hcases : x 0 = -1 ∨ x 0 = 1 := by
      rw [hx] at hnorm
      have hz : (x 0 + 1) * (x 0 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcases with hx | hx
    · left
      ext i
      fin_cases i
      simpa [point] using hx
    · right
      ext i
      fin_cases i
      simpa [point] using hx
  · rintro (rfl | rfl) <;> simp [point, PiLp.norm_single]

/-- A nonconstant polynomial field whose two endpoint fluxes do not cancel. -/
def cubicField (x : ℝ^1) : ℝ^1 := (x 0 ^ 3 + x 0) • point 1

/-- Its first derivative exists globally. -/
theorem contDiff_cubicField : ContDiff ℝ 1 cubicField := by
  unfold cubicField
  have hf : ContDiff ℝ 1 (fun x : ℝ^1 ↦ x 0 ^ 3 + x 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff.pow 3).add
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  exact hf.smul (contDiff_const (c := point 1))

/-- The divergence of the cubic field. -/
theorem divergence_cubicField (x : ℝ^1) :
    ∇· cubicField x = 3 * x 0 ^ 2 + 1 := by
  simp only [divergence, Fin.sum_univ_one, cubicField, PiLp.smul_apply, point,
    PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  cas

/-- Zero-dimensional Hausdorff measure gives each endpoint mass one. -/
theorem hausdorff_endpoint_mass (a : ℝ) :
    Measure.euclideanHausdorffMeasure (0 : ℕ) ({point a} : Set (ℝ^1)) = 1 := by
  rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]

/-- The boundary flux and the volume integral of the divergence both equal four.
The atlas comes from the smooth graph boundary of the ball. -/
theorem cubic_flux_and_volume :
    let hg : HasC1GraphBoundary (ball (0 : ℝ^1) 1) :=
      (Atlas.UnitBall.hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl
    letI := hg.c1ExtensionAtlas isOpen_ball isBounded_ball
    (∫ x, normalFlux (Ω := ball (0 : ℝ^1) 1) cubicField x
      ∂surfaceMeasure (ball (0 : ℝ^1) 1)) = 4 ∧
      (∫ x in ball (0 : ℝ^1) 1, (3 * x 0 ^ 2 + 1 : ℝ)) = 4 := by
  let hg : HasC1GraphBoundary (ball (0 : ℝ^1) 1) :=
    (Atlas.UnitBall.hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl
  let := hg.c1ExtensionAtlas isOpen_ball isBounded_ball
  have hmem (a : ℝ) (ha : a = -1 ∨ a = 1) :
      point a ∈ frontier (ball (0 : ℝ^1) 1) := by
    rw [frontier_unitBall]
    rcases ha with rfl | rfl <;> simp
  have hflux (a : ℝ) (ha : a = -1 ∨ a = 1) :
      normalFlux (Ω := ball (0 : ℝ^1) 1) cubicField (point a) = 2 := by
    rw [normalFlux_eq_inner _ (hmem a ha), outwardUnitNormal_unitBall]
    rcases ha with rfl | rfl <;>
      norm_num [cubicField, point, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        Fin.sum_univ_one]
  have hsurface :
      (∫ x, normalFlux (Ω := ball (0 : ℝ^1) 1) cubicField x
        ∂surfaceMeasure (ball (0 : ℝ^1) 1)) = 4 := by
    change (∫ x in frontier (ball (0 : ℝ^1) 1),
      normalFlux (Ω := ball (0 : ℝ^1) 1) cubicField x
        ∂Measure.euclideanHausdorffMeasure 0) = 4
    rw [frontier_unitBall, setIntegral_union]
    · simp only [integral_singleton, measureReal_def, hausdorff_endpoint_mass,
        ENNReal.toReal_one, one_smul, hflux (-1) (Or.inl rfl), hflux 1 (Or.inr rfl)]
      norm_num
    · simp only [disjoint_singleton_left, mem_singleton_iff]
      intro heq
      have h := congrArg (fun x : ℝ^1 ↦ x 0) heq
      norm_num [point] at h
    · exact measurableSet_singleton _
    · exact integrableOn_singleton (hx := by rw [hausdorff_endpoint_mass]; exact ENNReal.one_lt_top)
    · exact integrableOn_singleton (hx := by rw [hausdorff_endpoint_mass]; exact ENNReal.one_lt_top)
  refine ⟨hsurface, ?_⟩
  have hgg := integral_divergence_eq_normalFlux hg contDiff_cubicField
  simpa only [divergence_cubicField, hsurface] using hgg

end PDE.Examples.BoundaryFlux.Interval
