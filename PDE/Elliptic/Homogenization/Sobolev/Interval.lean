/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Interval.Graph
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ClassicalZero
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure

/-!
# Sobolev representatives on the one-dimensional cell interval

The domain uses the Euclidean coordinates of the Sobolev graph spaces.
The classical zero-trace theorem constructs `H¹₀` representatives from zero endpoint
values, retaining both the value and first-derivative representatives.
-/

@[expose] public noncomputable section

open Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal

namespace PDE.Elliptic.Homogenization

/-- The open unit interval in the Euclidean coordinates used by the Sobolev API. -/
def unitInterval : Set (ℝ^1) := {x | 0 < x 0 ∧ x 0 < 1}

/-- The interval domain is open. -/
theorem isOpen_unitInterval : IsOpen unitInterval :=
  isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous

/-- The interval domain is bounded. -/
theorem isBounded_unitInterval : Bornology.IsBounded unitInterval := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, fun x hx ↦ ?_⟩
  have he : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_one, Real.norm_eq_abs]
    rw [Real.sqrt_sq_eq_abs, abs_abs]
  rw [he, abs_of_pos hx.1]
  exact hx.2.le

/-- The two endpoints supply the smooth graph-boundary predicate. -/
theorem hasC1GraphBoundary_unitInterval : Boundary.HasC1GraphBoundary unitInterval :=
  (Boundary.Atlas.Interval.hasContDiffGraphBoundary_Ioo zero_lt_one 1).hasC1GraphBoundary le_rfl

/-- The only coordinate derivative of a scalar lift is its ordinary derivative. -/
theorem partialDeriv_lift {g : ℝ → ℝ} (hg : Differentiable ℝ g) (i : Fin 1) (x : ℝ^1) :
    (∂[i] (fun y : ℝ^1 ↦ g (y 0))) x = deriv g (x 0) := by
  have hd := (hg (x 0)).hasDerivAt.comp_hasFDerivAt x
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt)
  have hi : i = 0 := Subsingleton.elim _ _
  change HasFDerivAt (fun y : ℝ^1 ↦ g (y 0)) _ x at hd
  rw [partialDeriv, hd.fderiv]
  simp [hi]

/-- A continuous scalar function lifted to an `Lᵖ` class on the unit interval. -/
def continuousLiftLp {g : ℝ → ℝ} (hg : Continuous g) (p : ℝ≥0∞) :
    DerivLp 1 p unitInterval :=
  (ContDiffUpToBoundary.of_contDiff
    (contDiff_zero.mpr (hg.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous))
    isBounded_unitInterval).toLp isOpen_unitInterval isBounded_unitInterval p

/-- The lifted `Lᵖ` class has the prescribed continuous representative. -/
theorem continuousLiftLp_ae {g : ℝ → ℝ} (hg : Continuous g) (p : ℝ≥0∞) :
    (continuousLiftLp hg p : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval] fun x ↦ g (x 0) :=
  ContDiffUpToBoundary.toLp_coeFn _ _ _ _

/-- Zero classical endpoint values construct an element of the `H¹₀` space. -/
theorem exists_H10_of_endpoints {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hzero : u 0 = 0) (hone : u 1 = 0) :
    ∃ U : H¹₀(unitInterval),
      (baseCoordCLM U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval] (fun x ↦ u (x 0)) ∧
      ∀ i, (derivCoordCLM i U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ deriv u (x 0)) := by
  have hc : ContDiff ℝ 1 (fun x : ℝ^1 ↦ u (x 0)) :=
    hu.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  obtain ⟨U, hU, hd⟩ :=
    (ContDiffUpToBoundary.of_contDiff hc isBounded_unitInterval
      ).exists_H10_of_eq_zero_on_frontier isOpen_unitInterval isBounded_unitInterval
        hasC1GraphBoundary_unitInterval hc.continuous.continuousOn (by
          intro x hx
          rcases Boundary.Atlas.Interval.eq_endpoint_of_mem_frontier_Ioo hx with h | h
          · simpa only [h] using hzero
          · simpa only [h] using hone)
  refine ⟨U, hU, fun i ↦ ?_⟩
  filter_upwards [hd i] with x hx
  rw [hx, partialDeriv_lift (hu.differentiable one_ne_zero)]

end PDE.Elliptic.Homogenization
