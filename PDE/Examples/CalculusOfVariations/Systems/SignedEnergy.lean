/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Existence
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A coupled signed matrix energy

The density `‖P‖² + trace(P)² - 2` couples the two diagonal gradient entries.
Its quadratic coercivity and gradient convexity give a signed minimizer with
zero geometric trace on every bounded open `C¹` domain in the plane.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.CalculusOfVariations
open scoped ENNReal NNReal Matrix.Norms.Frobenius Sobolev

namespace PDE.Examples.VariationalSystems

/-- A quadratic matrix density with coupling between the diagonal entries. -/
def coupledDensity (t : (ℝ^2 × ℝ^2) × Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ‖Matrix.euclideanEquiv t.2‖ ^ 2 + Matrix.trace t.2 ^ 2 - 2

/-- The coupled density is continuously differentiable everywhere. -/
theorem coupledDensity_contDiff : ContDiff ℝ 1 coupledDensity := by
  have htrace : ContDiff ℝ 1 (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ Matrix.trace P) :=
    (Matrix.traceLinearMap (Fin 2) ℝ ℝ).toContinuousLinearMap.contDiff
  exact (((contDiff_norm_sq ℝ).comp
    (Matrix.euclideanEquiv.contDiff.comp contDiff_snd)).add
      ((htrace.comp contDiff_snd).pow 2)).sub contDiff_const

/-- `coupledDensity` is convex in the matrix variable. -/
theorem coupledDensity_convex (x s : ℝ^2) :
    ConvexOn ℝ univ (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ coupledDensity ((x, s), P)) := by
  have hnorm : ConvexOn ℝ univ (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ ‖P‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
  have htrace : ConvexOn ℝ univ
      (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ Matrix.trace P ^ 2) := by
    simpa only [Function.comp_def, Matrix.traceLinearMap_apply, preimage_univ] using
      (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 from ⟨1, rfl⟩)).comp_linearMap
      (Matrix.traceLinearMap (Fin 2) ℝ ℝ)
  have hsum : ConvexOn ℝ univ
      (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ ‖P‖ ^ 2 + Matrix.trace P ^ 2 + -2) :=
    (hnorm.add htrace).add_const (-2)
  simpa only [coupledDensity, Matrix.norm_euclideanEquiv, sub_eq_add_neg] using hsum

/-- The signed energy of `coupledDensity` has a minimizer among maps with zero trace. -/
theorem coupled_zero_trace_minimizer {Ω : Set (ℝ^2)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) :
    letI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
    letI : Boundary.C1ExtensionAtlas 2 Ω := hgraph.c1ExtensionAtlas hopen hbounded
    ∃ u : Fin 2 → W^{1,ENNReal.ofReal 2}(Ω),
      Trace.C1.vectorTraceLp 2 u = 0 ∧
      ∀ v : Fin 2 → W^{1,ENNReal.ofReal 2}(Ω),
        Trace.C1.vectorTraceLp 2 v = 0 →
        vectorWkpIntegral
          (fun x z ↦ coupledDensity ((x, z.1), Matrix.euclideanEquiv.symm z.2)) u ≤
        vectorWkpIntegral
          (fun x z ↦ coupledDensity ((x, z.1), Matrix.euclideanEquiv.symm z.2)) v := by
  let : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  let : Boundary.C1ExtensionAtlas 2 Ω := hgraph.c1ExtensionAtlas hopen hbounded
  have hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ),
      1 * ‖P‖ ^ (2 : ℝ) - 2 ≤ coupledDensity ((x, s), P) := by
    intro x _ s P
    simp only [coupledDensity, Matrix.norm_euclideanEquiv, Real.rpow_two, one_mul]
    linarith [sq_nonneg (Matrix.trace P)]
  exact exists_minimizer_matrixWkpIntegral_of_nonempty_trace hopen hbounded hgraph
      (by norm_num : (1 : ℝ) < 2) coupledDensity_contDiff.contDiffOn
      (fun x _ s ↦ coupledDensity_convex x s) (by norm_num : (0 : ℝ) < 1)
      hcoercive 0 ⟨0, map_zero _⟩

end PDE.Examples.VariationalSystems
