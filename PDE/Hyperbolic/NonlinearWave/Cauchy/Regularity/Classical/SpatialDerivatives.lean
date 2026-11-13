/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.Spaces.Sobolev.Fractional.Integer.ClassicalRepresentation
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder

/-!
# Classical derivatives of the whole-space Sobolev representative

The weak derivative graphs and classical derivatives describe the same
functions above the Sobolev threshold. Uniqueness of weak derivatives first
identifies them almost everywhere; continuity then identifies every point.
This discharges the spatial operator correspondence without assuming any
derivative identity for a chosen representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k r : ℕ}

/-- Classical derivative words are the stored weak derivative rows almost
everywhere, whenever the representative has the corresponding regularity. -/
theorem iteratedPartialDeriv_classicalRepresentative_ae (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (α : List (Fin n)) (hα : α.length + r ≤ k) (hreg : (n : ℝ) < 2 * ((k : ℝ) - α.length))
    (u : W^{k,2}(ℝ^n)) :
    iteratedPartialDeriv α (classicalRepresentativeCLM hk u) =ᵐ[volume]
      baseRepresentative (derivativeWordCLM α hα u) := by
  have hclass := hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn isOpen_univ
    (contDiff_classicalRepresentativeCLM hk hreg u).contDiffOn α le_rfl
  have hbase : baseRepresentative u =ᵐ[domainMeasure n univ]
      (classicalRepresentativeCLM hk u : ℝ^n → ℝ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      (classicalRepresentativeCLM_ae hk u).symm
  have hweak := (u.property.hasWeakDerivativeOn_list α (by omega)).congr_ae
    hbase (Filter.EventuallyEq.refl _ _)
  rw [baseRepresentative_derivativeWordCLM]
  simpa only [domainMeasure, Measure.restrict_univ] using
    HasWeakDerivativeOn.unique_ae isOpen_univ hclass hweak

/-- Above the threshold for the remaining order, classical differentiation
commutes pointwise with the canonical Sobolev representative. -/
theorem iteratedPartialDeriv_classicalRepresentative (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hr : (n : ℝ) < 2 * ((r : ℝ) - 1)) (α : List (Fin n)) (hα : α.length + r ≤ k)
    (u : W^{k,2}(ℝ^n)) :
    iteratedPartialDeriv α (classicalRepresentativeCLM hk u) =
      classicalRepresentativeCLM hr (derivativeWordCLM α hα u) := by
  have hαreal : (α.length : ℝ) + r ≤ k := by exact_mod_cast hα
  have hreg : (n : ℝ) < 2 * ((k : ℝ) - (α.length + 1 : ℕ)) := by
    push_cast
    linarith
  have hcont : Continuous (iteratedPartialDeriv α (classicalRepresentativeCLM hk u)) :=
    (contDiff_iteratedPartialDeriv_of_le
      (contDiff_classicalRepresentativeCLM hk hreg u) α (by omega)).continuous
  exact eq_classicalRepresentativeCLM_of_ae_eq hr _ hcont
    (iteratedPartialDeriv_classicalRepresentative_ae hk α hα (by linarith) u)

/-- The canonical representative carries the weak first partial derivative to
the first classical partial derivative. -/
theorem partialDeriv_classicalRepresentative (hk : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hlow : (n : ℝ) < 2 * ((k : ℝ) - 1)) (i : Fin n) (u : W^{k + 1,2}(ℝ^n)) :
    ∂[i] (classicalRepresentativeCLM hk u : ℝ^n → ℝ) =
      classicalRepresentativeCLM hlow (partialDerivCLM i u) := by
  simpa only [iteratedPartialDeriv, partialDerivCLM] using
    iteratedPartialDeriv_classicalRepresentative hk hlow [i] (by simp; omega) u

/-- The higher weak Laplacian represents the classical Laplacian at
every point of Euclidean space. -/
theorem laplacian_classicalRepresentative (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hr : (n : ℝ) < 2 * ((r : ℝ) - 1)) (h : r + 2 ≤ k) (u : W^{k,2}(ℝ^n)) :
    Δ (classicalRepresentativeCLM hk u : ℝ^n → ℝ) =
      classicalRepresentativeCLM hr (higherOrderLaplacianCLM h u) := by
  have hreal : (r : ℝ) + 2 ≤ k := by exact_mod_cast h
  have hreg : (n : ℝ) < 2 * ((k : ℝ) - 2) := by linarith
  ext x
  have hc : ContDiffAt ℝ 2 (classicalRepresentativeCLM hk u : ℝ^n → ℝ) x :=
    (contDiff_classicalRepresentativeCLM hk hreg u).contDiffAt
  rw [← hc.coordinate_laplacian_eq_laplacian]
  simp only [PDE.laplacian, higherOrderLaplacianCLM, sum_apply, map_sum,
    BoundedContinuousFunction.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact congrFun (iteratedPartialDeriv_classicalRepresentative hk hr [i, i]
    (by simpa [Nat.add_comm] using h) u) x

end PDE.Hyperbolic.NonlinearWave.Cauchy
