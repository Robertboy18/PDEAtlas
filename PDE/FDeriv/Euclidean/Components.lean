/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Derivatives of Euclidean vector fields from their components

A map `F` into `ℝⁿ` is the sum of its components times the standard basis vectors, so every
iterated derivative of `F` is bounded by the sum of the iterated derivatives of the components:
`‖DᵏF(x)‖ ≤ Σᵢ ‖DᵏFᵢ(x)‖`. Hence bounds and `Lᵖ` membership of the derivatives pass from the
components to the field.
-/

@[expose] public section

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace PDE

/-- The iterated derivatives of a smooth map into `ℝⁿ` are bounded by the sum of those of its
components. -/
theorem norm_iteratedFDeriv_le_sum_component {F : E → EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hF : ContDiff ℝ k F) (x : E) :
    ‖iteratedFDeriv ℝ k F x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ k (fun y ↦ F y i) x‖ := by
  let L : Fin n → ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) := fun i ↦
    (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1 : ℝ))
  have hL (i : Fin n) : ‖L i‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    simp
  have hFi (i : Fin n) : ContDiff ℝ k (fun y ↦ F y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  have hsum : F = fun y ↦ ∑ i, L i (F y i) := by
    funext y
    ext j
    simp [L, Pi.single_apply]
  have hcomp (i : Fin n) : ContDiff ℝ k (fun y ↦ L i (F y i)) := (L i).contDiff.comp (hFi i)
  calc ‖iteratedFDeriv ℝ k F x‖
      = ‖∑ i, iteratedFDeriv ℝ k (fun y ↦ L i (F y i)) x‖ := by
        conv_lhs => rw [hsum]
        rw [iteratedFDeriv_sum fun i _ ↦ hcomp i, Finset.sum_apply]
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ k (fun y ↦ L i (F y i)) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ k (fun y ↦ F y i) x‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc ‖iteratedFDeriv ℝ k (fun y ↦ L i (F y i)) x‖
            ≤ ‖L i‖ * ‖iteratedFDeriv ℝ k (fun y ↦ F y i) x‖ :=
              (L i).norm_iteratedFDeriv_comp_left (hFi i).contDiffAt le_rfl
          _ ≤ 1 * ‖iteratedFDeriv ℝ k (fun y ↦ F y i) x‖ := by gcongr; exact hL i
          _ = _ := one_mul _

/-- A smooth map into `ℝⁿ` whose components have their `k`-th derivatives in `Lᵖ` has its `k`-th
derivative in `Lᵖ`. -/
theorem memLp_iteratedFDeriv_of_component [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure E} {F : E → EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hF : ContDiff ℝ k F) {p : ENNReal}
    (h : ∀ i, MemLp (iteratedFDeriv ℝ k (fun y ↦ F y i)) p μ) :
    MemLp (iteratedFDeriv ℝ k F) p μ := by
  have hsum : MemLp (fun x ↦ ∑ i, ‖iteratedFDeriv ℝ k (fun y ↦ F y i) x‖) p μ :=
    memLp_finsetSum _ fun i _ ↦ (h i).norm
  refine hsum.of_le (hF.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]
  exact norm_iteratedFDeriv_le_sum_component hF x

/-- A smooth map into `ℝⁿ` whose components have bounded `k`-th derivatives has a bounded `k`-th
derivative. -/
theorem exists_bound_iteratedFDeriv_of_component {F : E → EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hF : ContDiff ℝ k F) (h : ∀ i, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (fun y ↦ F y i) x‖ ≤ C) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C := by
  choose C hC using h
  exact ⟨∑ i, C i, fun x ↦ (norm_iteratedFDeriv_le_sum_component hF x).trans
    (Finset.sum_le_sum fun i _ ↦ hC i x)⟩

end PDE
