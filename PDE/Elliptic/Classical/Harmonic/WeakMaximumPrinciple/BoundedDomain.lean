/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Elliptic.Classical.MaximumPrinciple.Weak

/-!
# Harmonic comparison on bounded open domains

The variable-coefficient weak maximum principle applies to the coordinate frame
with zero drift and potential. This gives harmonic comparison without any
boundary regularity or connectedness assumption.
-/

@[expose] public section

open PDE (laplacian)

open Set

namespace LaplacianEquation

/-- A boundary upper bound for a harmonic function controls the closure of any
bounded open domain. The bound may have either sign. -/
theorem IsHarmonicPDE.le_on_closure_of_boundary_le
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)} {M : ℝ}
    (hu : IsHarmonicPDE n u U) (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hcont : ContinuousOn u (closure U))
    (hboundary : ∀ x ∈ frontier U, u x ≤ M) :
    ∀ x ∈ closure U, u x ≤ M := by
  classical
  let i : Fin n := ⟨0, Fact.out⟩
  let σ : ℝ^n → Fin n → ℝ^n := fun _ j ↦ EuclideanSpace.single j 1
  have hcompact : IsCompact (closure U) :=
    hUbdd.isCompact_closure
  apply EllipticMaximum.subsolution_le_of_boundary_le_of_nonneg_mul hUopen hcompact
    σ (fun _ ↦ 0) (fun _ ↦ 0) (EuclideanSpace.proj i) (α := 1) (B := 0)
    zero_lt_one
  · intro x _
    simp [σ, EuclideanSpace.proj]
  · simp
  · simp
  · simp
  · exact hcont
  · exact fun x hx ↦ hu.contDiffAt_of_isOpen hUopen hx
  · intro x hx
    have hf := hu.contDiffAt_of_isOpen hUopen hx
    have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hsecond (j : Fin n) :
        PDE.Analysis.secondDirectionalDerivative u x (σ x j) =
          (∂[j] (∂[j] u)) x := by
      rw [PDE.Analysis.secondDirectionalDerivative_eq_fderiv hf]
      change ((fderiv ℝ (fderiv ℝ u) x) (σ x j)) (σ x j) =
        (fderiv ℝ (fun y ↦ fderiv ℝ u y (σ x j)) x) (σ x j)
      rw [fderiv_clm_apply hd (differentiableAt_const _)]
      simp
    simp only [EllipticMaximum.factoredOperator, hsecond, map_zero, zero_mul, add_zero]
    change -laplacian u x ≤ 0
    rw [hu.laplacian_eq_zero hx, neg_zero]
  · exact hboundary

end LaplacianEquation
