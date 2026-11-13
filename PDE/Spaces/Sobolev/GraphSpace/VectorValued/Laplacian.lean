/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives

/-!
# The Laplacian of a Banach-valued Sobolev function

The sum of the diagonal second weak derivatives lowers Sobolev order by two.
With `open scoped Sobolev Laplacian`, write `Δ u` for the resulting Sobolev
function. The sign is the usual positive sum `∑ i, ∂[i] (∂[i] u)`.

This uses the same derivative coordinates as the rest of the Sobolev graph.
It works on every open domain, for Banach codomains and both normed exponent
endpoints. The name `laplacianCLM` is available when composing bounded operators.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Laplacian

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The sum of the diagonal second weak derivatives as a bounded Sobolev operator. -/
def laplacianCLM : W^{k + 2,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; F) :=
  ∑ i : Fin n, (partialDerivCLM i).comp (partialDerivCLM i)

/-- Mathlib's `Δ` notation lowers the order of a Banach-valued Sobolev function by two. -/
instance instLaplacian : Laplacian (W^{k + 2,p}(Ω; F)) (W^{k,p}(Ω; F)) where
  laplacian u := laplacianCLM u

/-- The notation applies the bounded weak Laplacian. -/
@[simp] theorem laplacian_eq_laplacianCLM (u : W^{k + 2,p}(Ω; F)) :
    Δ u = laplacianCLM u :=
  rfl

/-- The Laplacian is the sum of the diagonal second weak partial derivatives. -/
theorem laplacian_eq_sum (u : W^{k + 2,p}(Ω; F)) :
    Δ u = ∑ i : Fin n, ∂[i] (∂[i] u) := by
  simp only [laplacian_eq_laplacianCLM, laplacianCLM, sum_apply,
    ContinuousLinearMap.comp_apply]

/-- Each derivative coordinate of the Laplacian is the sum of the corresponding
diagonal second derivative coordinates of the original function. -/
theorem laplacian_coordinate (u : W^{k + 2,p}(Ω; F)) (a : DerivIndex n k) :
    (Δ u).val a = ∑ i : Fin n,
      u.val (derivativeWordIndex [i, i] (by simp [Nat.add_comm]) a) := by
  change coordinateCLM a (Δ u) = _
  rw [laplacian_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change coordinateCLM a (((derivativeWordCLM [i] _).comp
    (derivativeWordCLM [i] _)) u) = _
  rw [derivativeWordCLM_comp]
  rfl

/-- The representative of every Laplacian coordinate has the expected sum formula
almost everywhere. -/
theorem laplacian_coordinate_ae (u : W^{k + 2,p}(Ω; F)) (a : DerivIndex n k) :
    ((Δ u).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω] fun x ↦
      ∑ i : Fin n, u.val (derivativeWordIndex [i, i] (by simp [Nat.add_comm]) a) x := by
  rw [laplacian_coordinate]
  exact Lp.coeFn_fun_finsetSum _ _

/-- The Laplacian is bounded by the spatial dimension in the remaining Sobolev norm. -/
theorem norm_laplacian_le (u : W^{k + 2,p}(Ω; F)) :
    ‖Δ u‖ ≤ n * ‖u‖ := by
  rw [laplacian_eq_sum]
  calc
    ‖∑ i : Fin n, ∂[i] (∂[i] u)‖ ≤ ∑ i : Fin n, ‖∂[i] (∂[i] u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖u‖ := Finset.sum_le_sum fun i _ ↦
      (norm_partialDeriv_le i (∂[i] u)).trans (norm_partialDeriv_le i u)
    _ = n * ‖u‖ := by simp

/-- The bounded Laplacian has operator norm at most the spatial dimension. -/
theorem norm_laplacianCLM_le :
    ‖laplacianCLM (F := F) (k := k) (p := p) (Ω := Ω)‖ ≤ n :=
  ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _) norm_laplacian_le

end SobolevSpace.VectorValued
