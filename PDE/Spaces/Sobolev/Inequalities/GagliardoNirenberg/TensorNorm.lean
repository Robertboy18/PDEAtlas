/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNorm
public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Smooth

/-!
# Interpolation bounds for full derivative tensors

The coordinate interpolation estimate controls the norm of each complete
Fréchet derivative tensor. This is the form used by the nonlinear higher
chain rule. The dimension enters only through the number of coordinates.
-/

@[expose] public noncomputable section

open PDE (iteratedCoordinateNormSum iteratedPartialDeriv)
open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.GagliardoNirenberg

variable {n : ℕ}

/-- The recursively summed coordinate norms satisfy the triangle inequality
with one contribution for each derivative word. -/
theorem lpNorm_iteratedCoordinateNormSum_le (j : ℕ) {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {M : ℝ}
    (hbound : ∀ α : List (Fin n), α.length = j →
      lpNorm (iteratedPartialDeriv α u) p volume ≤ M) :
    lpNorm (iteratedCoordinateNormSum j u) p volume ≤ (n : ℝ) ^ j * M := by
  induction j generalizing u with
  | zero =>
    simpa only [iteratedPartialDeriv, iteratedCoordinateNormSum,
      lpNorm_norm hu.continuous.aestronglyMeasurable,
      pow_zero, one_mul] using hbound [] rfl
  | succ j ih =>
    have hmem (i : Fin n) :
        MemLp (iteratedCoordinateNormSum j (∂[i] u)) p volume :=
      Continuous.memLp_of_hasCompactSupport
        (PDE.continuous_iteratedCoordinateNormSum (PDE.contDiff_top_partialDeriv hu) j)
        ((huc.iteratedPartialDeriv [i]).iteratedCoordinateNormSum j)
    have hnorm (i : Fin n) :
        lpNorm (iteratedCoordinateNormSum j (∂[i] u)) p volume ≤ (n : ℝ) ^ j * M := by
      apply ih (PDE.contDiff_top_partialDeriv hu) (huc.iteratedPartialDeriv [i])
      intro α hα
      have heq : iteratedPartialDeriv (α ++ [i]) u = iteratedPartialDeriv α (∂[i] u) :=
        funext (PDE.iteratedPartialDeriv_append_single α i u)
      simpa only [heq] using hbound (α ++ [i]) (by simp [hα])
    have heq : iteratedCoordinateNormSum (j + 1) u =
        ∑ i : Fin n, iteratedCoordinateNormSum j (∂[i] u) := by
      ext x
      exact (Finset.sum_apply x _ _).symm
    rw [heq]
    calc
      _ ≤ ∑ i : Fin n, lpNorm (iteratedCoordinateNormSum j (∂[i] u)) p volume :=
        lpNorm_sum_le (fun i _ ↦ hmem i) hp
      _ ≤ ∑ _i : Fin n, (n : ℝ) ^ j * M := Finset.sum_le_sum fun i _ ↦ hnorm i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, pow_succ]; ring

/-- Coordinate interpolation controls the norm of the full derivative tensor.
The statement applies to any exponent at least one. -/
theorem lpNorm_iteratedFDeriv_le_of_coordinate_bounds (j : ℕ) {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {M : ℝ}
    (hbound : ∀ α : List (Fin n), α.length = j →
      lpNorm (iteratedPartialDeriv α u) p volume ≤ M) :
    lpNorm (iteratedFDeriv ℝ j u) p volume ≤ (n : ℝ) ^ j * M := by
  have hmem : MemLp (iteratedCoordinateNormSum j u) p volume :=
    (PDE.continuous_iteratedCoordinateNormSum hu j).memLp_of_hasCompactSupport
      (huc.iteratedCoordinateNormSum j)
  exact (lpNorm_mono_real hmem fun x ↦
    PDE.norm_iteratedFDeriv_le_iteratedCoordinateNormSum j
      (hu.contDiffAt.of_le (by simp))).trans
    (lpNorm_iteratedCoordinateNormSum_le j hu huc hp hbound)

end SobolevSpace.GagliardoNirenberg
