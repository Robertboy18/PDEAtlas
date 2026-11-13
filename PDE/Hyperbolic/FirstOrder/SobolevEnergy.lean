/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.MatrixEnergy

/-!
# Transport energy for symmetric Sobolev coefficient matrices

Summing polarized integration by parts over symmetric W1,infinity coefficient entries
identifies the spatial transport energy with half the quadratic pairing against the
differentiated coefficient matrix. Its upper bound uses only the L² norms of the fields
and the L∞ norms of the coefficient derivatives, without H1 norms of the fields.

This is the integration by parts in step 2 of the proof of Theorem 2 in Evans, §7.3.2, which uses
the symmetry of the coefficient matrices.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, proof of Theorem 2, step 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The unmollified symmetric transport drift is one-sided bounded in the L2 norm of state
differences. All fields lie in whole-space H1, and coefficient symmetry is equality of the
base L-infinity classes. The finite component type may be empty. -/
theorem symmetric_system_transport_difference_energy_le {n : ℕ} {ι : Type*} [Fintype ι]
    (A : Fin n → ι → ι → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, (A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    (U V : ι → H¹(ℝ^n)) :
    let base := fun W : ι → H¹(ℝ^n) ↦
      WithLp.toLp 2 (fun p ↦ wkpCoordinateCLM (baseIndex n 1) (W p));
    let drift := fun W : ι → H¹(ℝ^n) ↦
      WithLp.toLp 2 (fun p ↦ -(∑ j, ∑ q,
        ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          wkpCoordinateCLM (singleDerivIndex n j) (W q)));
    2 * ⟪drift U - drift V, base U - base V⟫_ℝ ≤
      (∑ j, ∑ p, ∑ q,
        ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖) *
          ‖base U - base V‖ ^ 2 := by
  classical
  let W : ι → H¹(ℝ^n) := fun p ↦ U p - V p
  let w := fun p ↦ wkpCoordinateCLM (baseIndex n 1) (W p)
  let dw := fun j p ↦ wkpCoordinateCLM (singleDerivIndex n j) (W p)
  let c := fun j p q ↦ (A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let dc := fun j p q ↦ (A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)
  have hrow (j : Fin n) : -(∑ p, ∑ q, ⟪c j p q • dw j q, w p⟫_ℝ) ≤
        (1 / 2 : ℝ) * (∑ p, ∑ q, ‖dc j p q‖) * (∑ p, ‖w p‖ ^ 2) :=
    symmetric_matrix_transport_energy_le (A j) (hA j) j W
  have hsum : (∑ p, ⟪-(∑ j, ∑ q, c j p q • dw j q), w p⟫_ℝ) ≤
        (1 / 2 : ℝ) * (∑ j, ∑ p, ∑ q, ‖dc j p q‖) * (∑ p, ‖w p‖ ^ 2) := by
    calc
      _ = ∑ j, -(∑ p, ∑ q, ⟪c j p q • dw j q, w p⟫_ℝ) := by
        simp only [inner_neg_left, sum_inner, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
      _ ≤ ∑ j, (1 / 2 : ℝ) * (∑ p, ∑ q, ‖dc j p q‖) * (∑ p, ‖w p‖ ^ 2) :=
        Finset.sum_le_sum fun j _ ↦ hrow j
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hdrift (p : ι) : -(∑ j, ∑ q, c j p q • wkpCoordinateCLM (singleDerivIndex n j) (U q)) -
        (-(∑ j, ∑ q, c j p q • wkpCoordinateCLM (singleDerivIndex n j) (V q))) =
          -(∑ j, ∑ q, c j p q • dw j q) := by
    change -(∑ j, ∑ q, mulLpLeft (c j p q) (wkpCoordinateCLM (singleDerivIndex n j) (U q))) -
        (-(∑ j, ∑ q, mulLpLeft (c j p q) (wkpCoordinateCLM (singleDerivIndex n j) (V q)))) =
            -(∑ j, ∑ q, mulLpLeft (c j p q) (dw j q))
    simp only [dw, W, map_sub, Finset.sum_sub_distrib]
    abel
  dsimp only
  simp only [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, PiLp.sub_apply]
  change 2 * (∑ p, ⟪-(∑ j, ∑ q, c j p q • wkpCoordinateCLM (singleDerivIndex n j) (U q)) -
      (-(∑ j, ∑ q, c j p q • wkpCoordinateCLM (singleDerivIndex n j) (V q))),
      wkpCoordinateCLM (baseIndex n 1) (U p) - wkpCoordinateCLM (baseIndex n 1) (V p)⟫_ℝ) ≤
      (∑ j, ∑ p, ∑ q, ‖dc j p q‖) * ∑ p, ‖wkpCoordinateCLM (baseIndex n 1) (U p) -
          wkpCoordinateCLM (baseIndex n 1) (V p)‖ ^ 2
  simp_rw [hdrift, ← map_sub]
  change 2 * (∑ p, ⟪-(∑ j, ∑ q, c j p q • dw j q), w p⟫_ℝ) ≤
    (∑ j, ∑ p, ∑ q, ‖dc j p q‖) * ∑ p, ‖w p‖ ^ 2
  linarith only [hsum]

end SobolevSpace.GraphSpace
