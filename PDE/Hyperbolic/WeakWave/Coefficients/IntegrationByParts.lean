/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.LowerOrderDependence
public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts

/-!
# The lower-order bound for weak-wave uniqueness

Spatial integration by parts moves the derivative off the first argument of the drift
form. A `W¹,∞` drift therefore gives the `L² × H¹₀` bound used in Evans's backward-test
proof of uniqueness. The weak Leibniz rule gives the identity on every open domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4 (the form `C[u, v; t]` after
  equation (39)).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Integration by parts bounds a single drift term by the base norm of its first
argument and the Sobolev norm of its second argument. -/
theorem abs_inner_mul_deriv_le_base_left (hΩ : IsOpen Ω) (b : W^{1,∞}(Ω)) (i : Fin n)
    (u v : H¹₀(Ω)) :
    |⟪((b : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) • derivCoordCLM i u, baseCoordCLM v⟫_ℝ| ≤
      (‖(b : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)‖ +
      ‖(b : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)‖) * ‖baseCoordCLM u‖ * ‖v‖ := by
  let B := (b : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)
  let D := (b : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)
  have hibp : ⟪B • derivCoordCLM i u, baseCoordCLM v⟫_ℝ =
        -(⟪B • derivCoordCLM i v, baseCoordCLM u⟫_ℝ +
          ⟪D • baseCoordCLM u, baseCoordCLM v⟫_ℝ) := by
    have h := inner_mul_deriv_add_inner_mul_deriv_H10 hΩ b i u.1 v
    change ⟪B • derivCoordCLM i u, baseCoordCLM v⟫_ℝ + ⟪B • derivCoordCLM i v, baseCoordCLM u⟫_ℝ =
        -⟪D • baseCoordCLM u, baseCoordCLM v⟫_ℝ at h
    linarith only [h]
  change |⟪B • derivCoordCLM i u, baseCoordCLM v⟫_ℝ| ≤ (‖B‖ + ‖D‖) * ‖baseCoordCLM u‖ * ‖v‖
  rw [hibp, abs_neg]
  calc
    _ ≤ |⟪B • derivCoordCLM i v, baseCoordCLM u⟫_ℝ| +
        |⟪D • baseCoordCLM u, baseCoordCLM v⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖B‖ * ‖derivCoordCLM i v‖ * ‖baseCoordCLM u‖ + ‖D‖ * ‖baseCoordCLM u‖ * ‖baseCoordCLM v‖ :=
      add_le_add (Lp.abs_inner_lpSMul_le _ _ _) (Lp.abs_inner_lpSMul_le _ _ _)
    _ ≤ ‖B‖ * ‖v‖ * ‖baseCoordCLM u‖ + ‖D‖ * ‖baseCoordCLM u‖ * ‖v‖ := add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (derivCoordCLM_norm_le i v) (norm_nonneg _)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (baseCoordCLM_norm_le v) (by positivity))
    _ = _ := by ring

/-- A Sobolev drift and bounded potential give the lower-order estimate required by
weak-wave uniqueness, with the `L²` norm on the first argument. -/
theorem abs_lowerOrderForm_le_base_left (hΩ : IsOpen Ω) (b : Fin n → W^{1,∞}(Ω)) (c : DerivLp n ∞ Ω)
    (u v : H¹₀(Ω)) :
    |lowerOrderForm
        (fun i ↦ mulLpLeft ((b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)))
        (mulLpLeft c) u v| ≤
      ((∑ i, (‖(b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)‖ +
        ‖(b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)‖)) + ‖c‖) *
        ‖baseCoordCLM u‖ * ‖v‖ := by
  classical
  change |(∑ i, ⟪((b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
    derivCoordCLM i u, baseCoordCLM v⟫_ℝ) + ⟪c • baseCoordCLM u, baseCoordCLM v⟫_ℝ| ≤ _
  calc
    _ ≤ (∑ i, |⟪((b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        derivCoordCLM i u, baseCoordCLM v⟫_ℝ|) +
        |⟪c • baseCoordCLM u, baseCoordCLM v⟫_ℝ| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
    _ ≤ (∑ i, (‖(b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)‖ +
        ‖(b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)‖) *
        ‖baseCoordCLM u‖ * ‖v‖) + ‖c‖ * ‖baseCoordCLM u‖ * ‖v‖ :=
      add_le_add (Finset.sum_le_sum fun i _ ↦ abs_inner_mul_deriv_le_base_left hΩ (b i) i u v)
        ((Lp.abs_inner_lpSMul_le _ _ _).trans
          (mul_le_mul_of_nonneg_left (baseCoordCLM_norm_le v) (by positivity)))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

end SobolevSpace.GraphSpace
