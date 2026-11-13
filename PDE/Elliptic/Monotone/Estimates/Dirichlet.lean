/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PrincipalForms
public import PDE.Analysis.Scalar.QuadraticBound

/-!
# A homogeneous Dirichlet estimate from gradient coercivity

Testing the weak equation against the solution controls its gradient energy.
Bounded-domain Poincaré then controls the full H¹ norm by the L² load.
The estimate uses only the coercive flux pairing, so it does not require
that the flux be a derivative of a potential.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A coercive gradient pairing and the energy identity imply a full
`H¹₀` bound by the `L²` load. The constant precedes all fields and depends
only on the coercivity coefficient and the bounded domain. -/
theorem exists_H10_norm_bound_of_gradient_coercivity
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (u : H¹₀(Ω))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
    (∀ᵐ x ∂domainMeasure n Ω,
      θ * ‖∇ (u : H¹(Ω)) x‖ ^ 2 ≤ ⟪Lp.euclideanTuple q x, ∇ (u : H¹(Ω)) x⟫) →
    (∑ i, ⟪q i, derivCoordCLM i u⟫) = ⟪f, baseCoordCLM u⟫ →
    ‖u‖ ≤ M * ‖f‖ := by
  obtain ⟨k, hk, hP⟩ := dirichletForm_isCoercive hn hbounded
  have hθk : 0 < θ * k := mul_pos hθ hk
  refine ⟨1 + 1 / (θ * k), by positivity, ?_⟩
  intro u q f hcoercive henergy
  have hgrad : k * ‖u‖ ^ 2 ≤ ‖∇ (u : H¹(Ω))‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (∇ (u : H¹(Ω))),
      ← dirichletForm_eq_inner_gradient]
    simpa only [pow_two, mul_assoc] using hP u
  have hint : Integrable (fun x ↦ ‖∇ (u : H¹(Ω)) x‖ ^ 2) (domainMeasure n Ω) := by
    simpa only [real_inner_self_eq_norm_sq] using
      L2.integrable_inner (𝕜 := ℝ) (∇ (u : H¹(Ω))) (∇ (u : H¹(Ω)))
  have hnorm : (∫ x, ‖∇ (u : H¹(Ω)) x‖ ^ 2 ∂domainMeasure n Ω) =
      ‖∇ (u : H¹(Ω))‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.inner_def (𝕜 := ℝ) (∇ (u : H¹(Ω))) (∇ (u : H¹(Ω)))).symm
  have hpoint : θ * ‖∇ (u : H¹(Ω))‖ ^ 2 ≤
      ⟪Lp.euclideanTuple q, ∇ (u : H¹(Ω))⟫ := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, θ * ‖∇ (u : H¹(Ω)) x‖ ^ 2 ∂domainMeasure n Ω := by
        rw [integral_const_mul, hnorm]
      _ ≤ _ := integral_mono_ae (hint.const_mul θ)
        (L2.integrable_inner (𝕜 := ℝ) (Lp.euclideanTuple q) (∇ (u : H¹(Ω)))) hcoercive
  have hpair : ⟪Lp.euclideanTuple q, ∇ (u : H¹(Ω))⟫ = ⟪f, baseCoordCLM u⟫ :=
    (Lp.inner_euclideanTuple q (fun i ↦ derivCoordCLM i u)).trans henergy
  have hquad : (θ * k) * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ := by
    calc
      _ = θ * (k * ‖u‖ ^ 2) := mul_assoc _ _ _
      _ ≤ θ * ‖∇ (u : H¹(Ω))‖ ^ 2 := mul_le_mul_of_nonneg_left hgrad hθ.le
      _ ≤ ⟪f, baseCoordCLM u⟫ := hpoint.trans_eq hpair
      _ ≤ ‖f‖ * ‖baseCoordCLM u‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖u‖ :=
        mul_le_mul_of_nonneg_left (baseCoordCLM_norm_le u) (norm_nonneg f)
  simpa only [one_mul, zero_mul, add_zero] using
    PDE.Analysis.Scalar.le_linear_of_quadratic_le hθk
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 0) (norm_nonneg f)
      (by simpa only [one_mul, zero_mul, add_zero] using hquad)

end SobolevSpace.GraphSpace
