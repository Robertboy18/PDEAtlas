/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Laplacian.Extrema
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.JetOperator
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Touching tests for the viscous Hamilton–Jacobi equation

At an upper contact, the solution and test have the same first derivative.
Their spatial Laplacians are ordered, so nonnegative viscosity transfers the
classical subsolution inequality to the test. A lower contact reverses the
inequality. These are local calculations at a single point; the Hamiltonian
need not be continuous. They are (8)-(11) in Evans, §10.1.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1.1, (8)-(11).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Laplacian

namespace HamiltonJacobi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A classical viscous subsolution satisfies the same inequality on a
`C²` upper test. Only the test's spatial Laplacian remains on the right. -/
theorem spatialJetOperator_le_mul_laplacian_of_upper_contact {H : E → E → ℝ} {u φ : E × ℝ → ℝ}
    {z : E × ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hu : DifferentiableAt ℝ u z)
    (hspace : ContDiffAt ℝ 2 (fun x ↦ u (x, z.2)) z.1) (hφ : ContDiffAt ℝ 2 φ z)
    (hcontact : IsLocalMax (fun y ↦ u y - φ y) z)
    (hresidual : spatialJetOperator H (z, fderiv ℝ u z) ≤ ε * Δ (fun x ↦ u (x, z.2)) z.1) :
    spatialJetOperator H (z, fderiv ℝ φ z) ≤ ε * Δ (fun x ↦ φ (x, z.2)) z.1 := by
  have hdφ := hφ.differentiableAt (by norm_num)
  have heq : fderiv ℝ u z = fderiv ℝ φ z :=
    sub_eq_zero.mp (hcontact.hasFDerivAt_eq_zero (hu.hasFDerivAt.sub hdφ.hasFDerivAt))
  have hφs : ContDiffAt ℝ 2 (fun x ↦ φ (x, z.2)) z.1 :=
    hφ.comp z.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hs : IsLocalMax (fun x ↦ u (x, z.2) - φ (x, z.2)) z.1 :=
    hcontact.comp_continuous (g := fun x : E ↦ (x, z.2)) (continuousAt_id.prodMk continuousAt_const)
  have hΔ := hs.laplacian_nonpos (hspace.sub hφs)
  change Δ ((fun x ↦ u (x, z.2)) - fun x ↦ φ (x, z.2)) z.1 ≤ 0 at hΔ
  rw [hspace.laplacian_sub hφs] at hΔ
  rw [← heq]
  exact hresidual.trans (mul_le_mul_of_nonneg_left (sub_nonpos.mp hΔ) hε)

/-- At a `C²` lower contact, the test's Laplacian is bounded above by that of
the classical supersolution. Nonnegative viscosity preserves this order. -/
theorem mul_laplacian_le_spatialJetOperator_of_lower_contact {H : E → E → ℝ} {u φ : E × ℝ → ℝ}
    {z : E × ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hu : DifferentiableAt ℝ u z)
    (hspace : ContDiffAt ℝ 2 (fun x ↦ u (x, z.2)) z.1) (hφ : ContDiffAt ℝ 2 φ z)
    (hcontact : IsLocalMin (fun y ↦ u y - φ y) z)
    (hresidual : ε * Δ (fun x ↦ u (x, z.2)) z.1 ≤ spatialJetOperator H (z, fderiv ℝ u z)) :
    ε * Δ (fun x ↦ φ (x, z.2)) z.1 ≤ spatialJetOperator H (z, fderiv ℝ φ z) := by
  have hdφ := hφ.differentiableAt (by norm_num)
  have heq : fderiv ℝ u z = fderiv ℝ φ z :=
    sub_eq_zero.mp (hcontact.hasFDerivAt_eq_zero (hu.hasFDerivAt.sub hdφ.hasFDerivAt))
  have hφs : ContDiffAt ℝ 2 (fun x ↦ φ (x, z.2)) z.1 :=
    hφ.comp z.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hs : IsLocalMin (fun x ↦ u (x, z.2) - φ (x, z.2)) z.1 :=
    hcontact.comp_continuous (g := fun x : E ↦ (x, z.2)) (continuousAt_id.prodMk continuousAt_const)
  have hΔ := hs.laplacian_nonneg (hspace.sub hφs)
  change 0 ≤ Δ ((fun x ↦ u (x, z.2)) - fun x ↦ φ (x, z.2)) z.1 at hΔ
  rw [hspace.laplacian_sub hφs] at hΔ
  rw [← heq]
  exact (mul_le_mul_of_nonneg_left (sub_nonneg.mp hΔ) hε).trans hresidual

end HamiltonJacobi
