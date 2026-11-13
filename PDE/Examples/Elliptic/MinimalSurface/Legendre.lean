/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.MinimalSurface.Legendre
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonconvex minimal graph and its local Legendre dual

Scherk's graph `log(cos y) - log(cos x)` satisfies the planar minimal-surface equation
where both cosines are nonzero (`residual_scherk`). Mathlib's real logarithm makes this
`log |cos y| - log |cos x|` on the full domain. Its Hessian at the origin has
determinant `-1`, so the graph is not convex. Its normalized gradient is divergence
free, and `exists_localLegendre_solution_of_divergence_eq_zero` gives a local Legendre
dual near the origin that is `C²` and solves the linear dual equation
(`exists_scherk_dual`).
-/

@[expose] public noncomputable section

open Set
open scoped Gradient

namespace PDE.Examples.MinimalSurface

open PDE.Analysis PDE.Elliptic.MinimalSurface

/-- A separated logarithmic minimal graph on the nonsingular cosine region. -/
def scherk (x : ℝ^2) : ℝ := Real.log (Real.cos (x 1)) - Real.log (Real.cos (x 0))

/-- The set where `cos x₀ ≠ 0` and `cos x₁ ≠ 0`. -/
def domain : Set (ℝ^2) := {x | Real.cos (x 0) ≠ 0 ∧ Real.cos (x 1) ≠ 0}

/-- The domain is open. -/
theorem isOpen_domain : IsOpen domain := by
  apply IsOpen.inter
  · exact isOpen_ne.preimage (by fun_prop)
  · exact isOpen_ne.preimage (by fun_prop)

/-- The origin lies in the nonsingular region. -/
theorem zero_mem_domain : (0 : ℝ^2) ∈ domain := by
  simp [domain]

/-- Scherk's graph is `C²` on its domain. -/
theorem contDiffOn_scherk : ContDiffOn ℝ 2 scherk domain := by
  apply isOpen_domain.contDiffOn_iff.mpr
  intro x hx
  have hx0 := hx.1
  have hx1 := hx.2
  unfold scherk
  cas using hx0 hx1

/-- The coordinate derivatives of the logarithmic graph. -/
theorem partial_scherk {x : ℝ^2} (hx : x ∈ domain) :
    (∂[0] scherk) x = Real.sin (x 0) / Real.cos (x 0) ∧
      (∂[1] scherk) x = -Real.sin (x 1) / Real.cos (x 1) := by
  have hx0 := hx.1
  have hx1 := hx.2
  constructor <;> unfold scherk <;> cas using hx0 hx1

/-- The Hessian is diagonal, with one positive and one negative entry. -/
theorem hessian_scherk {x : ℝ^2} (hx : x ∈ domain) :
    jacobianMatrix (∇ scherk) x =
      !![1 / Real.cos (x 0) ^ 2, 0; 0, -1 / Real.cos (x 1) ^ 2] := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h0 (j : Fin 2) : (∂[j] (∂[0] scherk)) x =
      (∂[j] (fun y : ℝ^2 ↦ Real.sin (y 0) / Real.cos (y 0))) x := by
    apply partialDeriv_congr_nhds j
    filter_upwards [isOpen_domain.mem_nhds hx] with y hy
    exact (partial_scherk hy).1
  have h1 (j : Fin 2) : (∂[j] (∂[1] scherk)) x =
      (∂[j] (fun y : ℝ^2 ↦ -Real.sin (y 1) / Real.cos (y 1))) x := by
    apply partialDeriv_congr_nhds j
    filter_upwards [isOpen_domain.mem_nhds hx] with y hy
    exact (partial_scherk hy).2
  ext i j
  rw [jacobianMatrix_gradient_apply]
  fin_cases i <;> fin_cases j
  · change (∂[0] (∂[0] scherk)) x = 1 / Real.cos (x 0) ^ 2
    rw [h0]
    cas using hx0 (Real.sin_sq_add_cos_sq (x 0))
  · change (∂[1] (∂[0] scherk)) x = 0
    rw [h0]
    cas using hx0
  · change (∂[0] (∂[1] scherk)) x = 0
    rw [h1]
    cas using hx1
  · change (∂[1] (∂[1] scherk)) x = -1 / Real.cos (x 1) ^ 2
    rw [h1]
    cas using hx1 (Real.sin_sq_add_cos_sq (x 1))

/-- Scherk's graph solves the minimal-surface equation on its domain. -/
theorem residual_scherk {x : ℝ^2} (hx : x ∈ domain) : residual scherk x = 0 := by
  obtain ⟨h0, h1⟩ := partial_scherk hx
  have hH := hessian_scherk hx
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 0) hH
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 0) hH
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 1) hH
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    jacobianMatrix_gradient_apply] at h00 h10 h11
  unfold PDE.Elliptic.MinimalSurface.residual
  rw [h0, h1, h00, h10, h11]
  cas using [hx.1, hx.2, Real.sin_sq_add_cos_sq (x 0), Real.sin_sq_add_cos_sq (x 1)]

/-- The Hessian determinant at the origin is `-1`. -/
theorem det_hessian_scherk_zero : (jacobianMatrix (∇ scherk) 0).det = -1 := by
  rw [hessian_scherk zero_mem_domain, Matrix.det_fin_two]
  norm_num

/-- The normalized gradient of the Scherk graph has zero classical divergence. -/
theorem divergence_normalizedGradient_scherk {x : ℝ^2} (hx : x ∈ domain) :
    (∇· (fun y ↦ (Real.sqrt (1 + ‖∇ scherk y‖ ^ 2))⁻¹ • ∇ scherk y)) x = 0 :=
  (divergence_normalizedGradient_eq_zero_iff
    (contDiffOn_scherk.contDiffAt (isOpen_domain.mem_nhds hx))).mpr (residual_scherk hx)

/-- Near the origin the gradient of Scherk's graph is a local homeomorphism, and the
Legendre dual is `C²` and solves the linear dual equation. -/
theorem exists_scherk_dual :
    ∃ e : OpenPartialHomeomorph (ℝ^2) (ℝ^2),
      (e : ℝ^2 → ℝ^2) = ∇ scherk ∧ (0 : ℝ^2) ∈ e.source ∧ e.source ⊆ domain ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ContDiffOn ℝ 2 (localLegendre scherk e.symm) e.target ∧
            (∀ p ∈ e.target, HasGradientAt (localLegendre scherk e.symm) (e.symm p) p) ∧
              ∀ p ∈ e.target, dualResidual (localLegendre scherk e.symm) p = 0 := by
  apply exists_localLegendre_solution_of_divergence_eq_zero
    isOpen_domain zero_mem_domain contDiffOn_scherk
  · rw [det_hessian_scherk_zero]
    norm_num
  · exact fun _ hx ↦ divergence_normalizedGradient_scherk hx

end PDE.Examples.MinimalSurface
