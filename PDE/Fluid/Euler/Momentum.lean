/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Composition
public import PDE.Analysis.Calculus.Gradient

/-!
# Euler momentum on a real Hilbert space

Spacetime is `ℝ × E`. The joint derivative in direction `(1, u)` represents
time differentiation and convection. The perturbation and rescaling formulas
require actual differentiability, with no finite-dimensional assumption.
These are momentum identities; they impose no incompressibility condition.
The residual is `momentumResidual`; `momentumResidual_add` expands it under a perturbation and
`momentumResidual_rescale` gives the scaling factor `a² b`.
-/

@[expose] public noncomputable section

namespace Euler

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unforced momentum residual `∂ₜu + Dₓu(u) + ∇ₓp` on product spacetime. -/
def momentumResidual (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E) : E :=
  fderiv ℝ u q (1, u q) + ∇ (fun x ↦ p (q.1, x)) q.2

/-- Joint differentiability identifies the residual with its time and spatial
derivatives separately. -/
theorem momentumResidual_eq_deriv_add {u : ℝ × E → E} (p : ℝ × E → ℝ)
    (q : ℝ × E) (hu : DifferentiableAt ℝ u q) :
    momentumResidual u p q =
      deriv (fun t ↦ u (t, q.2)) q.1 +
        fderiv ℝ (fun x ↦ u (q.1, x)) q.2 (u q) +
          ∇ (fun x ↦ p (q.1, x)) q.2 := by
  have ht := hu.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have hx := hu.hasFDerivAt.comp q.2
    ((hasFDerivAt_const (𝕜 := ℝ) (x := q.2) (c := q.1)).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) q.2))
  change HasDerivAt (fun t ↦ u (t, q.2)) _ q.1 at ht
  change HasFDerivAt (fun x ↦ u (q.1, x)) _ q.2 at hx
  rw [momentumResidual, ht.deriv, hx.fderiv]
  congr 1
  change fderiv ℝ u q (1, u q) =
    fderiv ℝ u q (1, 0) + fderiv ℝ u q (0, u q)
  rw [← map_add]
  simp

/-- Expansion of the nonlinear momentum residual under a velocity and pressure
perturbation. Each differentiated field is assumed differentiable at the point. -/
theorem momentumResidual_add {u w : ℝ × E → E} {p r : ℝ × E → ℝ} (q : ℝ × E)
    (hu : DifferentiableAt ℝ u q) (hw : DifferentiableAt ℝ w q)
    (hp : DifferentiableAt ℝ (fun x ↦ p (q.1, x)) q.2)
    (hr : DifferentiableAt ℝ (fun x ↦ r (q.1, x)) q.2) :
    momentumResidual (fun y ↦ u y + w y) (fun y ↦ p y + r y) q =
      momentumResidual u p q + fderiv ℝ w q (1, u q) +
        fderiv ℝ u q (0, w q) + fderiv ℝ w q (0, w q) +
          ∇ (fun x ↦ r (q.1, x)) q.2 := by
  have hgrad : ∇ (fun x ↦ p (q.1, x) + r (q.1, x)) q.2 =
      ∇ (fun x ↦ p (q.1, x)) q.2 + ∇ (fun x ↦ r (q.1, x)) q.2 := by
    simp only [gradient, fderiv_fun_add hp hr, map_add]
  have hsplit : ((1 : ℝ), u q + w q) = (1, u q) + (0, w q) := by simp
  simp only [momentumResidual, fderiv_fun_add hu hw,
    hgrad, hsplit, add_apply, map_add]
  abel

/-- Euler scaling on any real Hilbert space: amplitude `a`, spatial factor `b`,
time factor `a b`, and pressure factor `a²` give residual factor `a² b`.
This includes spatial rescaling and time-amplitude rescaling. -/
theorem momentumResidual_rescale (a b : ℝ) (u : ℝ × E → E) (p : ℝ × E → ℝ)
    (q : ℝ × E) (hu : DifferentiableAt ℝ u (a * b * q.1, b • q.2))
    (hp : DifferentiableAt ℝ (fun x ↦ p (a * b * q.1, x)) (b • q.2)) :
    momentumResidual (fun y ↦ a • u (a * b * y.1, b • y.2))
      (fun y ↦ a ^ 2 * p (a * b * y.1, b • y.2)) q =
        (a ^ 2 * b) • momentumResidual u p (a * b * q.1, b • q.2) := by
  let T : (ℝ × E) →L[ℝ] (ℝ × E) :=
    ((a * b) • ContinuousLinearMap.fst ℝ ℝ E).prod
      (b • ContinuousLinearMap.snd ℝ ℝ E)
  have hvel : HasFDerivAt (fun y : ℝ × E ↦ a • u (a * b * y.1, b • y.2))
      (a • (fderiv ℝ u (T q)).comp T) q :=
    (hu.hasFDerivAt.comp q T.hasFDerivAt).const_smul a
  have hpres := (hp.hasFDerivAt.comp q.2
    (b • ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul (a ^ 2)
  change HasFDerivAt (fun x ↦ a ^ 2 • p (a * b * q.1, b • x)) _ q.2 at hpres
  have hgrad : ∇ (fun x ↦ a ^ 2 * p (a * b * q.1, b • x)) q.2 =
      (a ^ 2 * b) • ∇ (fun x ↦ p (a * b * q.1, x)) (b • q.2) := by
    apply ext_inner_right ℝ
    intro v
    change ⟪∇ (fun x ↦ a ^ 2 • p (a * b * q.1, b • x)) q.2, v⟫ = _
    rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left, hpres.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul]
    ring
  unfold momentumResidual
  rw [hvel.fderiv, hgrad]
  have hT : T (1, a • u (T q)) = (a * b) • (1, u (T q)) := by
    ext <;> simp [T, mul_comm, smul_smul]
  change a • (fderiv ℝ u (T q) (T (1, a • u (T q)))) + _ = _
  rw [hT, map_smul, smul_smul, show a * (a * b) = a ^ 2 * b by ring, ← smul_add]
  rfl

end Euler
