/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Pullback
public import PDE.CalculusOfVariations.Noether.Current

/-!
# Scalar coordinates of variational densities and currents

A one-row matrix is the gradient of a scalar field. The coordinate conversion
below identifies the general variational density, momentum, Euler–Lagrange
expression, and Noether current with their scalar forms, so the general theorems
apply to scalar fields.

The scalar Lagrangians `L(p, z, x)` are those of Evans, §8.6.1, (1), where Noether's theorem is
stated for real-valued `w`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1, (1), p. 512, and §8.6.2, Theorem 1
  (Noether's Theorem), p. 513.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter
open scoped Matrix.Norms.Elementwise Gradient Topology

namespace PDE.CalculusOfVariations

open Analysis Noether

variable {n : ℕ}

/-- Read the only row of a scalar-field Jacobian as a Euclidean vector. -/
def scalarJacobianRow : Matrix (Fin 1) (Fin n) ℝ →L[ℝ] ℝ^n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj 0)

/-- A scalar Lagrangian in the matrix/vector convention of the general theory. -/
def scalarLagrangian (L : ℝ^n → ℝ → ℝ^n → ℝ)
    (P : Matrix (Fin 1) (Fin n) ℝ) (z : ℝ^1) (x : ℝ^n) : ℝ :=
  L (scalarJacobianRow P) (z 0) x

/-- The single row of a Jacobian is the gradient of its scalar component. -/
theorem scalarJacobianRow_jacobianMatrix (u : ℝ^n → ℝ^1) (x : ℝ^n) :
    scalarJacobianRow (jacobianMatrix u x) = ∇ (fun y ↦ u y 0) x := by
  ext i
  change jacobianMatrix u x 0 i = _
  rw [gradient_apply_eq_partialDeriv]
  rfl

/-- Matrix-coordinate energy agrees pointwise with the scalar gradient energy. -/
theorem fieldDensity_scalarLagrangian (L : ℝ^n → ℝ → ℝ^n → ℝ)
    (u : ℝ^n → ℝ^1) (x : ℝ^n) :
    fieldDensity (scalarLagrangian L) u x =
      L (∇ (fun y ↦ u y 0) x) (u x 0) x := by
  simp only [fieldDensity, scalarLagrangian, scalarJacobianRow_jacobianMatrix]

/-- Smoothness of a scalar density passes through the canonical linear coordinate maps. -/
theorem contDiff_scalarLagrangian {L : ℝ^n → ℝ → ℝ^n → ℝ} {r : WithTop ℕ∞}
    (hL : ContDiff ℝ r (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2)) :
    ContDiff ℝ r
      (fun a : Matrix (Fin 1) (Fin n) ℝ × (ℝ^1 × ℝ^n) ↦
        scalarLagrangian L a.1 a.2.1 a.2.2) :=
  hL.comp ((scalarJacobianRow.contDiff.comp contDiff_fst).prodMk
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff.comp
      (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd)))

/-- The same coordinate conversion preserves smoothness of a density germ. -/
theorem contDiffAt_scalarLagrangian {L : ℝ^n → ℝ → ℝ^n → ℝ} {r : WithTop ℕ∞}
    {P : Matrix (Fin 1) (Fin n) ℝ} {z : ℝ^1} {x : ℝ^n}
    (hL : ContDiffAt ℝ r (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (scalarJacobianRow P, (z 0, x))) :
    ContDiffAt ℝ r
      (fun a : Matrix (Fin 1) (Fin n) ℝ × (ℝ^1 × ℝ^n) ↦
        scalarLagrangian L a.1 a.2.1 a.2.2) (P, (z, x)) :=
  hL.comp (P, (z, x)) (f := fun a ↦
    (scalarJacobianRow a.1, (a.2.1 0, a.2.2)))
    ((scalarJacobianRow.contDiff.contDiffAt.comp _ contDiffAt_fst).prodMk
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp _
      (contDiffAt_fst.comp _ contDiffAt_snd)).prodMk
        (contDiffAt_snd.comp _ contDiffAt_snd)))

/-- The scalar coordinate conversion also preserves one-sided closure jets. -/
def scalarLagrangianClosureJet {Ω : Set (ℝ^n)}
    {L : ℝ^n → ℝ → ℝ^n → ℝ} (hopen : IsOpen Ω)
    (hL : ContinuousSecondJetOn
      (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2) {a | a.2.2 ∈ Ω}) :
    ContinuousSecondJetOn
      (fun a : Matrix (Fin 1) (Fin n) ℝ × (ℝ^1 × ℝ^n) ↦
        scalarLagrangian L a.1 a.2.1 a.2.2) {a | a.2.2 ∈ Ω} := by
  let T : (Matrix (Fin 1) (Fin n) ℝ × (ℝ^1 × ℝ^n)) →L[ℝ] (ℝ^n × (ℝ × ℝ^n)) :=
    (scalarJacobianRow.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      (((EuclideanSpace.proj 0).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
  exact hL.compContinuousLinearMap
    (hopen.preimage (continuous_snd.comp continuous_snd)) T
    (hopen.preimage (continuous_snd.comp continuous_snd)) (fun _ hx ↦ hx)

private theorem scalarJacobianRow_single (i : Fin n) :
    scalarJacobianRow (Matrix.single (0 : Fin 1) i (1 : ℝ)) =
      EuclideanSpace.single i 1 := by
  ext j
  change Matrix.single (0 : Fin 1) i (1 : ℝ) 0 j = EuclideanSpace.single i 1 j
  simp [Matrix.single, PiLp.single_apply, eq_comm]

/-- The sole momentum row is the gradient of `L` in its scalar gradient argument. -/
theorem momentum_scalarLagrangian {L : ℝ^n → ℝ → ℝ^n → ℝ}
    (u : ℝ^n → ℝ^1) (x : ℝ^n)
    (hL : DifferentiableAt ℝ (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (∇ (fun y ↦ u y 0) x, (u x 0, x))) (i : Fin n) :
    momentum (scalarLagrangian L) u 0 i x =
      ∇ (fun p ↦ L p (u x 0) x) (∇ (fun y ↦ u y 0) x) i := by
  have hp : DifferentiableAt ℝ (fun p ↦ L p (u x 0) x)
      (scalarJacobianRow (jacobianMatrix u x)) := by
    rw [scalarJacobianRow_jacobianMatrix]
    exact hL.comp (∇ (fun y ↦ u y 0) x) (f := fun p ↦ (p, (u x 0, x)))
      (differentiableAt_id.prodMk (differentiableAt_const (u x 0, x)))
  have hd := hp.hasFDerivAt.comp (jacobianMatrix u x) scalarJacobianRow.hasFDerivAt
  change fderiv ℝ (fun P ↦ L (scalarJacobianRow P) (u x 0) x)
    (jacobianMatrix u x) (Matrix.single 0 i 1) = _
  erw [hd.fderiv]
  change fderiv ℝ (fun p ↦ L p (u x 0) x) (scalarJacobianRow (jacobianMatrix u x))
    (scalarJacobianRow (Matrix.single 0 i 1)) = _
  rw [scalarJacobianRow_single, scalarJacobianRow_jacobianMatrix,
    fderiv_apply_single_one_eq_gradient_apply]

/-- The value derivative of the lifted scalar density is the ordinary derivative in `z`. -/
theorem valueDerivative_scalarLagrangian {L : ℝ^n → ℝ → ℝ^n → ℝ}
    (u : ℝ^n → ℝ^1) (x : ℝ^n)
    (hL : DifferentiableAt ℝ (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (∇ (fun y ↦ u y 0) x, (u x 0, x))) :
    fderiv ℝ (fun z ↦ scalarLagrangian L (jacobianMatrix u x) z x) (u x)
      (EuclideanSpace.single 0 1) =
        deriv (fun z ↦ L (∇ (fun y ↦ u y 0) x) z x) (u x 0) := by
  have hz : DifferentiableAt ℝ (fun z ↦ L (scalarJacobianRow (jacobianMatrix u x)) z x)
      (u x 0) := by
    rw [scalarJacobianRow_jacobianMatrix]
    exact hL.comp (u x 0) (f := fun z ↦ (∇ (fun y ↦ u y 0) x, (z, x)))
      ((differentiableAt_const _).prodMk
        (differentiableAt_id.prodMk (differentiableAt_const _)))
  have hd := hz.hasFDerivAt.comp (u x)
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt
  unfold scalarLagrangian
  erw [hd.fderiv]
  change fderiv ℝ (fun z ↦ L (scalarJacobianRow (jacobianMatrix u x)) z x) (u x 0) 1 = _
  rw [scalarJacobianRow_jacobianMatrix, fderiv_apply_one_eq_deriv]

/-- The general residual uses `-div Lp + Lz`, the negative of the scalar Noether defect. -/
theorem classicalEulerLagrange_scalarLagrangian {L : ℝ^n → ℝ → ℝ^n → ℝ}
    (u : ℝ^n → ℝ^1) (x : ℝ^n)
    (hL : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
        (∇ (fun z ↦ u z 0) y, (u y 0, y))) :
    classicalEulerLagrange (scalarLagrangian L) u x 0 =
      -∇· (fun y ↦ ∇ (fun p ↦ L p (u y 0) y) (∇ (fun z ↦ u z 0) y)) x +
        deriv (fun z ↦ L (∇ (fun y ↦ u y 0) x) z x) (u x 0) := by
  change -(∑ i, (∂[i] (momentum (scalarLagrangian L) u 0 i)) x) + _ = _
  rw [valueDerivative_scalarLagrangian u x hL.self_of_nhds]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have heq : momentum (scalarLagrangian L) u 0 i =ᶠ[𝓝 x]
      (fun y ↦ ∇ (fun p ↦ L p (u y 0) y) (∇ (fun z ↦ u z 0) y) i) :=
    hL.mono fun y hy ↦ momentum_scalarLagrangian u y hy i
  exact congrArg (fun A : ℝ^n →L[ℝ] ℝ ↦ A (EuclideanSpace.single i 1)) heq.fderiv_eq

/-- The one-component Noether current has the scalar form `m Lp + L X`. -/
theorem noetherCurrent_scalarLagrangian {L : ℝ^n → ℝ → ℝ^n → ℝ}
    (u v : ℝ^n → ℝ^1) (X : ℝ^n → ℝ^n) (x : ℝ^n)
    (hL : DifferentiableAt ℝ (fun a : ℝ^n × (ℝ × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (∇ (fun y ↦ u y 0) x, (u x 0, x))) :
    noetherCurrent (scalarLagrangian L) u v X x =
      (v x 0) • ∇ (fun p ↦ L p (u x 0) x) (∇ (fun y ↦ u y 0) x) +
        L (∇ (fun y ↦ u y 0) x) (u x 0) x • X x := by
  ext i
  simp [noetherCurrent, fieldDensity_scalarLagrangian, momentum_scalarLagrangian u x hL,
    PiLp.smul_apply, mul_comm]

end PDE.CalculusOfVariations
