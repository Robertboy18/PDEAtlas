/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.Calculus

/-!
# Dirichlet integral and basic divergence identities

The classical Dirichlet integral `∫_U ‖∇u‖²` (without the factor `½` and without a load term;
the Dirichlet functional `½ ∫ |Dv|² - ∫ f v` on `H¹₀` is `SobolevSpace.GraphSpace.dirichletEnergy`),
the gradient pairing `∫_U ∇u · ∇v`, and the pointwise identity `div (u ∇v) = ∇u · ∇v + u Δv`
used by Green's formulas.

The energies are real-valued Bochner integrals, which are `0` for nonintegrable integrands, so
theorems about them assume the measurability and integrability they need.
-/

open scoped Gradient

@[expose] public section

open PDE (laplacian divergence)

namespace Energy

variable {n : ℕ}

/-- The Dirichlet integral `∫_U |Dw|² dx`, the squared `L²` norm of the classical gradient.

This is only the integral; finiteness and Sobolev-space membership are separate hypotheses in
the Sobolev and variational files. -/
noncomputable def dirichletEnergy (U : Set (ℝ^n))
    (w : ℝ^n → ℝ) : ℝ :=
  ∫ x in U, ‖∇ w x‖^2

/-- The L² pairing of two gradients, `∫_U Du·Dv dx`, as a Bochner integral of the pointwise
inner product. -/
noncomputable def gradientL2InnerProduct (U : Set (ℝ^n))
    (u v : ℝ^n → ℝ) : ℝ :=
  ∫ x in U, inner ℝ (∇ u x) (∇ v x)

/-- The divergence identity `div (u ∇v) = ∇u · ∇v + u Δv`. -/
theorem divergence_of_u_grad_v {u v : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] v) y) x) :
    ∇·
        (fun y ↦ WithLp.toLp 2 fun i ↦
          u y * (∂[i] v) y) x =
      ∑ i, (∂[i] u) x * (∂[i] v) x +
        u x * laplacian v x := by
  simp_rw [divergence, laplacian, PDE.partialDeriv_mul hu (hv _),
    Finset.sum_add_distrib, Finset.mul_sum]

/-- Pointwise identity
`div (u ∇v - v ∇u) = u Δv - v Δu` underlying Green's second formula. -/
theorem divergence_u_grad_v_sub_v_grad_u
    {u v : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hDu : ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] u) y) x)
    (hDv : ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] v) y) x) :
    ∇·
        (fun y ↦ WithLp.toLp 2 fun i ↦
          u y * (∂[i] v) y - v y * (∂[i] u) y) x =
      u x * laplacian v x - v x * laplacian u x := by
  let F : ℝ^n → ℝ^n :=
    fun y ↦ WithLp.toLp 2 fun i ↦ u y * (∂[i] v) y
  let G : ℝ^n → ℝ^n :=
    fun y ↦ WithLp.toLp 2 fun i ↦ v y * (∂[i] u) y
  have hF : ∀ i : Fin n, DifferentiableAt ℝ (F · i) x := by
    intro i
    rw [show (F · i) = fun y ↦ u y * (∂[i] v) y by
      funext y
      rfl]
    exact hu.mul (hDv i)
  have hG : ∀ i : Fin n, DifferentiableAt ℝ (G · i) x := by
    intro i
    rw [show (G · i) = fun y ↦ v y * (∂[i] u) y by
      funext y
      rfl]
    exact hv.mul (hDu i)
  have hsub := PDE.divergence_sub (n := n) (F := F) (G := G) (x := x) hF hG
  have hUv :
      ∇· F x =
        (∑ i : Fin n, (∂[i] u) x * (∂[i] v) x) +
          u x * laplacian v x := by
    simpa [F] using (divergence_of_u_grad_v (n := n) (u := u) (v := v) hu hDv)
  have hVu :
      ∇· G x =
        (∑ i : Fin n, (∂[i] v) x * (∂[i] u) x) +
          v x * laplacian u x := by
    simpa [G] using (divergence_of_u_grad_v (n := n) (u := v) (v := u) hv hDu)
  have hgrad :
      (∑ i : Fin n, (∂[i] u) x * (∂[i] v) x) =
        ∑ i : Fin n, (∂[i] v) x * (∂[i] u) x := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  have :
      ∇· (fun y ↦ F y - G y) x =
        ((∑ i : Fin n, (∂[i] u) x * (∂[i] v) x) +
            u x * laplacian v x) -
          ((∑ i : Fin n, (∂[i] v) x * (∂[i] u) x) +
            v x * laplacian u x) := by
    simp [hsub, hUv, hVu]
  rw [show
      (fun y ↦ WithLp.toLp 2 fun i ↦
        u y * (∂[i] v) y - v y * (∂[i] u) y) =
        fun y ↦ F y - G y by
    funext y
    ext i
    rfl]
  rw [this, hgrad]
  ring

end Energy
