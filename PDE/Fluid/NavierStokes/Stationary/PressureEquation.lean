/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Linearization
import PDE.Elliptic.Regularity.Interior.Weyl.SecondOrder
import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileScaling
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Smooth
import PDE.FDeriv.PartialDeriv.Transport

/-!
# The pressure equation of the stationary profile equation

Let `W` be a smooth divergence-free field on `ℝ³` with
`-½ W - ½ ξ·∇W + W·∇W - ΔW + ∇P = 0` at every point. The divergence of this equation is the
equation of the pressure, `ΔP = -∑ₖⱼ ∂ⱼWₖ ∂ₖWⱼ = -tr((∇W)²)`. The two divergence identities behind
it hold for every smooth divergence-free field in every dimension.

## Main results

* `NavierStokes.divergence_laplacian_eq_zero` (all dimensions, all smooth divergence-free
  fields): `div(ΔW) = 0`.
* `NavierStokes.divergence_advectiveDerivative_self` (the same scope):
  `div((W·∇)W) = ∑ₖⱼ ∂ⱼWₖ ∂ₖWⱼ`, which is `tr((∇W)²)`.
* `NavierStokes.laplacian_pressure_eq` (all smooth divergence-free `W` on `ℝ³` and all `P` with
  the stationary profile equation at every point): `ΔP = -∑ₖⱼ ∂ⱼWₖ ∂ₖWⱼ`.

## How it works

The terms `W + ξ·∇W` and `ΔW` are divergence free because `W` is
(`NavierStokes.Nonuniqueness.divergence_velocityDrift`, and the Laplacian commutes with
derivatives). The product rule gives `div((W·∇)W) = ∑ₖⱼ ∂ⱼWₖ ∂ₖWⱼ + W·∇(div W)`
(`PDE.partialDeriv_fderiv_apply`), and the last term vanishes.
`NavierStokes.Nonuniqueness.UnstableProfile.divergence_laplacian` is the first identity for the
profile of an `UnstableProfile`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, proof of
  Proposition 3: the pressure equation (2.18), obtained by taking the divergence.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public section

open scoped Gradient

namespace NavierStokes

variable {n : ℕ}

/-- The Laplacian of a smooth divergence-free field is divergence free. -/
theorem divergence_laplacian_eq_zero {W : ℝ^n → ℝ^n} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ x, ∇· W x = 0) (x : ℝ^n) : ∇· (PDE.laplacian W) x = 0 := by
  have hWi (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ W y i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hW
  have hcomp (i : Fin n) : (fun y ↦ PDE.laplacian W y i) =
      fun y ↦ PDE.laplacian (fun z ↦ W z i) y :=
    funext fun y ↦ PDE.laplacian_apply_of_contDiff (hW.of_le (by simp)) y i
  have hdivf : (fun y ↦ ∑ i : Fin n, ∂[i] (fun z ↦ W z i) y) = fun _ ↦ 0 :=
    funext fun y ↦ hdiv y
  unfold PDE.divergence
  simp_rw [hcomp]
  rw [Finset.sum_congr rfl fun i _ ↦ (PDE.laplacian_partialDeriv_eq (hWi i) i x).symm,
    ← LaplacianEquation.laplacian_finsetSum _
      (fun i _ ↦ (PDE.contDiff_top_partialDeriv (hWi i)).of_le (by simp)) x, hdivf]
  simp [PDE.laplacian, PDE.partialDeriv]

/-- **The divergence of the convection term of a divergence-free field** is the trace of the
square of its gradient: `div((W·∇)W) = Σₖⱼ ∂ⱼWₖ ∂ₖWⱼ`. The other term of the product rule,
`W·∇(div W)`, vanishes. -/
theorem divergence_advectiveDerivative_self {W : ℝ^n → ℝ^n} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ x, ∇· W x = 0) (x : ℝ^n) :
    ∇· (PDE.advectiveDerivative W W) x =
      ∑ k, ∑ j, ∂[j] (fun y ↦ W y k) x * ∂[k] (fun y ↦ W y j) x := by
  have hWd : Differentiable ℝ W := hW.differentiable (by simp)
  have hWi (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ W y i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hW
  -- The components of the convection term.
  have hcomp (k : Fin n) : (fun y ↦ PDE.advectiveDerivative W W y k) =
      fun y ↦ fderiv ℝ (fun z ↦ W z k) y (W y) := funext fun y ↦ by
    have h : HasFDerivAt (fun z ↦ W z k)
        ((EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).comp (fderiv ℝ W y)) y :=
      (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).hasFDerivAt.comp y (hWd y).hasFDerivAt
    rw [h.fderiv]
    rfl
  have hk (k : Fin n) : ∂[k] (fun y ↦ fderiv ℝ (fun z ↦ W z k) y (W y)) x =
      fderiv ℝ (∂[k] (fun z ↦ W z k)) x (W x) + fderiv ℝ (fun z ↦ W z k) x (∂[k] W x) :=
    PDE.partialDeriv_fderiv_apply k ((hWi k).of_le (by simp)).contDiffAt (hWd x)
  -- The derivative of the divergence vanishes.
  have hdivf : (fun y ↦ ∑ k : Fin n, ∂[k] (fun z ↦ W z k) y) = fun _ ↦ (0 : ℝ) :=
    funext fun y ↦ hdiv y
  have hzero : ∑ k : Fin n, fderiv ℝ (∂[k] (fun z ↦ W z k)) x (W x) = 0 := by
    have hd : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ (∂[k] (fun z ↦ W z k)) x := fun k _ ↦
      (PDE.contDiff_top_partialDeriv (hWi k)).differentiable (by simp) x
    have h := (fderiv_fun_sum (𝕜 := ℝ) hd).symm
    rw [hdivf, (hasFDerivAt_const (0 : ℝ) x).fderiv] at h
    have h' := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (W x)) h
    simpa only [sum_apply, zero_apply] using h'
  rw [PDE.divergence_eq_sum]
  simp_rw [hcomp, hk]
  rw [Finset.sum_add_distrib, hzero, zero_add]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PDE.partialDeriv_apply k j (hWd x)]

/-- **The pressure equation of the stationary profile equation.** If `W` is a smooth
divergence-free field on `ℝ³` and `-½ W - ½ ξ·∇W + W·∇W - ΔW + ∇P = 0` at every point, then
`ΔP = -Σₖⱼ ∂ⱼWₖ ∂ₖWⱼ = -tr((∇W)²)`. It is the divergence of the equation. -/
theorem laplacian_pressure_eq {W : ℝ^3 → ℝ^3} {P : ℝ^3 → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ x, ∇· W x = 0) (heq : ∀ x, stationaryVelocityOperator W x + ∇ P x = 0)
    (x : ℝ^3) :
    PDE.laplacian P x = -∑ k, ∑ j, ∂[j] (fun y ↦ W y k) x * ∂[k] (fun y ↦ W y j) x := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ W) := hW.fderiv_right (by simp)
  have hdrift : Differentiable ℝ (SpectralProfile.velocityDrift W) :=
    (hW.add (hD.clm_apply contDiff_id)).differentiable (by simp)
  have hadv : Differentiable ℝ (PDE.advectiveDerivative W W) :=
    (hD.clm_apply hW).differentiable (by simp)
  have hlapc : ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian W) := by
    unfold PDE.laplacian
    exact ContDiff.sum fun i _ ↦ PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hW)
  have hlap : Differentiable ℝ (PDE.laplacian W) := hlapc.differentiable (by simp)
  have h1 : Differentiable ℝ fun y ↦ (-(1 / 2) : ℝ) • SpectralProfile.velocityDrift W y :=
    hdrift.fun_const_smul _
  have h12 : Differentiable ℝ fun y ↦
      (-(1 / 2) : ℝ) • SpectralProfile.velocityDrift W y + PDE.advectiveDerivative W W y :=
    h1.fun_add hadv
  have hc : ∀ {F : ℝ^3 → ℝ^3}, Differentiable ℝ F →
      ∀ i : Fin 3, DifferentiableAt ℝ (fun y ↦ F y i) x := fun hF i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (hF x)
  have hgrad : ∇ P = fun y ↦ (-1 : ℝ) • stationaryVelocityOperator W y := funext fun y ↦ by
    rw [neg_one_smul]
    exact eq_neg_of_add_eq_zero_right (heq y)
  have hS : stationaryVelocityOperator W = fun y ↦
      ((-(1 / 2) : ℝ) • SpectralProfile.velocityDrift W y + PDE.advectiveDerivative W W y) -
        PDE.laplacian W y := rfl
  rw [PDE.laplacian_eq_divergence_gradient, hgrad, PDE.divergence_const_smul, hS,
    PDE.divergence_sub (hc h12) (hc hlap), PDE.divergence_add (hc h1) (hc hadv),
    PDE.divergence_const_smul, Nonuniqueness.divergence_velocityDrift hW hdiv x,
    divergence_laplacian_eq_zero hW hdiv x, divergence_advectiveDerivative_self hW hdiv x]
  ring

end NavierStokes
