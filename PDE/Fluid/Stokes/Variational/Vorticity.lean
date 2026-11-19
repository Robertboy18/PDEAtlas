/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.Residual
public import PDE.DistributionTheory.Distribution.Function.Lp
public import PDE.DistributionTheory.Distribution.Operator.Laplacian
import PDE.Analysis.Operator.ConstantCoefficient.Vorticity
import PDE.DistributionTheory.Distribution.Operator.Polynomial

/-!
# The native Stokes vorticity equation

The antisymmetric first weak derivatives lie in L² before any regularity
argument. Commuting ordinary distributional derivatives turns stationarity
into `Δ(∂ᵢuⱼ - ∂ⱼuᵢ) = ∂ⱼfᵢ - ∂ᵢfⱼ`. Incompressibility identifies the
divergence of this tensor with the velocity Laplacian. Thus first-order
interior regularity for the vorticity is enough to make the residual locally
L²; second-order regularity of the velocity is not an input.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Distributions Laplacian

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace IncompressibleFlow.Stokes

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Opens (ℝ^n)}

/-- The antisymmetric tensor of the first weak derivative coordinates. -/
def vorticity (u : H¹₀(Ω; ℝ^n)) (i j : Fin n) :
    DerivLp n 2 Ω :=
  derivCoordCLM i (u j) - derivCoordCLM j (u i)

private theorem lineDeriv_base (u : H¹₀(Ω; ℝ^n)) (i j : Fin n) :
    Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
      (Distribution.ofLp Ω 2 (baseCoordCLM (u j))) =
        Distribution.ofLp Ω 2 (derivCoordCLM i (u j)) := by
  have h : HasWeakDerivativeOn (Ω : Set (ℝ^n)) [i]
      (baseCoordCLM (u j) : ℝ^n → ℝ) (derivCoordCLM i (u j) : ℝ^n → ℝ) := by
    simpa only [baseCoordCLM_apply, derivCoordCLM_apply, singleDerivIndex_toList] using
      (u j : H¹(Ω)).property (singleDerivIndex n i)
  exact h.lineDerivCLM_ofFun

/-- The L² vorticity is the antisymmetric derivative of the velocity as an
ordinary distribution on the original domain. -/
theorem ofLp_vorticity (u : H¹₀(Ω; ℝ^n)) (i j : Fin n) :
    Distribution.ofLp Ω 2 (vorticity u i j) =
      Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
        (Distribution.ofLp Ω 2 (baseCoordCLM (u j))) -
      Distribution.lineDerivCLM (EuclideanSpace.single j (1 : ℝ))
        (Distribution.ofLp Ω 2 (baseCoordCLM (u i))) := by
  simp only [vorticity, map_sub, lineDeriv_base]

/-- Replacing the native first weak derivative by its distributional identity
expresses the residual as the velocity Laplacian plus force. -/
theorem residual_eq_sum_second_add
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (j : Fin n) :
    residual f u j =
      (∑ k : Fin n, Distribution.lineDerivCLM (EuclideanSpace.single k (1 : ℝ))
        (Distribution.lineDerivCLM (EuclideanSpace.single k (1 : ℝ))
          (Distribution.ofLp Ω 2 (baseCoordCLM (u j))) : 𝓓'(Ω, ℝ))) +
        Distribution.ofFun Ω (fun x ↦ f x j) volume ⊤ := by
  simp only [lineDeriv_base]
  rfl

/-- A raw incompressible energy minimizer has the divergence-form
vorticity equation. The force has no assumed weak derivative. -/
theorem laplacian_vorticity_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) (i j : Fin n) :
    Δ (Distribution.ofLp Ω 2 (vorticity u i j)) =
      ∂[j] (Distribution.ofFun Ω (fun x ↦ f x i) volume ⊤) -
        ∂[i] (Distribution.ofFun Ω (fun x ↦ f x j) volume ⊤) := by
  change LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'(Ω, ℝ) _ = _
  let D (k : Fin n) : Module.End ℝ 𝓓'(Ω, ℝ) :=
    (Distribution.lineDerivCLM (EuclideanSpace.single k (1 : ℝ))).toLinearMap
  have hD (k l : Fin n) : Commute (D k) (D l) :=
    Distribution.lineDerivEnd_commute _ _
  have hclosed (k l : Fin n) :=
    lineDeriv_residual_eq_of_minimizes_energy f u hu hmin k l
  simp only [residual_eq_sum_second_add] at hclosed
  have h := PDE.Analysis.sum_second_antisymmetric_eq_of_closed_residual D hD
    (fun k ↦ Distribution.ofLp Ω 2 (baseCoordCLM (u k)))
    (fun k ↦ Distribution.ofFun Ω (fun x ↦ f x k) volume ⊤) hclosed i j
  rw [LineDeriv.laplacianCLM_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [EuclideanSpace.basisFun_apply, Distribution.lineDerivOp_eq_lineDerivCLM,
    ofLp_vorticity]
  exact h

/-- Incompressibility expresses the Laplacian through first derivatives of
the L² vorticity tensor, including its precise index and sign convention. -/
theorem sum_lineDeriv_vorticity_eq_residual_sub_force
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0) (j : Fin n) :
    (∑ i : Fin n, Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
      (Distribution.ofLp Ω 2 (vorticity u i j))) =
      residual f u j - Distribution.ofFun Ω (fun x ↦ f x j) volume ⊤ := by
  let D (k : Fin n) : Module.End ℝ 𝓓'(Ω, ℝ) :=
    (Distribution.lineDerivCLM (EuclideanSpace.single k (1 : ℝ))).toLinearMap
  have hD (k l : Fin n) : Commute (D k) (D l) :=
    Distribution.lineDerivEnd_commute _ _
  have hdiv :
      (∑ i : Fin n, D i (Distribution.ofLp Ω 2 (baseCoordCLM (u i)))) = 0 := by
    change (∑ i : Fin n, Distribution.lineDerivCLM _
      (Distribution.ofLp Ω 2 (baseCoordCLM (u i)))) = 0
    simp only [lineDeriv_base, ← map_sum, ← divergence_apply, hu, map_zero]
  rw [residual_eq_sum_second_add, add_sub_cancel_right]
  simp only [ofLp_vorticity]
  exact PDE.Analysis.sum_deriv_antisymmetric_eq_of_divergence_zero D hD
    (fun k ↦ Distribution.ofLp Ω 2 (baseCoordCLM (u k))) hdiv j

end IncompressibleFlow.Stokes
