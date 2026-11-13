/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.Properties
public import PDE.Analysis.Convex.Extended.LinearImage.Subdifferential
public import PDE.Analysis.Calculus.ConvexIntegral.Derivative
public import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition

/-!
# First variation and the ambient L² subgradient

The Lipschitz gradient acts continuously on vector-valued `L²`, including
its constant part on a bounded domain. The two supporting-hyperplane
inequalities differentiate the integral. Ambient subgradients consequently
satisfy the weak divergence equation against every `H¹₀` test.

The coordinate flux in the final equivalence is tied almost everywhere
to the gradient of the density. The elliptic regularity argument starts
from this equivalence.
-/

open scoped Sobolev Gradient

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

local notation "μ" => domainMeasure n Ω

/-- The derivative of the Dirichlet integral pairs the weak gradient
with the pointwise gradient of the density. -/
theorem hasFDerivAt_dirichletGradientIntegralEnergy
    (hbounded : Bornology.IsBounded Ω) (hL : ConvexOn ℝ univ L)
    (hd : Differentiable ℝ L) {C : ℝ≥0} (hLip : LipschitzWith C (∇ L))
    (hint : ∀ w : H¹₀(Ω), Integrable (fun x ↦ L (∇ (w : H¹(Ω)) x)) μ)
    (u : H¹₀(Ω)) (q : Lp (ℝ^n) 2 μ)
    (hq : q =ᵐ[μ] fun x ↦ ∇ L (∇ (u : H¹(Ω)) x)) :
    HasFDerivAt (E := H¹₀(Ω)) (dirichletGradientIntegralEnergy (fun _ ↦ L))
      ((innerSL ℝ q).comp gradientCLM) u := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hmem (w : Lp (ℝ^n) 2 μ) : MemLp (fun x ↦ ∇ L (w x)) 2 μ :=
    hLip.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp w)
  let N := Lp.superposition (fun _ : ℝ^n ↦ ∇ L) hmem
  have hN : Continuous N := (hLip.lipschitzWith_superposition hmem).continuous
  have hq' : N (∇ (u : H¹(Ω))) = q :=
    Lp.ext ((Lp.coeFn_superposition _ hmem (∇ (u : H¹(Ω)))).trans hq.symm)
  have h := Analysis.Calculus.hasFDerivAt_integral_convex_potential_of_integrable
    (gradientCLM (n := n) (Ω := Ω)) hL
    (fun x ↦ (hd x).hasGradientAt.hasFDerivAt) (fun w ↦ N (∇ (w : H¹(Ω))))
    (fun w ↦ Lp.coeFn_superposition _ hmem (∇ (w : H¹(Ω))))
    hint u (hN.comp gradientCLM.continuous).continuousAt
  rw [hq'] at h
  convert h using 1
  rfl

/-- Under Hessian bounds, the ambient subgradient condition is exactly
the weak equation `-div DL(Du) = f`. -/
theorem mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (u : H¹₀(Ω)) (f : DerivLp n 2 Ω) (q : Fin n → DerivLp n 2 Ω)
    (hq : ∀ᵐ x ∂μ, ∇ L (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
      WithLp.toLp 2 (fun i ↦ q i x)) :
    f ∈ subdifferential (l2DirichletGradientEnergy (Ω := Ω) L) (baseCoordCLM u) ↔
      ∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫ := by
  have hconvex := ((Analysis.strongConvexOn_of_hessian_bound hL hlower).strictConvexOn
    hθ).convexOn
  have hint := integrable_gradientDensity_of_hessian_bounds hbounded hL hθ
    C.coe_nonneg hlower hupper
  have hpair (v : H¹₀(Ω)) :
      ⟪Lp.euclideanTuple q, ∇ (v : H¹(Ω))⟫ = ∑ i, ⟪q i, derivCoordCLM i v⟫ := by
    have hv : ∇ (v : H¹(Ω)) = Lp.euclideanTuple (fun i ↦ derivCoordCLM i v) := by
      apply Lp.ext
      filter_upwards [gradientCLM_apply_ae v,
        Lp.euclideanTuple_apply_ae (fun i ↦ derivCoordCLM i v)] with x hx hy
      exact PiLp.ext fun i ↦ (hx i).trans (hy i).symm
    rw [hv, Lp.inner_euclideanTuple]
  have hqa : Lp.euclideanTuple q =ᵐ[μ] fun x ↦ ∇ L (∇ (u : H¹(Ω)) x) := by
    filter_upwards [hq, gradientCLM_apply_ae u, Lp.euclideanTuple_apply_ae q] with x hx hu hq'
    have hu' : ∇ (u : H¹(Ω)) x = WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x) :=
      PiLp.ext hu
    rw [hu', hx]
    exact PiLp.ext hq'
  have hderiv := hasFDerivAt_dirichletGradientIntegralEnergy hbounded hconvex
    (hL.differentiable (by norm_num))
    (Analysis.lipschitzWith_gradient_of_hessian_bound hL hupper) hint u
    (Lp.euclideanTuple q) hqa
  have hc : ConvexOn ℝ univ (dirichletGradientIntegralEnergy (fun _ ↦ L) :
      H¹₀(Ω) → ℝ) :=
    convexOn_integral_Lp_comp gradientCLM.toLinearMap
      (Filter.Eventually.of_forall fun _ ↦ hconvex) hint
  rw [l2DirichletGradientEnergy, mem_subdifferential_linearImageEnergy_iff
    (V := H¹₀(Ω)) _ (baseCoordCLM_injective hΩ) hc hderiv]
  constructor
  · intro h v
    have hv := congrArg (fun D : H¹₀(Ω) →L[ℝ] ℝ ↦ D v) h
    exact (hpair v).symm.trans hv
  · intro h
    ext v
    exact (hpair v).trans (h v)

end PDE.CalculusOfVariations
