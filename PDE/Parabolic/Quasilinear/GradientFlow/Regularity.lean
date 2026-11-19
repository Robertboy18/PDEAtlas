/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Solution.Regularity
public import PDE.CalculusOfVariations.GradientEnergy.L2.Domain
public import PDE.Parabolic.Quasilinear.GradientFlow.Solution
public import PDE.Spaces.Sobolev.Calculus.Divergence.VectorValued

/-!
# Spatial and temporal regularity of gradient diffusion

The weak equation determines more regularity than its definition requires.
Elliptic regularity gives an `H²` time slice with norm controlled by the
`L²` velocity. The nonlinear flux then belongs to `H¹`, and its weak divergence
is the velocity itself.

Time regularity comes from the distributional equation: the continuous
trajectory is locally absolutely continuous, with strong derivative equal
to its prescribed velocity almost everywhere.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Quasilinear.GradientFlow.IsWeakSolution

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Convex PDE.Analysis.Evolution PDE.CalculusOfVariations
open scoped ENNReal Gradient NNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}
  {u g : ℝ → (ℝ^n →₂[domainMeasure n Ω] ℝ)}

/-- The weak time derivative is the strong `L²` derivative almost everywhere;
the solution is absolutely continuous on every finite time interval. -/
theorem regularity_Icc
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (hu : IsWeakSolution L u g) {T : ℝ} (hT : 0 < T) :
    AbsolutelyContinuousOnInterval u 0 T ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt u (g t) t :=
  ((isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper u g).mp hu).regularity_Icc hT

/-- One elliptic constant bounds the `H²` slices of every weak solution
by the corresponding `L²` velocities. The constant is chosen before the
trajectory or its velocity. -/
theorem exists_H2_bound_ae [Fact (0 < n)]
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u g : ℝ → (ℝ^n →₂[domainMeasure n Ω] ℝ), IsWeakSolution L u g →
        ∀ᵐ t ∂volume.restrict (Ioi 0), ∃ W : W^{2,2}(Ω),
          wkpBaseCoordinateCLM W = u t ∧
          lowerOrderCLM (by omega : 1 ≤ 2) W ∈
            (h10SubmoduleOn (n := n) (Ω := Ω)) ∧ ‖W‖ ≤ M * ‖g t‖ := by
  obtain ⟨M, hM, hregularity⟩ :=
    exists_H2_of_mem_subdifferential_l2DirichletGradientEnergy
      hΩ hbounded hgraph hL hθ hlower hupper
  refine ⟨M, hM, fun u g hu ↦ ?_⟩
  have hflow := (isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper u g).mp hu
  filter_upwards [hu.equation, hflow.inclusion] with t ht hf
  obtain ⟨w, hw, _⟩ := ht
  rw [← hw] at hf
  obtain ⟨W, hW, hbound⟩ := hregularity w (-g t) hf
  have hbase : wkpBaseCoordinateCLM W = baseCoordCLM w := by
    simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex, baseCoordCLM_apply] using
        congrArg wkpBaseCoordinateCLM hW
  refine ⟨W, hbase.trans hw, ?_, ?_⟩
  · rw [hW]
    exact w.property
  · simpa only [norm_neg] using hbound

/-- The nonlinear flux is an `H¹` vector field whose weak divergence equals
the velocity in `L²`. Its values are the gradient of the density,
evaluated on the solution's weak spatial gradient. -/
theorem ae_exists_flux [Fact (0 < n)] {Ω : TopologicalSpace.Opens ℝ^n}
    (hbounded : Bornology.IsBounded (Ω : Set (ℝ^n)))
    (hgraph : Boundary.HasContDiffGraphBoundary 2 (Ω : Set (ℝ^n)))
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    {u g : ℝ → (ℝ^n →₂[domainMeasure n Ω] ℝ)} (hu : IsWeakSolution L u g) :
    ∀ᵐ t ∂volume.restrict (Ioi 0), ∃ w : H¹₀(Ω), ∃ Q : W^{1,2}(Ω; ℝ^n),
      baseCoordCLM w = u t ∧
      ((Q.val (baseIndex n 1) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω]
        fun x ↦ ∇ L (∇ (w : H¹(Ω)) x)) ∧
      wkpBaseCoordinateCLM (∇· Q) = g t := by
  obtain ⟨_, _, hregularity⟩ :=
    exists_H2_of_mem_subdifferential_l2DirichletGradientEnergy
      Ω.isOpen hbounded hgraph hL hθ hlower hupper
  have hflow := (isWeakSolution_iff_isSubgradientFlow
    Ω.isOpen hbounded hL hθ hlower hupper u g).mp hu
  filter_upwards [hu.equation, hflow.inclusion] with t ht hf
  obtain ⟨w, hw, _⟩ := ht
  rw [← hw] at hf
  obtain ⟨W, hW, _⟩ := hregularity w (-g t) hf
  obtain ⟨q, hq, _, hoperator⟩ :=
    exists_flux_subdifferential_l2DirichletGradientEnergy_eq_singleton
      Ω.isOpen hbounded hgraph hL hθ hlower hupper W w hW
  have hvelocity : -g t = negativeDivergence q := by
    simpa only [hoperator, mem_singleton_iff] using hf
  refine ⟨w, VectorValued.ofComponentsCLM q, hw, ?_, ?_⟩
  · filter_upwards [VectorValued.ofComponentsCLM_coordinate_ae q (baseIndex n 1),
      hq, gradientCLM_apply_ae w] with x hx hqx hgrad
    rw [hx]
    have hgrad' : ∇ (w : H¹(Ω)) x =
        WithLp.toLp 2 (fun i ↦ derivCoordCLM i w x) := PiLp.ext hgrad
    rw [hgrad']
    exact PiLp.ext fun i ↦ hqx i
  · rw [VectorValued.divergence_ofComponentsCLM_baseCoordinate, ← hvelocity, neg_neg]

end PDE.Parabolic.Quasilinear.GradientFlow.IsWeakSolution
