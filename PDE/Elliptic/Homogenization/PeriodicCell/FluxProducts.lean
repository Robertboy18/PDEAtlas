/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.FluxDistribution
public import PDE.Elliptic.Homogenization.PeriodicCell.FluxAveraging
public import PDE.Elliptic.Homogenization.PeriodicCell.Compactness
public import PDE.Spaces.Sobolev.Periodic.FluxProducts

/-!
# Compensated cell-flux products along Dirichlet subsequences

Periodic flux testing and strong L² compactness identify weighted pairings of the
constructed cell fluxes with the gradients of varying zero-boundary Sobolev functions.
For nonsymmetric coefficients the adjoint construction gives the adjoint effective
flux. A common subsequence of the Dirichlet solutions satisfies these limits
for all cell directions and smooth cutoffs. The Dirichlet solution flux is then
identified from its loaded weak equation with the rescaled cell potentials
(`PeriodicCell.OscillatingTests`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open PDE.Analysis.PeriodicAveraging SobolevSpace.Periodic
open scoped ENNReal Topology InnerProductSpace Sobolev Distributions

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]

include hΩo

/-- The cell flux can be paired with gradients of a strongly L²-convergent
zero-boundary Sobolev family. Its limit is the derived effective flux pairing. -/
theorem tendsto_inner_cellFlux_weighted_gradient
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (u : ι → H¹₀(Ω)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ SobolevSpace.GraphSpace.baseCoordCLM (u j)) l
      (𝓝 (SobolevSpace.GraphSpace.baseCoordCLM U)))
    (ξ : ℝ^n) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Tendsto (fun j ↦ ⟪rescaleLp hΩ (ε j) (hε j) (hε1 j)
      (coefficientOperator A (correctedField A hα hA ξ)),
      SobolevSpace.GraphSpace.testFunctionLpTop (Ω := Ω) κ •
        SobolevSpace.GraphSpace.gradientCLM (u j)⟫_ℝ) l
      (𝓝 ⟪Lp.const 2 (volume.restrict Ω) (effectiveOperator A hα hA ξ),
        SobolevSpace.GraphSpace.testFunctionLpTop (Ω := Ω) κ •
          SobolevSpace.GraphSpace.gradientCLM U⟫_ℝ) := by
  have hmean : (∫ y, coefficientOperator A (correctedField A hα hA ξ) y
      ∂cellMeasure n) = effectiveOperator A hα hA ξ :=
    (integral_congr_ae (coefficientOperator_ae A _)).trans
      (effectiveOperator_eq_mean_flux A hα hA ξ).symm
  simpa only [hmean] using tendsto_inner_rescale_weighted_gradient hΩ hΩo
    (coefficientOperator A (correctedField A hα hA ξ))
    (cellFlux_orthogonal_periodicGradient A hα hA ξ) ε hε hε1 ht u U hu κ

/-- The corresponding compensated pairing for the adjoint correctors has the
adjoint effective matrix in its limit, without a symmetry assumption on A. -/
theorem tendsto_inner_adjointCellFlux_weighted_gradient
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (u : ι → H¹₀(Ω)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ SobolevSpace.GraphSpace.baseCoordCLM (u j)) l
      (𝓝 (SobolevSpace.GraphSpace.baseCoordCLM U)))
    (ξ : ℝ^n) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Tendsto (fun j ↦ ⟪rescaleLp hΩ (ε j) (hε j) (hε1 j)
      (coefficientOperator (adjointCoefficient A)
        (correctedField (adjointCoefficient A) hα
          (adjointCoefficient_elliptic A hA) ξ)),
      SobolevSpace.GraphSpace.testFunctionLpTop (Ω := Ω) κ •
        SobolevSpace.GraphSpace.gradientCLM (u j)⟫_ℝ) l
      (𝓝 ⟪Lp.const 2 (volume.restrict Ω) ((effectiveOperator A hα hA).adjoint ξ),
        SobolevSpace.GraphSpace.testFunctionLpTop (Ω := Ω) κ •
          SobolevSpace.GraphSpace.gradientCLM U⟫_ℝ) := by
  simpa only [effectiveOperator_adjoint A hα hA] using
    tendsto_inner_cellFlux_weighted_gradient (adjointCoefficient A) hα
      (adjointCoefficient_elliptic A hA) hΩ hΩo ε hε hε1 ht u U hu ξ κ

/-- A single subsequence of the constructed Dirichlet solutions has weak H¹₀ and
strong L² limits and the compensated limits against every adjoint cell flux.
This proves the cell-flux side of oscillating-test identification. -/
theorem exists_subseq_rescaledDirichletSolution_adjointFlux_products
    (hn : 0 < n) (f : SobolevSpace.GraphSpace.DerivLp n 2 Ω)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) :
    ∃ (u : H¹₀(Ω)) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (fun j ↦ toWeakSpace ℝ (H¹₀(Ω))
        (rescaledDirichletSolution A hα hA hn hΩ
          (ε (ns j)) (hε (ns j)).ne' f)) atTop
        (𝓝 (toWeakSpace ℝ (H¹₀(Ω)) u)) ∧
      Tendsto (fun j ↦ SobolevSpace.GraphSpace.baseCoordCLM
        (rescaledDirichletSolution A hα hA hn hΩ
          (ε (ns j)) (hε (ns j)).ne' f)) atTop
        (𝓝 (SobolevSpace.GraphSpace.baseCoordCLM u)) ∧
      ∀ (ξ : ℝ^n) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
        Tendsto (fun j ↦ ⟪rescaleLp hΩ (ε (ns j)) (hε (ns j)) (hε1 (ns j))
          (coefficientOperator (adjointCoefficient A)
            (correctedField (adjointCoefficient A) hα
              (adjointCoefficient_elliptic A hA) ξ)),
          SobolevSpace.GraphSpace.testFunctionLpTop (Ω := Ω) κ •
            SobolevSpace.GraphSpace.gradientCLM
              (rescaledDirichletSolution A hα hA hn hΩ
                (ε (ns j)) (hε (ns j)).ne' f)⟫_ℝ) atTop
          (𝓝 ⟪Lp.const 2 (volume.restrict Ω) ((effectiveOperator A hα hA).adjoint ξ),
            SobolevSpace.GraphSpace.testFunctionLpTop (Ω := Ω) κ •
              SobolevSpace.GraphSpace.gradientCLM u⟫_ℝ) := by
  obtain ⟨u, ns, hns, hu, hbase⟩ := exists_subseq_rescaledDirichletSolution
    A hα hA hn hΩ hΩo f ε (fun j ↦ (hε j).ne')
  refine ⟨u, ns, hns, hu, hbase, fun ξ κ ↦ ?_⟩
  exact tendsto_inner_adjointCellFlux_weighted_gradient A hα hA hΩ hΩo
    (fun j ↦ ε (ns j)) (fun j ↦ hε (ns j)) (fun j ↦ hε1 (ns j))
    (ht.comp hns.tendsto_atTop)
    (fun j ↦ rescaledDirichletSolution A hα hA hn hΩ
      (ε (ns j)) (hε (ns j)).ne' f) u hbase ξ κ

end PDE.Elliptic.Homogenization.PeriodicCell
