/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.Uniqueness

/-!
# Continuous-data Dirichlet spectral heat on bounded smooth domains

The domain geometry and a continuous function vanishing on the boundary determine
the pivot datum, eigenbasis, and convergent positive-time heat series. The prescribed
function supplies the time-zero representative. Smooth approximation and the maximum
principle give uniform initial attainment and joint continuity on closed cylinders.
The solution is unique against an independently supplied classical solution.

For continuous zero-boundary data this strengthens the strong `L²` initial attainment of
`Spectral.SmoothDomain` to uniform attainment.
-/

@[expose] public noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory HolderSpace Set Filter ParabolicMaximum
open scoped Sobolev Topology ContDiff

/-- Bounded smooth-domain geometry and continuous zero-boundary data alone construct a
classical Dirichlet heat series, continuous on closed cylinders and attaining its datum
uniformly. The same witnesses identify the pivot evolution and are unique in the natural
separate classical class, with differential hypotheses only in the open cylinder. -/
theorem exists_continuous_dirichletSpectralHeat {n : ℕ} [Fact (0 < n)]
    {Ω : Set (ℝ^n)} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, g x = 0) :
    ∃ (S : DirichletHeatSpectrum n Ω) (φ : ℕ → ℝ^n → ℝ)
      (u : ℝ → ℝ^n → ℝ) (v : ℝ → DerivLp n 2 Ω),
      (∀ i, φ i =ᵐ[domainMeasure n Ω] ⇑(S.basis i)) ∧
      (∀ i, ContDiffOn ℝ ∞ (φ i) Ω) ∧
      u 0 = g ∧
      Continuous v ∧
      (∀ t, ⇑(v t) =ᵐ[domainMeasure n Ω] u t) ∧
      Tendsto v (𝓝[>] 0) (𝓝 (continuousInitialL2 hopen hbounded hg hzero)) ∧
      (∀ T, ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.2 p.1) (closedCylinder Ω T)) ∧
      TendstoUniformlyOn u g (𝓝[>] 0) (closure Ω) ∧
      (∀ t, 0 < t → ContDiffOn ℝ ∞ (u t) Ω) ∧
      (∀ t, 0 < t → ∀ x ∈ Ω,
        HasDerivAt (fun s ↦ u s x) (PDE.laplacian (u t) x) t) ∧
      (∀ t, ∀ x ∈ frontier Ω, u t x = 0) ∧
      (∀ t, 0 < t → ∀ x ∈ closure Ω,
        HasSum (fun i ↦ Real.exp (-S.eigenvalue i * t) *
          S.basis.repr (continuousInitialL2 hopen hbounded hg hzero) i * φ i x) (u t x)) ∧
      (∀ T, 0 < T → ∀ z : ℝ^n → ℝ → ℝ,
        ContinuousOn (fun p : ℝ^n × ℝ ↦ z p.1 p.2) (closedCylinder Ω T) →
        (∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ z y t) x) →
        (∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
          HasDerivAt (z x) (PDE.laplacian (fun y ↦ z y t) x) t) →
        (∀ x ∈ closure Ω, z x 0 = g x) →
        (∀ x ∈ frontier Ω, ∀ t ∈ Icc 0 T, z x t = 0) →
        ∀ p ∈ closedCylinder Ω T, z p.1 p.2 = u p.2 p.1) := by
  let γ : Exponent := ⟨1 / 2, by norm_num, by norm_num⟩
  have hγ : (γ : ℝ) < 1 := by norm_num [γ]
  let S := dirichletHeatSpectrum (Fact.out : 0 < n) hopen hbounded hne
  let f := continuousInitialL2 hopen hbounded hg hzero
  have hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g :=
    continuousInitialL2_ae hopen hbounded hg hzero
  refine ⟨S, S.classicalEigenfunction hopen hbounded hgraph hγ,
    S.continuousDirichletHeat hopen hbounded hgraph hγ f g,
    S.dirichletHeatL2 hopen hbounded hgraph hγ f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact S.classicalEigenfunction_ae hopen hbounded hgraph hγ
  · exact S.contDiffOn_classicalEigenfunction hopen hbounded hgraph hγ
  · exact S.continuousDirichletHeat_zero hopen hbounded hgraph hγ f g
  · exact S.continuous_dirichletHeatL2 hopen hbounded hgraph hγ f
  · exact S.continuousDirichletHeat_ae hopen hbounded hgraph hγ f hf
  · exact S.tendsto_dirichletHeatL2_zero hopen hbounded hgraph hγ f
  · exact S.continuousOn_continuousDirichletHeat hopen hbounded hgraph hγ f hg hzero hf
  · exact S.tendstoUniformlyOn_continuousDirichletHeat_initial
      hopen hbounded hgraph hγ f hg hzero hf
  · intro t ht
    rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht]
    exact S.contDiffOn_classicalPower hopen hbounded hgraph hγ 0 f ht
  · intro t ht x hx
    exact S.hasDerivAt_continuousDirichletHeat_laplacian hopen hbounded hgraph hγ f g ht hx
  · intro t x hx
    exact S.continuousDirichletHeat_zero_on_frontier hopen hbounded hgraph hγ f hzero t hx
  · intro t ht x hx
    rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht]
    exact S.hasSum_classicalEigenfunction hopen hbounded hgraph hγ f ht hx
  · intro T hT z hz hzspace hzheat hzinitial hzboundary
    exact S.eq_continuousDirichletHeat_of_classical hopen hbounded hgraph hγ f hg hzero hf hT
      z hz hzspace hzheat hzinitial hzboundary

end HeatEquation
