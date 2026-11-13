/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletInitial

/-!
# Dirichlet spectral heat from bounded smooth-domain geometry

A nonempty bounded open subset of positive-dimensional Euclidean space with smooth
graph boundary admits a classical positive-time Dirichlet heat solution for every
real `L²` initial class. The eigenbasis, its smooth representatives, and convergence
of the heat series are constructed from the variational spectral theorem and global
elliptic regularity.

The initial topology here is strong `L²`. Spatial smoothness holds in the open domain,
and the positive-time function is continuous on the closure with zero boundary values.
The supporting modules give convergence and time smoothness in every classical Hölder
derivative graph.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace HolderSpace MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A classical Dirichlet heat series constructed solely from smooth bounded-domain
geometry and arbitrary `L²` data. The same witnesses give the normalized eigenfunction
series, heat PDE, geometric boundary values, and strong initial trace. -/
theorem exists_classical_dirichletSpectralHeat {n : ℕ} [Fact (0 < n)]
    {Ω : Set (ℝ^n)} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    (f : DerivLp n 2 Ω) :
    ∃ (S : DirichletHeatSpectrum n Ω) (φ : ℕ → ℝ^n → ℝ)
      (u : ℝ → ℝ^n → ℝ) (v : ℝ → DerivLp n 2 Ω),
      (∀ i, φ i =ᵐ[domainMeasure n Ω] ⇑(S.basis i)) ∧
      (∀ i, ContDiffOn ℝ ∞ (φ i) Ω) ∧
      (∀ t, MemLp (u t) 2 (domainMeasure n Ω)) ∧
      (∀ t, ⇑(v t) =ᵐ[domainMeasure n Ω] u t) ∧
      u 0 = f ∧
      Continuous v ∧
      Tendsto v (𝓝[>] 0) (𝓝 f) ∧
      Continuous (fun p : Ioi (0 : ℝ) × closure Ω ↦ u p.1 p.2) ∧
      (∀ t, 0 < t → ContDiffOn ℝ ∞ (u t) Ω) ∧
      (∀ t, 0 < t → ContinuousOn (u t) (closure Ω)) ∧
      (∀ t, 0 < t → ∀ x ∈ Ω,
        HasDerivAt (fun s ↦ u s x) (PDE.laplacian (u t) x) t) ∧
      (∀ t, 0 < t → ∀ x ∈ frontier Ω, u t x = 0) ∧
      (∀ t, 0 < t → ∀ x ∈ closure Ω,
        HasSum (fun i ↦ Real.exp (-S.eigenvalue i * t) * S.basis.repr f i * φ i x)
          (u t x)) := by
  let γ : Exponent := ⟨1 / 2, by norm_num, by norm_num⟩
  have hγ : (γ : ℝ) < 1 := by norm_num [γ]
  let S := dirichletHeatSpectrum (Fact.out : 0 < n) hopen hbounded hne
  refine ⟨S, S.classicalEigenfunction hopen hbounded hgraph hγ,
    S.dirichletHeat hopen hbounded hgraph hγ f,
    S.dirichletHeatL2 hopen hbounded hgraph hγ f, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact S.classicalEigenfunction_ae hopen hbounded hgraph hγ
  · exact S.contDiffOn_classicalEigenfunction hopen hbounded hgraph hγ
  · exact S.memLp_dirichletHeat hopen hbounded hgraph hγ f
  · intro t
    exact (S.memLp_dirichletHeat hopen hbounded hgraph hγ f t).coeFn_toLp
  · exact S.dirichletHeat_zero hopen hbounded hgraph hγ f
  · exact S.continuous_dirichletHeatL2 hopen hbounded hgraph hγ f
  · exact S.tendsto_dirichletHeatL2_zero hopen hbounded hgraph hγ f
  · apply (S.continuous_holderPower_derivative hopen hbounded hgraph hγ 2 0 0 f).congr
    intro p
    rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f p.1.property,
      DirichletHeatSpectrum.classicalPower,
      CKGammaOn.interiorDerivative_apply _ _ p.2.property]
  · intro t ht
    rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht]
    exact S.contDiffOn_classicalPower hopen hbounded hgraph hγ 0 f ht
  · intro t ht
    rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht]
    exact S.continuousOn_classicalPower hopen hbounded hgraph hγ 0 f t
  · intro t ht x hx
    exact S.hasDerivAt_dirichletHeat_laplacian hopen hbounded hgraph hγ f ht hx
  · intro t ht
    rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht]
    exact S.classicalPower_zero_on_frontier hopen hbounded hgraph hγ 0 f ht
  · intro t ht x hx
    rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht]
    exact S.hasSum_classicalEigenfunction hopen hbounded hgraph hγ f ht hx

end HeatEquation
