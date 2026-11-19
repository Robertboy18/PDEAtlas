/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.Stability

/-!
# Uniform initial attainment on a smooth bounded domain

Uniform approximation by compact smooth data, their proved initial reconstruction,
and the supremum contraction yield uniform attainment of every continuous datum
vanishing on the boundary. The initial datum enters only through its natural pivot
class.
-/

@[expose] public noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory HolderSpace Set Filter
open scoped Sobolev Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A compactly supported domain test vanishes on the geometric boundary. -/
theorem testFunction_zero_on_frontier (hopen : IsOpen Ω) (φ : TestFunctionOn n Ω)
    {x : ℝ^n} (hx : x ∈ frontier Ω) : φ.1.toFun x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hnot : x ∉ Ω := (hopen.frontier_eq ▸ hx).2
  exact hnot (φ.2 hs)

namespace DirichletHeatSpectrum

variable [Fact (0 < n)] {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- The positive-time Dirichlet spectral heat series attains every continuous
zero-boundary datum uniformly on the domain closure. -/
theorem tendstoUniformlyOn_classicalPower_initial_of_continuousOn
    (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ} (hg : ContinuousOn g (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, g x = 0)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) :
    TendstoUniformlyOn (S.classicalPower hopen hbounded hgraph hγ 0 f) g
      (𝓝[>] (0 : ℝ)) (closure Ω) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨φ, hnear⟩ := exists_testFunction_uniform_approximation hopen hbounded hg hzero
    (show 0 < ε / 3 by positivity)
  have hevent := (S.eventually_testHeat_near_initial hopen hbounded hgraph hγ φ
    (show 0 < ε / 3 by positivity)).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  filter_upwards [hevent, self_mem_nhdsWithin] with t ht htpos
  intro x hx
  have hstab := S.norm_classicalPower_sub_le hopen hbounded hgraph hγ f
    (baseCoordCLM (testFunctionToH10 φ)) hg φ.1.continuous.continuousOn hzero
    (fun y hy ↦ testFunction_zero_on_frontier hopen φ hy) hf
    (baseCoordCLM_testFunction_apply_ae φ) (show 0 ≤ ε / 3 by positivity)
    (fun y hy ↦ by
      change ‖g y - φ.1.toFun y‖ ≤ _
      rw [norm_sub_rev, Real.norm_eq_abs]
      exact (hnear y hy).le)
    htpos hx
  have h₁ : dist (g x) (φ.1.toFun x) < ε / 3 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hnear x hx
  have h₂ := ht x hx
  rw [S.testHeat_of_pos hopen hbounded hgraph hγ 2 φ htpos] at h₂
  change dist (S.classicalPower hopen hbounded hgraph hγ 0
    (baseCoordCLM (testFunctionToH10 φ)) t x) (φ.1.toFun x) < ε / 3 at h₂
  have h₃ : dist (S.classicalPower hopen hbounded hgraph hγ 0
      (baseCoordCLM (testFunctionToH10 φ)) t x)
      (S.classicalPower hopen hbounded hgraph hγ 0 f t x) ≤ ε / 3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hstab
  have htri := dist_triangle (g x) (φ.1.toFun x)
    (S.classicalPower hopen hbounded hgraph hγ 0 f t x)
  have htri' := dist_triangle (φ.1.toFun x)
    (S.classicalPower hopen hbounded hgraph hγ 0 (baseCoordCLM (testFunctionToH10 φ)) t x)
    (S.classicalPower hopen hbounded hgraph hγ 0 f t x)
  rw [dist_comm _ (φ.1.toFun x)] at h₂
  linarith

end DirichletHeatSpectrum

end HeatEquation
