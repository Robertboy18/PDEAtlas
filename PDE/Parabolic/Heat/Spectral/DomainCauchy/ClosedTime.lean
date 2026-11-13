/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.Initial

/-!
# A continuous closed-time representative of the domain heat series

The prescribed continuous datum defines the representative at time zero. At positive
times this is the same classical spectral sum. The supremum contraction makes the
compact smooth approximations uniform on every closed cylinder, proving joint
continuity through the initial boundary as well as the uniform initial trace.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory HolderSpace Set Filter ParabolicMaximum
open scoped Sobolev Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- The continuous datum is the initial representative, while positive times are given
by the classical Dirichlet eigenfunction series `S.classicalPower`. -/
def continuousDirichletHeat (f : DerivLp n 2 Ω) (g : ℝ^n → ℝ) (t : ℝ) : ℝ^n → ℝ :=
  if 0 < t then S.classicalPower hopen hbounded hgraph hγ 0 f t else g

/-- At time zero the representative equals the prescribed function pointwise. -/
@[simp] theorem continuousDirichletHeat_zero (f : DerivLp n 2 Ω) (g : ℝ^n → ℝ) :
    S.continuousDirichletHeat hopen hbounded hgraph hγ f g 0 = g := by
  simp [continuousDirichletHeat]

/-- The closed-time representative retains the constructed spectral solution at positive time. -/
theorem continuousDirichletHeat_of_pos (f : DerivLp n 2 Ω) (g : ℝ^n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    S.continuousDirichletHeat hopen hbounded hgraph hγ f g t =
      S.classicalPower hopen hbounded hgraph hγ 0 f t :=
  ite_eq_left ht

/-- Uniform smooth approximation on every closed cylinder proves joint continuity,
including the initial face and its intersection with the lateral boundary. -/
theorem continuousOn_continuousDirichletHeat (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ}
    (hg : ContinuousOn g (closure Ω)) (hzero : ∀ x ∈ frontier Ω, g x = 0)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) (T : ℝ) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      S.continuousDirichletHeat hopen hbounded hgraph hγ f g p.2 p.1)
      (closedCylinder Ω T) := by
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨φ, hnear⟩ := exists_testFunction_uniform_approximation hopen hbounded hg hzero
    (half_pos hε)
  refine ⟨fun p : ℝ^n × ℝ ↦
    (S.testHeat hopen hbounded hgraph hγ 2 φ p.2).interiorDerivative 0 p.1,
    S.continuousOn_testHeat_field hopen hbounded hgraph hγ φ T, ?_⟩
  intro p hp
  apply hεV
  change dist (S.continuousDirichletHeat hopen hbounded hgraph hγ f g p.2 p.1)
    ((S.testHeat hopen hbounded hgraph hγ 2 φ p.2).interiorDerivative 0 p.1) < ε
  by_cases ht : 0 < p.2
  · rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht,
      S.testHeat_of_pos hopen hbounded hgraph hγ 2 φ ht]
    change dist (S.classicalPower hopen hbounded hgraph hγ 0 f p.2 p.1)
      (S.classicalPower hopen hbounded hgraph hγ 0
        (baseCoordCLM (testFunctionToH10 φ)) p.2 p.1) < ε
    rw [dist_eq_norm]
    exact (S.norm_classicalPower_sub_le hopen hbounded hgraph hγ f
      (baseCoordCLM (testFunctionToH10 φ)) hg φ.1.continuous.continuousOn hzero
      (fun y hy ↦ testFunction_zero_on_frontier hopen φ hy) hf
      (baseCoordCLM_testFunction_apply_ae φ) (half_pos hε).le
      (fun y hy ↦ by
        change ‖g y - φ.1.toFun y‖ ≤ _
        rw [norm_sub_rev, Real.norm_eq_abs]
        exact (hnear y hy).le)
      ht hp.1).trans_lt (half_lt_self hε)
  · have hz : p.2 = 0 := le_antisymm (le_of_not_gt ht) hp.2.1
    rw [hz, S.continuousDirichletHeat_zero hopen hbounded hgraph hγ,
      S.testHeat_zero hopen hbounded hgraph hγ 2 φ hp.1]
    exact (show dist (g p.1) (φ.1.toFun p.1) < ε / 2 by
      simpa only [Real.dist_eq, abs_sub_comm] using hnear p.1 hp.1).trans (half_lt_self hε)

/-- The closed-time representative attains the initial data uniformly from positive time. -/
theorem tendstoUniformlyOn_continuousDirichletHeat_initial
    (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ} (hg : ContinuousOn g (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, g x = 0)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) :
    TendstoUniformlyOn (S.continuousDirichletHeat hopen hbounded hgraph hγ f g) g
      (𝓝[>] (0 : ℝ)) (closure Ω) := by
  apply (S.tendstoUniformlyOn_classicalPower_initial_of_continuousOn
    hopen hbounded hgraph hγ f hg hzero hf).congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x _
  exact congr_fun (S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht).symm x

/-- The scalar derivative of the closed-time representative is its Laplacian
at every positive time and every interior point. -/
theorem hasDerivAt_continuousDirichletHeat_laplacian (f : DerivLp n 2 Ω) (g : ℝ^n → ℝ)
    {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : x ∈ Ω) :
    HasDerivAt (fun s ↦ S.continuousDirichletHeat hopen hbounded hgraph hγ f g s x)
      (PDE.laplacian (S.continuousDirichletHeat hopen hbounded hgraph hγ f g t) x) t := by
  rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht]
  apply (S.hasDerivAt_classicalPower_laplacian hopen hbounded hgraph hγ 0 f ht hx)
    |>.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g hs]

/-- The continuous representative vanishes on the boundary also at time zero. -/
theorem continuousDirichletHeat_zero_on_frontier (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ}
    (hzero : ∀ x ∈ frontier Ω, g x = 0) (t : ℝ) {x : ℝ^n} (hx : x ∈ frontier Ω) :
    S.continuousDirichletHeat hopen hbounded hgraph hγ f g t x = 0 := by
  by_cases ht : 0 < t
  · rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht]
    exact S.classicalPower_zero_on_frontier hopen hbounded hgraph hγ 0 f ht x hx
  · simp only [continuousDirichletHeat, ite_eq_right ht]
    exact hzero x hx

/-- The continuous representative is exactly the sealed spectral pivot trajectory
almost everywhere, including its initial time. -/
theorem continuousDirichletHeat_ae (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ}
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) (t : ℝ) :
    (S.dirichletHeatL2 hopen hbounded hgraph hγ f t : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      S.continuousDirichletHeat hopen hbounded hgraph hγ f g t := by
  by_cases ht : 0 < t
  · have h := (S.memLp_dirichletHeat hopen hbounded hgraph hγ f t).coeFn_toLp
    change (S.dirichletHeatL2 hopen hbounded hgraph hγ f t : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      S.dirichletHeat hopen hbounded hgraph hγ f t at h
    simpa only [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht,
      S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht] using h
  · rw [S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ,
      Real.toNNReal_of_nonpos (le_of_not_gt ht), spectralHeatEvolution_zero]
    simpa only [continuousDirichletHeat, ite_eq_right ht] using hf

end HeatEquation.DirichletHeatSpectrum
