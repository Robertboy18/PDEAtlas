/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.TestData
public import PDE.Parabolic.Heat.MaximumPrinciple

/-!
# Maximum principle for the reconstructed test-data heat orbit

The elliptic reconstruction provides continuity at time zero for compact smooth data.
The general parabolic maximum principle then gives a supremum bound independent of time.
This bound will survive uniform approximation of continuous zero-boundary data.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace HolderSpace Set Filter ParabolicMaximum
open scoped Sobolev Topology ContDiff

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- Test-data heat reconstruction is jointly continuous through the initial time. -/
theorem continuousOn_testHeat_field (φ : TestFunctionOn n Ω) (T : ℝ) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      (S.testHeat hopen hbounded hgraph hγ 2 φ p.2).interiorDerivative 0 p.1)
      (closedCylinder Ω T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have ht : Continuous (fun p : closedCylinder Ω T ↦
      S.testHeat hopen hbounded hgraph hγ 2 φ p.1.2) :=
    (S.continuous_testHeat hopen hbounded hgraph hγ 2 φ).comp
      (continuous_snd.comp continuous_subtype_val)
  have hx : Continuous (fun p : closedCylinder Ω T ↦ (⟨p.1.1, p.2.1⟩ : closure Ω)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have he := ((CKGammaOn.derivativeCLM (0 : MultiIndex n 2)).continuous.comp ht).eval hx
  convert he using 1
  funext p
  exact CKGammaOn.interiorDerivative_apply _ _ p.2.1

/-- The compact smooth orbit converges uniformly to its datum on the whole closure. -/
theorem eventually_testHeat_near_initial (φ : TestFunctionOn n Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 0, ∀ x ∈ closure Ω,
      dist ((S.testHeat hopen hbounded hgraph hγ 2 φ t).interiorDerivative 0 x)
        (φ.1.toFun x) < ε := by
  have hc := (CKGammaOn.derivativeCLM (0 : MultiIndex n 2)).continuous.comp
    (S.continuous_testHeat hopen hbounded hgraph hγ 2 φ)
  have he := (Metric.tendsto_nhds.mp (hc.continuousAt (x := 0)).tendsto) ε hε
  filter_upwards [he] with t ht x hx
  rw [← S.testHeat_zero hopen hbounded hgraph hγ 2 φ hx,
    CKGammaOn.interiorDerivative_apply _ _ hx, CKGammaOn.interiorDerivative_apply _ _ hx]
  exact (BoundedContinuousFunction.dist_coe_le_dist ⟨x, hx⟩).trans_lt ht

/-- The maximum principle bounds the spectral solution of a compact smooth datum
by its initial supremum, with no constant depending on time. -/
theorem norm_classicalPower_test_le (φ : TestFunctionOn n Ω) {M t : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ closure Ω, ‖φ.1.toFun x‖ ≤ M)
    (ht : 0 < t) {x : ℝ^n} (hx : x ∈ closure Ω) :
    ‖S.classicalPower hopen hbounded hgraph hγ 0 (baseCoordCLM (testFunctionToH10 φ)) t x‖
      ≤ M := by
  have hne : Ω.Nonempty := closure_nonempty_iff.mp ⟨x, hx⟩
  let u (y : ℝ^n) (s : ℝ) :=
    (S.testHeat hopen hbounded hgraph hγ 2 φ s).interiorDerivative 0 y
  have heq {s : ℝ} (hs : 0 < s) :
      (fun y ↦ u y s) =
        S.classicalPower hopen hbounded hgraph hγ 0 (baseCoordCLM (testFunctionToH10 φ)) s := by
    unfold u
    rw [S.testHeat_of_pos hopen hbounded hgraph hγ 2 φ hs]
    rfl
  have hd (y : ℝ^n) (hy : y ∈ Ω) (s : ℝ) (hs : 0 < s) :
      HasDerivAt (u y) (PDE.laplacian (fun z ↦ u z s) y) s := by
    rw [heq hs]
    apply (S.hasDerivAt_classicalPower_laplacian hopen hbounded hgraph hγ 0
      (baseCoordCLM (testFunctionToH10 φ)) hs hy).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hs] with r hr
    exact congr_fun (heq hr) y
  have hc := S.continuousOn_testHeat_field hopen hbounded hgraph hγ φ t
  have hspace (y : ℝ^n) (hy : y ∈ Ω) (s : ℝ) (hs : s ∈ Ioo 0 t) :
      ContDiffAt ℝ 2 (fun z ↦ u z s) y := by
    rw [heq hs.1]
    exact ((S.contDiffOn_classicalPower hopen hbounded hgraph hγ 0
      (baseCoordCLM (testFunctionToH10 φ)) hs.1).of_le
        (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt (hopen.mem_nhds hy)
  have hb (p : ℝ^n × ℝ) (hp : p ∈ parabolicBoundary Ω t) : ‖u p.1 p.2‖ ≤ M := by
    rcases hp with hp | hp
    · by_cases hs : 0 < p.2
      · rw [congr_fun (heq hs) p.1,
          S.classicalPower_zero_on_frontier hopen hbounded hgraph hγ 0 _ hs p.1 hp.1,
          norm_zero]
        exact hM
      · have hz : p.2 = 0 := le_antisymm (le_of_not_gt hs) hp.2.1
        change ‖(S.testHeat hopen hbounded hgraph hγ 2 φ p.2).interiorDerivative 0 p.1‖ ≤ M
        rw [hz, S.testHeat_zero hopen hbounded hgraph hγ 2 φ (frontier_subset_closure hp.1)]
        exact hbound p.1 (frontier_subset_closure hp.1)
    · have hz : p.2 = 0 := hp.2
      change ‖(S.testHeat hopen hbounded hgraph hγ 2 φ p.2).interiorDerivative 0 p.1‖ ≤ M
      rw [hz, S.testHeat_zero hopen hbounded hgraph hγ 2 φ hp.1]
      exact hbound p.1 hp.1
  have hop (y : ℝ^n) (hy : y ∈ Ω) (s : ℝ) (hs : s ∈ Ioo 0 t) :
      heatParabolicOperator u y s = 0 := by
    rw [heatParabolicOperator, (hd y hy s hs.1).deriv, sub_self]
  have hup := heat_subsolution_le_of_boundary_le hopen hne hbounded.isCompact_closure ht u
    hc hspace (fun y hy s hs ↦ (hd y hy s hs.1).differentiableAt)
    (fun y hy s hs ↦ le_of_eq (hop y hy s hs))
    (fun p hp ↦ (le_abs_self _).trans (hb p hp)) (x, t) ⟨hx, ht.le, le_rfl⟩
  have hlo := boundary_le_heat_supersolution hopen hne hbounded.isCompact_closure ht u
    hc hspace (fun y hy s hs ↦ (hd y hy s hs.1).differentiableAt)
    (fun y hy s hs ↦ le_of_eq (hop y hy s hs).symm)
    (fun p hp ↦ neg_le.mp ((neg_le_abs _).trans (hb p hp)))
    (x, t) ⟨hx, ht.le, le_rfl⟩
  rw [← congr_fun (heq ht) x, Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlo, hup⟩

end HeatEquation.DirichletHeatSpectrum
