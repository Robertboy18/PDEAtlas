/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.FiniteTime

/-!
# Terminal Sobolev norm divergence of the constructed quadratic wave

The higher lifetime is positive and finite by local construction and
the Strauss obstruction. The norm-ball composition estimates give the
continuation alternative, hence the state norm tends to infinity at that
lifetime. The classical field below is linked to both components of this same
trajectory; no amplitude bound or continuation principle is a hypothesis.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev Topology

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- The natural H⁵ × H⁴ product norm tends to infinity as time approaches
the positive finite higher lifetime from the left. -/
theorem tendsto_norm_quadraticTrajectory
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    Tendsto (fun t ↦ ‖quadraticTrajectory H t‖)
      (𝓝[<] (quadraticLifespan H).toReal) atTop := by
  have hfinite := quadraticLifespan_ne_top H hs hR hpositive
  have hT := quadratic_terminalTime_pos H hs hR hpositive
  have hlarge := higherSmooth_maximal_norm_eventually_gt
    (by norm_num : (3 : ℝ) < 2 * ((4 : ℝ) - 1)) contDiff_neg_sq (by simp)
    (0, lowerOrderCLM (by omega : 4 ≤ 5) H) hfinite
  refine tendsto_atTop.2 fun B ↦ ?_
  obtain ⟨ε, hε, hbound⟩ := hlarge B
  filter_upwards [Ioo_mem_nhdsLT
    (max_lt hT (sub_lt_self (quadraticLifespan H).toReal hε))] with t ht
  have ht0 : 0 ≤ t := ((le_max_left 0 _).trans_lt ht.1).le
  have hgap : (quadraticLifespan H).toReal - t < ε := by
    have hlow := (le_max_right 0 _).trans_lt ht.1
    linarith
  exact (hbound t ⟨ht0, ht.2⟩ hgap).le

/-- Equivalently, the sum of the displacement H⁵ norm and velocity
H⁴ norm tends to infinity; this is not merely a limsup statement. -/
theorem tendsto_norm_sum_quadraticTrajectory
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    Tendsto (fun t ↦ ‖(quadraticTrajectory H t).1‖ + ‖(quadraticTrajectory H t).2‖)
      (𝓝[<] (quadraticLifespan H).toReal) atTop := by
  apply tendsto_atTop_mono (fun t ↦ ?_) (tendsto_norm_quadraticTrajectory H hs hR hpositive)
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

/-- The classical PDE and both time traces hold up to the constructed
terminal time, with pointwise displacement and velocity equal to the higher
trajectory whose norm diverges there. -/
theorem exists_classical_quadratic_terminal
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    ∃ u : ℝ^4 → ℝ,
      IsSolutionBefore (fun z ↦ -(z ^ 2)) (fun _ ↦ 0)
        (classicalRepresentativeCLM (by norm_num) H) (quadraticLifespan H).toReal u ∧
      ∀ t ∈ Ico 0 (quadraticLifespan H).toReal, ∀ x,
        u (timeSpaceCons t x) =
          classicalRepresentativeCLM (by norm_num) (quadraticTrajectory H t).1 x ∧
        (∂[0] u) (timeSpaceCons t x) =
          classicalRepresentativeCLM (by norm_num) (quadraticTrajectory H t).2 x := by
  have hR : 0 < R := by
    by_contra hR
    have hzero : ∀ᵐ x, classicalRepresentativeCLM (by norm_num) H x = 0 := by
      filter_upwards [(Set.countable_singleton (0 : ℝ^3)).ae_notMem volume] with x hx
      exact hs x ((not_lt.mp hR).trans_lt (norm_pos_iff.mpr hx))
    rw [integral_eq_zero_of_ae hzero] at hpositive
    exact lt_irrefl 0 hpositive
  exact exists_classical_maximal_observation (k := 3) (by norm_num) (by norm_num) (by norm_num)
    contDiff_neg_sq (by simp) H (quadraticLifespan_ne_top H hs hR hpositive)

/-- No higher mild solution with the same data can include the terminal
time. This maximality is asserted in H⁵ × H⁴, not over all C² competitors. -/
theorem not_exists_quadratic_mild_at_terminal
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    ¬ ∃ τ : ℝ≥0, (quadraticLifespan H).toReal ≤ (τ : ℝ) ∧
      ∃ V : C(Icc (0 : ℝ) (τ : ℝ), W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3)),
        (higherLinearSemigroup 3 4).IsMildSolutionOn quadraticStateMap
          (0, lowerOrderCLM (by omega : 4 ≤ 5) H) τ V :=
  (higherLinearSemigroup 3 4).not_exists_mildSolutionOn_at_or_after_lifespan
    locallyLipschitz_quadraticStateMap _ (quadraticLifespan_ne_top H hs hR hpositive)

end WaveEquation.SmallData.Classical.NormBlowup
