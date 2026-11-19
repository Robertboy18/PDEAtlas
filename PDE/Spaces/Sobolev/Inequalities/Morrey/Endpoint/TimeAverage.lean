/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.Averages
public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.WeakGradient

/-!
# Initial Lipschitz bounds from positive-time weak gradients

Compact nonnegative time averages inherit the spatial weak gradient bound.
The bounded-gradient Morrey theorem gives Lipschitz representatives of these
averages. A uniform modulus towards a continuous initial function identifies
their limit, so the initial function has the same Lipschitz bound.

The spatial gradient is only bounded at positive times. Its nonpositive-time
values need not be bounded, and no initial Sobolev bound is assumed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions NNReal Topology

namespace SobolevSpace

variable {n : ℕ}

private theorem exists_positiveTime_test {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : 𝓓((⊤ : Opens ℝ), ℝ),
      (∀ t, 0 ≤ ψ t) ∧ (∫ t, ψ t = 1) ∧ tsupport ψ ⊆ Ioo 0 ε := by
  let φ : ContDiffBump (ε / 2) :=
    { rIn := ε / 8
      rOut := ε / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let ψ : 𝓓((⊤ : Opens ℝ), ℝ) :=
    .mk (φ.normed volume) φ.contDiff_normed φ.hasCompactSupport_normed (subset_univ _)
  refine ⟨ψ, φ.nonneg_normed, φ.integral_normed, ?_⟩
  intro t ht
  change t ∈ tsupport (φ.normed volume) at ht
  rw [φ.tsupport_normed_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
  dsimp only [φ] at ht
  constructor <;> linarith [ht.1, ht.2]

/-- A continuous initial function inherits the sum of the positive-time weak
spatial derivative bounds whenever the spacetime field approaches it uniformly
at a linear rate. The statement includes spatial dimension zero. -/
theorem lipschitzWith_initial_of_positiveTime_weak_derivative_bound
    {f : ℝ^(n + 1) → ℝ} (hf : LocallyIntegrable f volume)
    {v : ℝ^n → ℝ} (hv : Continuous v)
    (g : Fin n → ℝ^(n + 1) → ℝ)
    (hg : ∀ j, HasWeakDerivativeOn univ [j.succ] f (g j))
    (C : Fin n → ℝ≥0)
    (hC : ∀ j, ∀ᵐ p ∂volume, 0 < p 0 → ‖g j p‖ ≤ C j)
    (B : ℝ≥0)
    (hinitial : ∀ p, ‖f p - v (spatialPart p)‖ ≤ B * max (p 0) 0) :
    LipschitzWith (∑ j, C j) v := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      ∃ w : ℝ^n → ℝ, LipschitzWith (∑ j, C j) w ∧
        ∀ x, ‖w x - v x‖ ≤ B * ε := by
    obtain ⟨ψ, hψ, hmass, hsupp⟩ := exists_positiveTime_test hε
    have havg : LocallyIntegrable (fun x ↦ ∫ t, ψ t * f (timeSpaceCons t x)) volume :=
      Slices.locallyIntegrable_timeAverage hf ψ
    have hgrad (j : Fin n) :
        ∀ᵐ x ∂volume, ‖∫ t, ψ t * g j (timeSpaceCons t x)‖ ≤ C j := by
      apply Slices.ae_norm_timeAverage_le ψ hψ hmass
      filter_upwards [hC j] with p hp hne
      exact hp (hsupp (subset_closure hne)).1
    obtain ⟨w, hw, heq⟩ := exists_lipschitzWith_ae_eq_of_weak_derivative_bound havg
      (fun j x ↦ ∫ t, ψ t * g j (timeSpaceCons t x))
      (fun j ↦ (hg j).timeAverage j ψ) C hgrad
    have herr : ∀ᵐ x ∂volume,
        ‖(∫ t, ψ t * f (timeSpaceCons t x)) - v x‖ ≤ B * ε := by
      apply Slices.ae_norm_timeAverage_sub_le hf ψ hψ hmass
      apply Eventually.of_forall
      intro p hne
      have ht := hsupp (subset_closure hne)
      exact (hinitial p).trans (mul_le_mul_of_nonneg_left
        (max_le ht.2.le hε.le) B.coe_nonneg)
    have haew : ∀ᵐ x ∂volume, ‖w x - v x‖ ≤ B * ε := by
      filter_upwards [heq, herr] with x hx hbound
      simpa only [hx] using hbound
    refine ⟨w, hw, fun x ↦ ?_⟩
    exact (isClosed_le (hw.continuous.sub hv).norm continuous_const).closure_subset
      ((volume : Measure (ℝ^n)).dense_of_ae haew x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdist (ε : ℝ) (hε : 0 < ε) :
      dist (v x) (v y) ≤ B * ε + (∑ j, C j : ℝ≥0) * dist x y + B * ε := by
    obtain ⟨w, hw, he⟩ := happrox ε hε
    have hx : dist (v x) (w x) ≤ B * ε := by
      simpa only [dist_comm (v x), dist_eq_norm] using he x
    have hy : dist (w y) (v y) ≤ B * ε := by
      simpa only [dist_eq_norm] using he y
    exact (dist_triangle4 (v x) (w x) (w y) (v y)).trans
      (add_le_add (add_le_add hx (hw.dist_le_mul x y)) hy)
  have hr : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim :
      Tendsto (fun k : ℕ ↦ B * (1 / ((k : ℝ) + 1)) +
        (∑ j, C j : ℝ≥0) * dist x y + B * (1 / ((k : ℝ) + 1)))
        atTop (𝓝 ((∑ j, C j : ℝ≥0) * dist x y)) := by
    simpa only [mul_zero, zero_add, add_zero] using
      ((tendsto_const_nhds.mul hr).add tendsto_const_nhds).add
        (tendsto_const_nhds.mul hr)
  exact ge_of_tendsto hlim
    (Eventually.of_forall fun k : ℕ ↦ hdist (1 / ((k : ℝ) + 1))
      (div_pos zero_lt_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one)))

end SobolevSpace
