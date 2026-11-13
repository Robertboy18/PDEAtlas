/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.NormBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Multiplication

/-!
# Local Lipschitz estimates for general smooth Sobolev composition

The fundamental theorem of calculus, the bounded Sobolev product, and the
uniform norm bound for the centered scalar derivative give a Lipschitz
constant on each norm ball. Integration is performed on continuous bounded
representatives; weak compactness recovers the Sobolev norm estimate.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped BoundedContinuousFunction Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- General smooth scalar composition fixing zero is Lipschitz on every
Sobolev norm ball above the classical embedding threshold. -/
theorem exists_lipschitzOn_higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {R : ℝ} :
    ∃ K, LipschitzOnWith K (higherComposition hk hf hf0) (Metric.closedBall 0 R) := by
  let : NormedAddCommGroup W^{k,2}(ℝ^n) := inferInstance
  let : NormedSpace ℝ W^{k,2}(ℝ^n) := inferInstance
  let A := classicalRepresentativeCLM hk
  let P := higherProductCLM hk
  let r : ℝ → ℝ := fun s ↦ deriv f s - deriv f 0
  have hr : ContDiff ℝ (⊤ : ℕ∞) r := (contDiff_infty_iff_deriv.mp hf).2.sub contDiff_const
  have hr0 : r 0 = 0 := sub_self _
  obtain ⟨C, hC, hbound⟩ := exists_norm_higherComposition_bound (R := R) hk hr hr0
  let M := ‖deriv f 0‖ + ‖P‖ * C
  have hM : 0 ≤ M := add_nonneg (norm_nonneg _) (mul_nonneg P.opNorm_nonneg hC)
  refine ⟨⟨M, hM⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  let w := u - v
  let U : ℝ → W^{k,2}(ℝ^n) := fun t ↦ v + t • w
  let W : ℝ → W^{k,2}(ℝ^n) := fun t ↦ deriv f 0 • w + P (higherComposition hk hr hr0 (U t)) w
  let z : ℝ → (ℝ^n →ᵇ ℝ) := fun t ↦ A (W t)
  have hU : Continuous U := continuous_const.add (continuous_id.smul continuous_const)
  have hzexpr : z = fun t ↦ deriv f 0 • A w +
      A (higherComposition hk hr hr0 (U t)) * A w := by
    ext t x
    simp only [z, W, A, P, map_add, map_smul, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.mul_apply,
      classicalRepresentative_higherProductCLM]
  have hz : Continuous z := by
    rw [hzexpr]
    exact continuous_const.add
      (((locallyLipschitz_observed_composition hk hr hr0).continuous.comp hU).mul continuous_const)
  have hW (t : ℝ) (ht : t ∈ Icc 0 1) : ‖W t‖ ≤ M * ‖w‖ := by
    have he : U t = (1 - t) • v + t • u := by
      simp only [U, w, sub_smul, one_smul, smul_sub]
      abel
    have hUt' : ‖U t‖ ≤ R := by
      simpa only [he, Metric.mem_closedBall, dist_zero_right] using
        (convex_closedBall (0 : W^{k,2}(ℝ^n)) R) hv hu (sub_nonneg.mpr ht.2) ht.1 (by ring)
    calc
      ‖W t‖ ≤ ‖deriv f 0 • w‖ + ‖P (higherComposition hk hr hr0 (U t)) w‖ := norm_add_le _ _
      _ ≤ ‖deriv f 0‖ * ‖w‖ + ‖P‖ * C * ‖w‖ := by
        rw [norm_smul]
        apply add_le_add_right
        exact (P.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hbound _ hUt') P.opNorm_nonneg) (norm_nonneg _))
      _ = M * ‖w‖ := by dsimp [M]; ring
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hzi : IntervalIntegrable z volume 0 1 := hz.intervalIntegrable 0 1
  have hzm : Integrable z μ := hzi.1
  have hball : ∀ᵐ t ∂μ, ∃ e : W^{k,2}(ℝ^n), ‖e‖ ≤ M * ‖w‖ ∧ A e = z t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨W t, hW t ⟨ht.1.le, ht.2⟩, rfl⟩
  obtain ⟨e, he, hAe⟩ := exists_lift_integral_observation A hzm hball
  have hAe' : A e = ∫ t in (0 : ℝ)..1, z t := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), μ] using hAe
  have hzpoint (t : ℝ) (x : ℝ^n) :
      z t x = deriv f (A v x + t * A w x) * A w x := by
    simp only [z, W, A, P, map_add, map_smul, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul,
      classicalRepresentative_higherProductCLM, classicalRepresentative_higherComposition, U, r]
    ring
  have heq : e = higherComposition hk hf hf0 u - higherComposition hk hf hf0 v := by
    apply classicalRepresentativeCLM_injective hk
    ext x
    have hscalar : (∫ t in (0 : ℝ)..1, deriv f (A v x + t * A w x) * A w x) =
          f (A u x) - f (A v x) := by
      have hd (t : ℝ) : HasDerivAt (fun s ↦ f (A v x + s * A w x))
          (deriv f (A v x + t * A w x) * A w x) t := by
        simpa only [Function.comp_def, one_mul] using
          (hf.differentiable (by simp) _).hasDerivAt.comp t
            (((hasDerivAt_id' t).mul_const (A w x)).const_add (A v x))
      have hcd := hf.continuous_deriv (by simp)
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      have hend : A v x + A w x = A u x := by simp [w, map_sub]
      simpa only [one_mul, zero_mul, add_zero, hend] using hi
    change A e x = _
    rw [hAe']
    have hi := (BoundedContinuousFunction.evalCLM ℝ x).intervalIntegral_comp_comm hzi
    change (∫ t in (0 : ℝ)..1, z t x) = (∫ t in (0 : ℝ)..1, z t) x at hi
    rw [← hi]
    simp only [hzpoint, hscalar, map_sub, BoundedContinuousFunction.sub_apply,
      classicalRepresentative_higherComposition, A]
  rw [dist_eq_norm, dist_eq_norm, ← heq]
  exact he

/-- Smooth reactions fixing zero define locally Lipschitz maps on the constructed whole-space
Sobolev class. -/
theorem locallyLipschitz_higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    LocallyLipschitz (higherComposition hk hf hf0) := by
  intro u
  obtain ⟨K, hK⟩ := exists_lipschitzOn_higherComposition (R := ‖u‖ + 1) hk hf hf0
  refine ⟨K, Metric.closedBall 0 (‖u‖ + 1), ?_, hK⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy
