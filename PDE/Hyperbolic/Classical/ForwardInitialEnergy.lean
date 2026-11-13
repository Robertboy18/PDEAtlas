/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.Analysis.Calculus.SpaceTime.ForwardDerivative

/-!
# The initial energy of a forward classical wave

Continuity of the first derivative on the closed forward half-space controls the
shrinking-ball energy as time tends to zero. The initial velocity is the
right derivative of the time trace. Initial data are imposed only on the open base ball.
-/

@[expose] public section

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis PDE.Common Set
open scoped Topology

variable {n : ℕ}

private noncomputable def differentialEnergy (D : ℝ^(n + 1) →L[ℝ] ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((D (EuclideanSpace.single 0 1)) ^ 2 +
    ‖(WithLp.toLp 2 fun i : Fin n ↦ D (EuclideanSpace.single i.succ 1) : ℝ^n)‖ ^ 2)

private theorem continuous_differentialEnergy :
    Continuous (differentialEnergy (n := n)) := by
  apply continuous_const.mul
  apply Continuous.add
  · exact (continuous_id.clm_apply continuous_const).pow 2
  · apply Continuous.pow
    apply Continuous.norm
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun i ↦ continuous_id.clm_apply continuous_const

private theorem differentialEnergy_nonneg (D : ℝ^(n + 1) →L[ℝ] ℝ) :
    0 ≤ differentialEnergy D :=
  mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))

private noncomputable def clippedEnergy (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) : ℝ :=
  differentialEnergy (forwardDifferential u t x)

private theorem continuous_clippedEnergy {u : ℝ^(n + 1) → ℝ} (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) :
    Continuous (Function.uncurry (clippedEnergy u)) :=
  continuous_differentialEnergy.comp (continuous_forwardDifferential hu)

private theorem clippedEnergy_eq {u : ℝ^(n + 1) → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    clippedEnergy u t x = classicalWaveEnergyDensity u (timeSpaceCons t x) := by
  rw [clippedEnergy, forwardDifferential_eq_fderiv u ht x]
  rfl

private theorem clippedEnergy_initial_eq_zero {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ}
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0)
    {x : ℝ^n} (hx : x ∈ Metric.ball c T) :
    clippedEnergy u 0 x = 0 := by
  rw [clippedEnergy, forwardDifferential_initial_eq_zero hu Metric.isOpen_ball hpos hvel hx]
  simp only [differentialEnergy, one_div, zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff, norm_eq_zero,
    WithLp.toLp_eq_zero, false_or]
  rfl

/-- Zero initial displacement and right velocity imply that the shrinking-ball
energy tends to zero from positive times. Only forward `C¹` regularity is required here. -/
theorem tendsto_backwardConeEnergy_zero_forward {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ} (hT : 0 < T)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    Tendsto (backwardConeEnergy u c T) (𝓝[>] 0) (𝓝 0) := by
  let F : ℝ → ℝ := fun t ↦ ∫ x in Metric.closedBall c T, clippedEnergy u t x
  have hF : Continuous F :=
    continuous_parametric_integral_of_continuous (continuous_clippedEnergy hu)
      (isCompact_closedBall c T)
  have hzero : F 0 = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    have hbase : EqOn (clippedEnergy u 0) 0 (Metric.ball c T) :=
      fun x hx ↦ clippedEnergy_initial_eq_zero hu c hpos hvel hx
    have hclosed := hbase.closure
      ((continuous_clippedEnergy hu).comp (continuous_const.prodMk continuous_id)) continuous_const
    exact fun x hx ↦ hclosed (by rwa [closure_ball _ hT.ne'])
  apply squeeze_zero' (Filter.Eventually.of_forall (backwardConeEnergy_nonneg u c T))
    ?_ (hzero ▸ hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hcont : Continuous (clippedEnergy u t) :=
    (continuous_clippedEnergy hu).comp (continuous_const.prodMk continuous_id)
  have heq : backwardConeEnergy u c T t =
      ∫ x in Metric.ball c (T - t), clippedEnergy u t x := by
    unfold backwardConeEnergy ballIntegral
    exact setIntegral_congr_fun measurableSet_ball fun x _ ↦ (clippedEnergy_eq ht x).symm
  rw [heq]
  apply setIntegral_mono_set (hcont.continuousOn.integrableOn_compact (isCompact_closedBall c T))
    (Filter.Eventually.of_forall fun x ↦ differentialEnergy_nonneg _)
  exact Filter.Eventually.of_forall fun x hx ↦ Metric.mem_closedBall.mpr
    ((Metric.mem_ball.mp hx).le.trans (sub_le_self T ht.le))

end WaveEquation
