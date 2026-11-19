/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.PhysicalCone
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.PowerIncrement

/-!
# A uniform amplitude barrier for the integral solution

The norm of a physical cone field varies continuously from zero as its
time scale increases. The integral equation prevents this norm from
reaching a fixed barrier while the free field and nonlinear term are
strictly below the barrier. The resulting bound uses the velocity norm
and the length of the time interval, without assuming a bound on the
unknown solution.
-/

@[expose] public noncomputable section

open Set Filter BoundedContinuousFunction
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- Continuation from the zero initial displacement proves a uniform cone
bound whenever the scalar norm barrier is strict. -/
theorem norm_physicalCone_lt_of_barrier {p T M : ℝ}
    (hp : 1 < p) (hM : 0 < M) {v : ℝ × ℝ^3 → ℝ}
    (hv : ContinuousOn v {q | |q.1| < T}) (hzero : ∀ x, v (0, x) = 0)
    (g : ℝ^3 →ᵇ ℝ) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    (∀ q : {q : ℝ × ℝ^3 | |q.1| < T},
      physicalCone hv q = freeField g.toContinuousMap q.1 +
        q.1.1 ^ 2 • duhamelOperator (composeCompact f (physicalCone hv q))) →
    ∀ q : {q : ℝ × ℝ^3 | |q.1| < T},
      |q.1.1| * ‖g‖ + q.1.1 ^ 2 * ‖duhamelOperator‖ * M ^ p < M →
      ‖physicalCone hv q‖ < M := by
  intro f heq q hsmall
  have ht (s : I) : |(s : ℝ) * q.1.1| ≤ |q.1.1| := by
    rw [abs_mul, abs_of_nonneg s.2.1]
    exact (mul_le_mul_of_nonneg_right s.2.2 (abs_nonneg _)).trans_eq (one_mul _)
  let path : I → {q : ℝ × ℝ^3 | |q.1| < T} := fun s ↦
    ⟨((s : ℝ) * q.1.1, q.1.2), (ht s).trans_lt q.2⟩
  have hc : Continuous (fun s : I ↦ ‖physicalCone hv (path s)‖) :=
    ((continuous_physicalCone hv).comp
      (((continuous_subtype_val.mul continuous_const).prodMk continuous_const).subtype_mk
        (fun s ↦ (ht s).trans_lt q.2))).norm
  have hz : physicalCone hv (path 0) = 0 := by
    ext r
    simpa [physicalCone_apply, path, physicalPoint] using hzero q.1.2
  have ho : path 1 = q := by
    apply Subtype.ext
    simp [path]
  by_contra! hbad
  obtain ⟨s, hs⟩ := intermediate_value_univ (0 : I) (1 : I) hc
    (show M ∈ Icc ‖physicalCone hv (path 0)‖ ‖physicalCone hv (path 1)‖ by
      rw [hz, norm_zero, ho]
      exact ⟨hM.le, hbad⟩)
  have hN := norm_composeCompact_abs_rpow_le hp (physicalCone hv (path s)) hs.le
  have hsq : ((s : ℝ) * q.1.1) ^ 2 ≤ q.1.1 ^ 2 := by
    nlinarith [sq_abs ((s : ℝ) * q.1.1), sq_abs q.1.1, ht s,
      abs_nonneg ((s : ℝ) * q.1.1), abs_nonneg q.1.1]
  have hb : ‖physicalCone hv (path s)‖ < M := by
    calc
      ‖physicalCone hv (path s)‖ = ‖freeField g.toContinuousMap (path s).1 +
          (path s).1.1 ^ 2 • duhamelOperator
            (composeCompact f (physicalCone hv (path s)))‖ := congrArg norm (heq _)
      _ ≤ ‖freeField g.toContinuousMap (path s).1‖ + ‖(path s).1.1 ^ 2 • duhamelOperator
            (composeCompact f (physicalCone hv (path s)))‖ := norm_add_le _ _
      _ = ‖freeField g.toContinuousMap (path s).1‖ + (path s).1.1 ^ 2 * ‖duhamelOperator
            (composeCompact f (physicalCone hv (path s)))‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg (path s).1.1)]
      _ ≤ |(path s).1.1| * ‖g‖ + (path s).1.1 ^ 2 *
          (‖duhamelOperator‖ * M ^ p) := by
        apply add_le_add (norm_freeField_le g _)
        exact mul_le_mul_of_nonneg_left ((duhamelOperator.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hN (norm_nonneg duhamelOperator))) (sq_nonneg _)
      _ ≤ |q.1.1| * ‖g‖ + q.1.1 ^ 2 * (‖duhamelOperator‖ * M ^ p) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (ht s) (norm_nonneg g)
        · exact mul_le_mul_of_nonneg_right hsq
            (mul_nonneg (norm_nonneg duhamelOperator) (Real.rpow_nonneg hM.le _))
      _ = |q.1.1| * ‖g‖ + q.1.1 ^ 2 * ‖duhamelOperator‖ * M ^ p := by rw [mul_assoc]
      _ < M := hsmall
  exact (hs ▸ hb).false

/-- Every continuous power integral solution with zero displacement has a
uniform short time interval where its cone norm is less than one and the
linearized coefficient can be absorbed. -/
theorem exists_time_uniform_cone_control {p T : ℝ} (hp : 1 < p) (hT : 0 < T)
    {v : ℝ × ℝ^3 → ℝ} (hv : ContinuousOn v {q | |q.1| < T})
    (hzero : ∀ x, v (0, x) = 0) (g : ℝ^3 →ᵇ ℝ) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    (∀ q : {q : ℝ × ℝ^3 | |q.1| < T},
      physicalCone hv q = freeField g.toContinuousMap q.1 +
        q.1.1 ^ 2 • duhamelOperator (composeCompact f (physicalCone hv q))) →
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧
      ∀ q : {q : ℝ × ℝ^3 | |q.1| < T}, |q.1.1| < τ →
        ‖physicalCone hv q‖ < 1 ∧ q.1.1 ^ 2 * ‖duhamelOperator‖ * p ≤ 1 / 2 := by
  intro f heq
  have hb : ContinuousAt (fun t : ℝ ↦ |t| * ‖g‖ + t ^ 2 * ‖duhamelOperator‖) 0 := by
    fun_prop
  have hd : ContinuousAt (fun t : ℝ ↦ t ^ 2 * ‖duhamelOperator‖ * p) 0 := by fun_prop
  have hsmall : ∀ᶠ t : ℝ in nhds 0,
      |t| * ‖g‖ + t ^ 2 * ‖duhamelOperator‖ < 1 ∧ t ^ 2 * ‖duhamelOperator‖ * p < 1 / 2 :=
    (hb.eventually_lt_const (by simp)).and (hd.eventually_lt_const (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨min T δ, lt_min hT hδ, min_le_left _ _, fun q hq ↦ ?_⟩
  have hmem : q.1.1 ∈ Metric.ball 0 δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hq.trans_le (min_le_right T δ)
  have hs := hball hmem
  refine ⟨norm_physicalCone_lt_of_barrier hp zero_lt_one hv hzero g heq q ?_, hs.2.le⟩
  simpa only [Real.one_rpow, mul_one] using hs.1

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
