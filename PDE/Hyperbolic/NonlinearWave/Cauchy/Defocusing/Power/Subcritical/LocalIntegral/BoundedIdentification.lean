/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespan

/-!
# Bounded identification of quadratic integral waves

A free-wave barrier bounds a local integral field. Bounded integral uniqueness identifies it
with the global trajectory having the same Cauchy data.
-/

@[expose] public noncomputable section

section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower
open scoped unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A strict scalar barrier bounds the complete physical cone of a continuous
integral wave with bounded free input, without a prior bound on that wave. -/
theorem norm_physicalCone_lt_of_bounded_free_barrier {T B A M : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {q | |q.1| < T}) (H : C(ℝ × ℝ^3, ℝ)) (f : C(ℝ, ℝ))
    (hH : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → |H q| ≤ B) (hf : ∀ z : ℝ, ‖z‖ ≤ M → ‖f z‖ ≤ A)
    (heq : ∀ q : {q : ℝ × ℝ^3 | |q.1| < T}, 0 ≤ q.1.1 → physicalCone hu q =
      coneField H q.1 + q.1.1 ^ 2 • duhamelOperator (composeCompact f (physicalCone hu q)))
    (q : {q : ℝ × ℝ^3 | |q.1| < T}) (hq : 0 ≤ q.1.1)
    (hsmall : B + q.1.1 ^ 2 * ‖duhamelOperator‖ * A < M) :
    ‖physicalCone hu q‖ < M := by
  have ht (s : I) : |(s : ℝ) * q.1.1| ≤ |q.1.1| := by
    rw [abs_mul, abs_of_nonneg s.2.1]
    exact (mul_le_mul_of_nonneg_right s.2.2 (abs_nonneg _)).trans_eq (one_mul _)
  let path : I → {q : ℝ × ℝ^3 | |q.1| < T} := fun s ↦
    ⟨((s : ℝ) * q.1.1, q.1.2), (ht s).trans_lt q.2⟩
  have hp (s : I) : 0 ≤ (path s).1.1 := mul_nonneg s.2.1 hq
  have hfree (s : I) : ‖coneField H (path s).1‖ ≤ B := by
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro r
    rw [coneField_apply]
    apply hH
    exact ⟨mul_nonneg (hp s) (coneTime_mem r).1, (le_abs_self _).trans_lt
        ((abs_physicalPoint_time_le (path s).1 r).trans_lt (path s).2)⟩
  have hc : Continuous (fun s : I ↦ ‖physicalCone hu (path s)‖) :=
    ((continuous_physicalCone hu).comp
      (((continuous_subtype_val.mul continuous_const).prodMk continuous_const).subtype_mk
        (fun s ↦ (ht s).trans_lt q.2))).norm
  have hz : ‖physicalCone hu (path 0)‖ ≤ B := by
    rw [heq (path 0) (hp 0)]
    have htime : (path 0).1.1 = 0 := by simp [path]
    rw [htime, zero_pow (by decide : 2 ≠ 0), zero_smul, add_zero]
    exact hfree 0
  have ho : path 1 = q := by
    apply Subtype.ext
    simp [path]
  have hBM : B < M := lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg
      (mul_nonneg (sq_nonneg q.1.1) (norm_nonneg duhamelOperator)) hA)) hsmall
  by_contra! hbad
  obtain ⟨s, hs⟩ := intermediate_value_univ (0 : I) (1 : I) hc
    (show M ∈ Icc ‖physicalCone hu (path 0)‖ ‖physicalCone hu (path 1)‖ by
      rw [ho]
      exact ⟨hz.trans hBM.le, hbad⟩)
  have hN : ‖composeCompact f (physicalCone hu (path s))‖ ≤ A := by
    apply (BoundedContinuousFunction.norm_le hA).mpr
    intro r
    exact hf _ (((physicalCone hu (path s)).norm_coe_le_norm r).trans hs.le)
  have hsq : (path s).1.1 ^ 2 ≤ q.1.1 ^ 2 := by
    have hle : (path s).1.1 ≤ q.1.1 := by
      change (s : ℝ) * q.1.1 ≤ q.1.1
      simpa only [one_mul] using mul_le_mul_of_nonneg_right s.2.2 hq
    exact sq_le_sq₀ (hp s) hq |>.mpr hle
  have hb : ‖physicalCone hu (path s)‖ < M := by
    calc
      ‖physicalCone hu (path s)‖ = ‖coneField H (path s).1 + (path s).1.1 ^ 2 • duhamelOperator
            (composeCompact f (physicalCone hu (path s)))‖ := congrArg norm (heq _ (hp s))
      _ ≤ ‖coneField H (path s).1‖ + ‖(path s).1.1 ^ 2 • duhamelOperator
            (composeCompact f (physicalCone hu (path s)))‖ := norm_add_le _ _
      _ = ‖coneField H (path s).1‖ + (path s).1.1 ^ 2 *
          ‖duhamelOperator (composeCompact f (physicalCone hu (path s)))‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
      _ ≤ B + (path s).1.1 ^ 2 * (‖duhamelOperator‖ * A) := by
        apply add_le_add (hfree s)
        exact mul_le_mul_of_nonneg_left ((duhamelOperator.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hN (norm_nonneg _))) (sq_nonneg _)
      _ ≤ B + q.1.1 ^ 2 * (‖duhamelOperator‖ * A) :=
        add_le_add_right (mul_le_mul_of_nonneg_right hsq
          (mul_nonneg (norm_nonneg duhamelOperator) hA)) B
      _ = B + q.1.1 ^ 2 * ‖duhamelOperator‖ * A := by rw [mul_assoc]
      _ < M := hsmall
  exact (hs ▸ hb).false

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A quadratic integral wave inherits a uniform bound from a strict free-wave
barrier on the full two-unit interval. Spatial boundedness of the wave is a conclusion. -/
theorem abs_lt_of_quadratic_integral_free_barrier {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    {u H : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {p | |p.1| < 3}) (hH : Continuous H)
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → |H p| ≤ B)
    (heq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower 2 (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2))
    (hsmall : B + 4 * ‖duhamelOperator‖ * M ^ 2 < M) :
    ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → |u p| < M := by
  have hu₂ : ContinuousOn u {p | |p.1| < 2} :=
    hu.mono (fun p hp ↦ lt_trans (show |p.1| < 2 from hp) (by norm_num))
  let f : C(ℝ, ℝ) := ⟨fun z ↦ -Real.signedPower 2 z,
    (Real.continuous_signedPower (by norm_num : (0 : ℝ) < 2)).neg⟩
  have hf (z : ℝ) (hz : ‖z‖ ≤ M) : ‖f z‖ ≤ M ^ 2 := by
    change ‖-Real.signedPower 2 z‖ ≤ M ^ 2
    rw [norm_neg, Real.norm_signedPower (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    exact (sq_le_sq₀ (norm_nonneg z) hM).mpr hz
  have he (q : ℝ × ℝ^3) (hq : q.1 ∈ Ico 0 2) : u q = H q + q.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
        ((∫ θ : Direction, f (u (q.1 * (s : ℝ), q.2 + q.1 • ((1 - (s : ℝ)) • (θ : ℝ^3))))
            ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
    rw [heq q hq, oddDuhamelSolution_zero_eq_normalized _ _ hq.1]
    rfl
  intro p hp
  let q : {q : ℝ × ℝ^3 | |q.1| < 2} :=
    ⟨p, by
      change |p.1| < 2
      simpa only [abs_of_nonneg hp.1] using hp.2⟩
  have hsq : p.1 ^ 2 ≤ 4 := by nlinarith [hp.1, hp.2]
  have hn := norm_physicalCone_lt_of_bounded_free_barrier hB (sq_nonneg M) hu₂ ⟨H, hH⟩ f hHB hf
    (fun q hq ↦ physicalCone_eq_of_free_integral_eq hu₂ ⟨H, hH⟩ f he q hq) q hp.1
    (lt_of_le_of_lt (add_le_add_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq (norm_nonneg duhamelOperator)) (sq_nonneg M)) B) hsmall)
  have hv := (physicalCone hu₂ q).norm_coe_le_norm vertex |>.trans_lt hn
  simpa only [physicalCone_apply, physicalPoint, vertex, coneTime, coneSpace,
    mul_one, smul_zero, add_zero, Real.norm_eq_abs] using hv

/-- Integral uniqueness identifies a bounded local quadratic wave
with any same-free-field global trajectory on its full local forward interval. -/
theorem eq_global_of_bounded_local_quadratic_integral {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    {u U H : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {p | |p.1| < 3}) (hH : ContDiff ℝ 1 H)
    (hU : IsGlobalIntegralTrajectory 2 b H U) (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → |u p| ≤ M)
    (heq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower 2 (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2)) :
    ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → u p = U p := by
  obtain ⟨A, hA, hUA⟩ := hU.bounded_before 2
  have hband : ContDiffOn ℝ 1 u {p | -(min b 3) < p.1 ∧ p.1 < 2} := by
    apply hu.mono
    intro p hp
    change |p.1| < 3
    rw [abs_lt]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right b 3)) hp.1,
      hp.2.trans (by norm_num)⟩
  have hUband : ContDiffOn ℝ 1 U {p | -(min b 3) < p.1 ∧ p.1 < 2} :=
    hU.regular.mono (fun p hp ↦ lt_of_le_of_lt (neg_le_neg (min_le_left b 3)) hp.1)
  exact eq_on_forward_interval_of_bounded_signedPower_integral_eq
    (by norm_num : (1 : ℝ) ≤ 2) (lt_min hb (by norm_num))
    (hM.trans (le_max_left M A)) hband hUband hH (fun p hp ↦ (huB p hp).trans (le_max_left M A))
    (fun p hp ↦ (hUA p hp).trans (le_max_right M A)) heq (fun p hp ↦ hU.equation p hp.1)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end
