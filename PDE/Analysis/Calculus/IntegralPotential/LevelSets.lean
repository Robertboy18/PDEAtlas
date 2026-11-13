/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegralPotential.QuadraticGrowth

/-!
# Nonempty integral level sets from quadratic lower bounds

A potential with negative integral at zero and a positive quadratic lower
bound crosses the zero level along every nonzero `L²` direction. Linear growth
of its actual derivative supplies continuity of the integral; the intermediate
value theorem then constructs a feasible amplitude.
-/

@[expose] public section

noncomputable section

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- A potential's positive quadratic lower bound passes to its actual `L²`
integral, with the constant integrated against the full finite measure. -/
theorem quadratic_lower_bound_integral_L2
    {G g : ℝ → ℝ} {C k b : ℝ} (hC : 0 ≤ C)
    (hd : ∀ s, HasDerivAt G (g s) s) (hg : ∀ s, |g s| ≤ C * (1 + |s|))
    (hlower : ∀ s, k * s ^ 2 - b ≤ G s) (u : Lp ℝ 2 μ) :
    k * ‖u‖ ^ 2 - b * μ.real univ ≤ ∫ x, G (u x) ∂μ := by
  have hsq : (∫ x, (u x) ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    simp [pow_two]
  calc
    _ = ∫ x, k * (u x) ^ 2 - b ∂μ := by
      rw [integral_sub ((Lp.memLp u).integrable_sq.const_mul k) (integrable_const b),
        integral_const_mul, hsq, integral_const]
      simp [smul_eq_mul, mul_comm]
    _ ≤ _ := integral_mono
      (((Lp.memLp u).integrable_sq.const_mul k).sub (integrable_const b))
      (integrable_potential_L2_of_deriv_growth hC hd hg u) (fun x ↦ hlower (u x))

/-- Scaling any nonzero `L²` function reaches the zero integral level. Both
the continuity of the integral and its large-amplitude lower bound are proved
from the scalar potential's derivative growth and quadratic lower bound. -/
theorem exists_smul_integral_eq_zero_of_quadratic_lower
    {G g : ℝ → ℝ} {C k b : ℝ} (hC : 0 ≤ C)
    (hd : ∀ s, HasDerivAt G (g s) s) (hg : ∀ s, |g s| ≤ C * (1 + |s|))
    (hzero : μ.real univ * G 0 < 0) (hk : 0 < k)
    (hlower : ∀ s, k * s ^ 2 - b ≤ G s)
    (u : Lp ℝ 2 μ) (hu : u ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∫ x, G ((t • u : Lp ℝ 2 μ) x) ∂μ) = 0 := by
  let J : ℝ → ℝ := fun t ↦ ∫ x, G ((t • u : Lp ℝ 2 μ) x) ∂μ
  have hJ : Continuous J :=
    (continuous_integral_L2_of_deriv_growth hC hd hg).comp (continuous_id.smul continuous_const)
  have hJzero : J 0 < 0 := by
    have heq : J 0 = μ.real univ * G 0 := by
      change (∫ x, G ((0 • u : Lp ℝ 2 μ) x) ∂μ) = _
      rw [zero_smul]
      calc
        _ = ∫ _ : α, G 0 ∂μ :=
          integral_congr_ae ((Lp.coeFn_zero ℝ 2 μ).mono fun x hx ↦ congrArg G hx)
        _ = _ := by simp
    rwa [heq]
  let A := k * ‖u‖ ^ 2
  let B := b * μ.real univ
  have hA : 0 < A := mul_pos hk (sq_pos_of_pos (norm_pos_iff.mpr hu))
  let t := max 1 ((B + 1) / A)
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hAt : B + 1 ≤ A * t := by
    have h := (div_le_iff₀ hA).mp (le_max_right 1 ((B + 1) / A))
    simpa only [mul_comm] using h
  have hAt2 : A * t ≤ A * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hA.le ht0)
    nlinarith
  have hJt : 0 < J t := by
    have hl := quadratic_lower_bound_integral_L2 hC hd hg hlower (t • u)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hl
    change k * (t * ‖u‖) ^ 2 - B ≤ J t at hl
    dsimp [A] at hAt hAt2
    nlinarith
  obtain ⟨s, hs, hJs⟩ := intermediate_value_Icc ht0 hJ.continuousOn
    (show (0 : ℝ) ∈ Icc (J 0) (J t) from ⟨hJzero.le, hJt.le⟩)
  exact ⟨s, hs.1, hJs⟩

end MeasureTheory
