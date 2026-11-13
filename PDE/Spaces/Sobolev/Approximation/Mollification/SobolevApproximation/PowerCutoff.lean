/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoff

/-!
# Powers of smooth cutoffs

Differentiating a sufficiently high power of a smooth function retains a prescribed
power of that function. Applied to the radial cutoff before dilation, this controls
its derivatives by the remaining cutoff and the correct inverse power of the radius.
The retained factor permits absorption in a compact energy test, while radial symmetry
preserves the parity of the tested field.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv iteratedPartialDeriv_comp_const_smul)

open Filter Metric Set Function
open scoped Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- A word of coordinate derivatives removes at most its length from the power
of a smooth function; the remaining factor is smooth even where the function vanishes. -/
theorem exists_iteratedPartialDeriv_pow_factor {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin n)) (m : ℕ) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      iteratedPartialDeriv α (fun x ↦ f x ^ (m + α.length)) =
        fun x ↦ f x ^ m * g x := by
  induction α generalizing m with
  | nil =>
    exact ⟨fun _ ↦ 1, contDiff_const, by simp [iteratedPartialDeriv]⟩
  | cons i α ih =>
    obtain ⟨g, hg, hfactor⟩ := ih (m + 1)
    refine ⟨fun x ↦ (m + 1 : ℝ) * (∂[i] f) x * g x +
      f x * (∂[i] g) x, ?_, ?_⟩
    · exact ((contDiff_const.mul (PDE.contDiff_top_partialDeriv hf)).mul hg).add
        (hf.mul (PDE.contDiff_top_partialDeriv hg))
    · funext x
      have horder : m + (i :: α).length = (m + 1) + α.length := by simp; omega
      simp only [horder, iteratedPartialDeriv]
      rw [hfactor, PDE.partialDeriv_mul
        ((hf.pow (m + 1)).differentiable (by simp)).differentiableAt
        (hg.differentiable (by simp)).differentiableAt]
      have hpow :
          (∂[i] (fun y ↦ f y ^ (m + 1))) x =
            (m + 1 : ℝ) * f x ^ m * (∂[i] f) x := by
        simp only [partialDeriv, fderiv_fun_pow (m + 1)
          (hf.differentiable (by simp)).differentiableAt,
          Nat.add_sub_cancel, smul_apply, smul_eq_mul,
          nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [hpow, pow_succ]
      ring

/-- On a compactly supported nonnegative smooth function, the factor remaining
after differentiation of a power admits a uniform bound. -/
theorem exists_abs_iteratedPartialDeriv_pow_le {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) (α : List (Fin n)) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedPartialDeriv α (fun y ↦ f y ^ (m + α.length)) x| ≤ C * f x ^ m := by
  obtain ⟨g, hg, hfactor⟩ := exists_iteratedPartialDeriv_pow_factor hf α m
  obtain ⟨B, hB⟩ := hfc.bddAbove_image hg.continuous.abs.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x
  rw [congrFun hfactor x, abs_mul, abs_of_nonneg (pow_nonneg (hf0 x) m)]
  by_cases hx : x ∈ tsupport f
  · calc
      _ ≤ f x ^ m * max B 0 := mul_le_mul_of_nonneg_left
        ((hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)) (pow_nonneg (hf0 x) m)
      _ = _ := mul_comm _ _
  · simp [image_eq_zero_of_notMem_tsupport hx, zero_pow hm.ne']

/-- A positive-order derivative of any cutoff power vanishes on the inner ball. -/
theorem iteratedPartialDeriv_radialCutoff_pow_zero_inside
    (α : List (Fin n)) (hα : α ≠ []) (m : ℕ) {R : ℝ} (hR : 0 < R)
    {x : ℝ^n} (hx : ‖x‖ < R) :
    iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ m) x = 0 := by
  have heq : (fun y : ℝ^n ↦ radialCutoff R y ^ m) =ᶠ[𝓝 x] radialCutoff R := by
    have hxball : x ∈ ball (0 : ℝ^n) R := by simpa using hx
    filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
    rw [radialCutoff_eq_one hR (by simpa using ball_subset_closedBall hy), one_pow]
  exact (heq.iteratedPartialDeriv α).eq_of_nhds.trans
    (radialCutoff_derivative_zero_inside α hα hR hx)

/-- Positive cutoff powers and all their derivatives vanish outside the outer ball. -/
theorem iteratedPartialDeriv_radialCutoff_pow_zero_outside
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 < R)
    {x : ℝ^n} (hx : 2 * R < ‖x‖) :
    iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ m) x = 0 := by
  have heq : (fun y : ℝ^n ↦ radialCutoff R y ^ m) =ᶠ[𝓝 x] radialCutoff R := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    have hz : radialCutoff R y = 0 := by
      simpa only [iteratedPartialDeriv] using
        radialCutoff_derivative_zero_outside [] hR hy
    simp only [hz, zero_pow hm.ne']
  exact (heq.iteratedPartialDeriv α).eq_of_nhds.trans
    (radialCutoff_derivative_zero_outside α hR hx)

/-- A derivative of a powered radius-R cutoff retains the undifferentiated
power, with a constant independent of the positive radius and the evaluation point. -/
theorem exists_abs_iteratedPartialDeriv_radialCutoff_pow_le
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 0 < R) (x : ℝ^n),
      |iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ (m + α.length)) x| ≤
        C * R⁻¹ ^ α.length * radialCutoff R x ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_iteratedPartialDeriv_pow_le
    (radialCutoff_contDiff 1) (radialCutoff_hasCompactSupport zero_lt_one)
    (fun x : ℝ^n ↦ (radialCutoff_mem_Icc 1 x).1) α hm
  refine ⟨C, hC, ?_⟩
  intro R hR x
  have hscale (y : ℝ^n) : radialCutoff R y = radialCutoff 1 (R⁻¹ • y) := by
    simp [radialCutoff]
  simp_rw [hscale]
  rw [iteratedPartialDeriv_comp_const_smul α
    ((radialCutoff_contDiff 1).pow _), abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) _)]
  calc
    _ ≤ R⁻¹ ^ α.length * (C * radialCutoff 1 (R⁻¹ • x) ^ m) :=
      mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg (inv_nonneg.mpr hR.le) _)
    _ = _ := by ring

/-- Up to order m, derivatives of the power 2m retain at least the power m
of the cutoff. This is the factor required for a compact energy self-test. -/
theorem exists_abs_iteratedPartialDeriv_radialCutoff_two_mul_pow_le
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) (hα : α.length ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 0 < R) (x : ℝ^n),
      |iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ (2 * m)) x| ≤
        C * R⁻¹ ^ α.length * radialCutoff R x ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_iteratedPartialDeriv_radialCutoff_pow_le α
    (show 0 < 2 * m - α.length by omega)
  refine ⟨C, hC, ?_⟩
  intro R hR x
  have horder : 2 * m - α.length + α.length = 2 * m := by omega
  rw [horder] at hbound
  exact (hbound R hR x).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (radialCutoff_mem_Icc R x).1
      (radialCutoff_mem_Icc R x).2 (by omega))
    (mul_nonneg hC (pow_nonneg (inv_nonneg.mpr hR.le) _)))

/-- The radial power cancels the derivative scale while retaining the energy cutoff.
This bound is uniform in the radius, including where the cutoff vanishes. -/
theorem exists_radialCutoff_pow_derivative_scaled_bound
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) (hα : α.length ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 0 < R) (x : ℝ^n),
      (‖x‖ ^ 2) ^ α.length *
          (iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ (2 * m)) x) ^ 2 ≤
        C * radialCutoff R x ^ (2 * m) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_abs_iteratedPartialDeriv_radialCutoff_two_mul_pow_le α hm hα
  refine ⟨B ^ 2 * (4 : ℝ) ^ α.length, by positivity, ?_⟩
  intro R hR x
  by_cases hx : ‖x‖ ≤ 2 * R
  · have hi : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    have hd :
        (iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ (2 * m)) x) ^ 2 ≤
          B ^ 2 * (R⁻¹ ^ 2) ^ α.length * radialCutoff R x ^ (2 * m) := by
      have hs := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (mul_nonneg hB (pow_nonneg hi _))
          (pow_nonneg (radialCutoff_mem_Icc R x).1 _))).mpr (hbound R hR x)
      simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm α.length 2,
        Nat.mul_comm m 2] using hs
    have hs : ‖x‖ * R⁻¹ ≤ 2 := (mul_inv_le_iff₀ hR).mpr hx
    have hs0 : 0 ≤ ‖x‖ * R⁻¹ := mul_nonneg (norm_nonneg x) hi
    have hr : ‖x‖ ^ 2 * R⁻¹ ^ 2 ≤ 4 := by
      nlinarith [mul_self_le_mul_self hs0 hs]
    calc
      _ ≤ (‖x‖ ^ 2) ^ α.length *
          (B ^ 2 * (R⁻¹ ^ 2) ^ α.length * radialCutoff R x ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = B ^ 2 * (‖x‖ ^ 2 * R⁻¹ ^ 2) ^ α.length *
          radialCutoff R x ^ (2 * m) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hr α.length) (sq_nonneg B))
        (pow_nonneg (radialCutoff_mem_Icc R x).1 _)
  · rw [iteratedPartialDeriv_radialCutoff_pow_zero_outside α
      (by omega : 0 < 2 * m) hR (lt_of_not_ge hx)]
    simpa using mul_nonneg
      (show 0 ≤ B ^ 2 * (4 : ℝ) ^ α.length by positivity)
      (pow_nonneg (radialCutoff_mem_Icc R x).1 (2 * m))

/-- Young's inequality for the derivative of a powered cutoff.
The same constant works for every radius, absorption parameter, and pair of real values.
The first term has exactly the cutoff power appearing in the principal energy. -/
theorem exists_two_mul_abs_radialCutoff_pow_derivative_mul_le
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) (hα : α.length ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R ε : ℝ) (_hR : 0 < R) (_hε : 0 < ε)
      (x : ℝ^n) (a b : ℝ),
      2 * |a * iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ (2 * m)) x * b| ≤
        ε * radialCutoff R x ^ (2 * m) * a ^ 2 +
          C / ε * R⁻¹ ^ (2 * α.length) * b ^ 2 := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_abs_iteratedPartialDeriv_radialCutoff_two_mul_pow_le α hm hα
  refine ⟨B ^ 2, sq_nonneg _, ?_⟩
  intro R ε hR hε x a b
  have hprod :
      |a * iteratedPartialDeriv α (fun y ↦ radialCutoff R y ^ (2 * m)) x * b| ≤
        (radialCutoff R x ^ m * |a|) * (B * R⁻¹ ^ α.length * |b|) := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |a| * (B * R⁻¹ ^ α.length * radialCutoff R x ^ m) * |b| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound R hR x) (abs_nonneg a)) (abs_nonneg b)
      _ = _ := by ring
  have hsq :
      ((radialCutoff R x ^ m * |a|) * (B * R⁻¹ ^ α.length * |b|)) ^ 2 =
        (ε * radialCutoff R x ^ (2 * m) * a ^ 2) *
          (B ^ 2 / ε * R⁻¹ ^ (2 * α.length) * b ^ 2) := by
    simp only [mul_pow, sq_abs, Nat.mul_comm 2 m, Nat.mul_comm 2 α.length,
      pow_mul]
    field_simp
  exact (mul_le_mul_of_nonneg_left hprod (by norm_num)).trans
    (two_mul_le_add_of_sq_le_mul
      (mul_nonneg (mul_nonneg hε.le
        (pow_nonneg (radialCutoff_mem_Icc R x).1 _)) (sq_nonneg a))
      (mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg B) hε.le)
        (pow_nonneg (inv_nonneg.mpr hR.le) _)) (sq_nonneg b)) hsq.le)

end SobolevSpace.Approximation
