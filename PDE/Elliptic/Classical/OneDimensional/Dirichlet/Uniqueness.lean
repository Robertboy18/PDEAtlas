/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.OneDimensional.Dirichlet

/-!
# Uniqueness of nonresonant Dirichlet oscillators

Nonresonance makes the two Dirichlet values determine a forced oscillator
uniquely. Consequently residual bounds for approximate solutions apply to the
explicit solution `dirichletSolution` itself.

## Main results

* `oscillator_eq_of_dirichlet_boundary`: two nonresonant oscillator solutions with the same
  forcing and the same Dirichlet values agree everywhere.
* `dirichletSolution_error_le_of_residual_bound`: a residual bound controls the distance to
  `dirichletSolution`, including the first derivative.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Classical.OneDimensional

/-- For `sin (a L) ≠ 0` (so `a ≠ 0`), a `C²` solution of `-d'' - a² d = 0` with `d 0 = d L = 0`
vanishes identically. -/
private theorem oscillator_eq_zero_of_dirichlet
    {a L : ℝ} (hsin : Real.sin (a * L) ≠ 0)
    {d : ℝ → ℝ} (hd : ContDiff ℝ 2 d)
    (heq : ∀ t, -deriv (deriv d) t - a ^ 2 * d t = 0)
    (hzero : d 0 = 0) (hL : d L = 0) : d = 0 := by
  have ha : a ≠ 0 := by rintro rfl; simp at hsin
  let A : ℝ := deriv d 0 / a
  let s : ℝ → ℝ := fun t ↦ A * Real.sin (a * t)
  have hs : ContDiff ℝ 2 s := contDiff_const.mul
    (contDiff_const.mul contDiff_id).sin
  have hsfirst : deriv s = fun t ↦ A * a * Real.cos (a * t) := by
    funext t
    simpa only [s, id_eq, mul_one, mul_assoc, mul_comm, mul_left_comm] using
      ((((hasDerivAt_id t).const_mul a).sin).const_mul A).deriv
  have hssecond (t : ℝ) : deriv (deriv s) t = -A * a ^ 2 * Real.sin (a * t) := by
    rw [hsfirst]
    have h := ((((hasDerivAt_id t).const_mul a).cos).const_mul (A * a)).deriv
    simp only [id_eq, mul_one] at h
    rw [h]
    ring
  have hds : d = s := oscillator_eq_of_initial_jet a 0 hd hs heq
    (by intro t; rw [hssecond]; dsimp [s]; ring)
    (by simp [s, hzero]) (by
      rw [hsfirst]
      simp only [mul_zero, Real.cos_zero, mul_one]
      exact (div_mul_cancel₀ _ ha).symm)
  have hAL : A * Real.sin (a * L) = 0 := by
    simpa only [hL, s] using (congrFun hds L).symm
  have hA : A = 0 := (mul_eq_zero.mp hAL).resolve_right hsin
  rw [hds]
  funext t
  simp [s, hA]

/-- Two nonresonant oscillator solutions with the same forcing and Dirichlet
values agree globally. The common boundary values need not vanish. -/
theorem oscillator_eq_of_dirichlet_boundary
    {a L : ℝ} (hsin : Real.sin (a * L) ≠ 0)
    {f q g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hq : ContDiff ℝ 2 q)
    (heqf : ∀ t, -deriv (deriv f) t - a ^ 2 * f t = g t)
    (heqq : ∀ t, -deriv (deriv q) t - a ^ 2 * q t = g t)
    (hzero : f 0 = q 0) (hL : f L = q L) : f = q := by
  have hfirst : deriv (f - q) = deriv f - deriv q := by
    funext t
    exact deriv_sub (hf.differentiable (by norm_num) t) (hq.differentiable (by norm_num) t)
  have hsecond : deriv (deriv (f - q)) = deriv (deriv f) - deriv (deriv q) := by
    rw [hfirst]
    funext t
    exact deriv_sub (hf.differentiable_deriv_two t) (hq.differentiable_deriv_two t)
  apply sub_eq_zero.mp
  apply oscillator_eq_zero_of_dirichlet hsin (hf.sub hq)
  · intro t
    change -deriv (deriv (f - q)) t - a ^ 2 * (f - q) t = 0
    rw [hsecond]
    change -(deriv (deriv f) t - deriv (deriv q) t) - a ^ 2 * (f t - q t) = 0
    linarith [heqf t, heqq t]
  · exact sub_eq_zero.mpr hzero
  · exact sub_eq_zero.mpr hL

/-- A residual bound controls the distance to `dirichletSolution` itself, including
the first derivative, rather than to some nearby solution. -/
theorem dirichletSolution_error_le_of_residual_bound
    {a L M : ℝ} (ha : 0 < a)
    (hsin : Real.sin (a * L) ≠ 0)
    {q g : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (hg : Continuous g)
    (hq₀ : q 0 = 0) (hqL : q L = 0)
    (hresidual : ∀ β ∈ Set.Icc 0 L,
      |g β + deriv (deriv q) β + a ^ 2 * q β| ≤ M) :
    ∀ β ∈ Set.Icc 0 L,
      |dirichletSolution a L g β - q β| ≤
        2 * M * L / a * (1 + 1 / |Real.sin (a * L)|) ∧
      |deriv (dirichletSolution a L g) β - deriv q β| ≤
        2 * M * L * (1 + 1 / |Real.sin (a * L)|) := by
  obtain ⟨f, hf, hfzero, hfL, hfeq, herror⟩ :=
    exists_dirichletSolution_near_of_residual_bound ha hsin hq hg hq₀ hqL hresidual
  have heq : f = dirichletSolution a L g :=
    oscillator_eq_of_dirichlet_boundary hsin hf
      (contDiff_dirichletSolution ha.ne' L hg) hfeq
      (dirichletSolution_equation ha.ne' L hg)
      (by rw [hfzero, dirichletSolution_zero])
      (by rw [hfL, dirichletSolution_right hsin])
  simpa only [heq] using herror

end PDE.Elliptic.Classical.OneDimensional
