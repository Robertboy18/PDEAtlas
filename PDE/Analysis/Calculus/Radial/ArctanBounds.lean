/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivative decay under radial arctangent compactification

A twice continuously differentiable function has bounded derivatives on the
closed arctangent range. The exact first two derivatives of the compactification
then give quadratic and cubic decay, respectively.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

/-- The scaled arctangent has its exact rational derivative. -/
theorem hasDerivAt_arctan_div {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    HasDerivAt (fun t ↦ Real.arctan (t / s)) (s / (s ^ 2 + r ^ 2)) r := by
  have hden : s ^ 2 + r ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg r)).ne'
  convert ((hasDerivAt_id r).div_const s).arctan using 1
  · rfl
  · dsimp
    field_simp

/-- Twice differentiating a compactified function retains both chain-rule terms. The codomain is
any normed space and only `C²` regularity at the compactified point is used. -/
theorem hasDerivAt_deriv_comp_arctan_div_of_contDiffAt {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {s : ℝ} (hs : s ≠ 0) {g : ℝ → G} {r : ℝ}
    (hg : ContDiffAt ℝ 2 g (Real.arctan (r / s))) :
    HasDerivAt (deriv (fun t ↦ g (Real.arctan (t / s))))
      ((s / (s ^ 2 + r ^ 2)) ^ 2 • deriv (deriv g) (Real.arctan (r / s)) +
        (-2 * r * s / (s ^ 2 + r ^ 2) ^ 2) • deriv g (Real.arctan (r / s))) r := by
  have hden : s ^ 2 + r ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg r)).ne'
  have hδ : HasDerivAt (fun t ↦ s / (s ^ 2 + t ^ 2))
      (-2 * r * s / (s ^ 2 + r ^ 2) ^ 2) r := by
    convert (hasDerivAt_const r s).div
      (((hasDerivAt_id r).pow 2).const_add (s ^ 2)) hden using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, mul_one, zero_mul, zero_sub]
      ring
  have hnear : ∀ᶠ t in nhds r, DifferentiableAt ℝ g (Real.arctan (t / s)) :=
    (hasDerivAt_arctan_div hs r).continuousAt.eventually
      ((hg.eventually (by simp)).mono fun _ hb ↦ hb.differentiableAt (by norm_num))
  have heq : deriv (fun t ↦ g (Real.arctan (t / s))) =ᶠ[nhds r]
      fun t ↦ (s / (s ^ 2 + t ^ 2)) • deriv g (Real.arctan (t / s)) := by
    filter_upwards [hnear] with t ht
    exact (ht.hasDerivAt.scomp t (hasDerivAt_arctan_div hs t)).deriv
  have hDg : DifferentiableAt ℝ (deriv g) (Real.arctan (r / s)) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const (1 : ℝ))
  have hD := hδ.smul (hDg.hasDerivAt.scomp r (hasDerivAt_arctan_div hs r))
  refine (HasDerivAt.congr_of_eventuallyEq ?_ heq)
  convert hD using 1
  · rfl
  · rw [smul_smul, ← sq]
    rfl

/-- Twice differentiating a compactified scalar function retains both chain-rule terms. -/
theorem hasDerivAt_deriv_comp_arctan_div {s : ℝ} (hs : s ≠ 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    HasDerivAt (deriv (fun t ↦ g (Real.arctan (t / s))))
      (deriv (deriv g) (Real.arctan (r / s)) * (s / (s ^ 2 + r ^ 2)) ^ 2 +
        deriv g (Real.arctan (r / s)) * (-2 * r * s / (s ^ 2 + r ^ 2) ^ 2)) r := by
  convert hasDerivAt_deriv_comp_arctan_div_of_contDiffAt hs hg.contDiffAt using 1
  simp only [smul_eq_mul]
  ring

/-- Compactification bounds the value and gives quadratic first-derivative and
cubic second-derivative tails, with constants from the actual scalar function. -/
theorem exists_bounds_comp_arctan_div {s : ℝ} (hs : 0 < s)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    ∃ A ≥ 0, ∃ D ≥ 0, ∃ K ≥ 0, ∀ r : ℝ, 1 ≤ r →
      |g (Real.arctan (r / s))| ≤ A ∧
      |deriv (fun t ↦ g (Real.arctan (t / s))) r| ≤ D / r ^ 2 ∧
      |deriv (deriv (fun t ↦ g (Real.arctan (t / s)))) r| ≤ K / r ^ 3 := by
  let I := Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
  have hI : IsCompact I := isCompact_Icc
  have hDg : ContDiff ℝ 1 (deriv g) := hg.deriv'
  obtain ⟨A, hA, hAbound⟩ := (hI.image hg.continuous).isBounded.exists_pos_norm_le
  obtain ⟨D, hD, hDbound⟩ := (hI.image hDg.continuous).isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hKbound⟩ :=
    (hI.image hDg.continuous_deriv_one).isBounded.exists_pos_norm_le
  refine ⟨A, hA.le, s * D, by positivity, s ^ 2 * K + 2 * s * D,
    by positivity, fun r hr ↦ ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hβ : Real.arctan (r / s) ∈ I :=
    ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hvalue : |g (Real.arctan (r / s))| ≤ A := by
    simpa only [Real.norm_eq_abs] using hAbound _ (Set.mem_image_of_mem _ hβ)
  have hfirst : |deriv g (Real.arctan (r / s))| ≤ D := by
    simpa only [Real.norm_eq_abs] using hDbound _ (Set.mem_image_of_mem _ hβ)
  have hsecond : |deriv (deriv g) (Real.arctan (r / s))| ≤ K := by
    simpa only [Real.norm_eq_abs] using hKbound _ (Set.mem_image_of_mem _ hβ)
  have hδ : s / (s ^ 2 + r ^ 2) ≤ s / r ^ 2 :=
    div_le_div_of_nonneg_left hs.le (by positivity) (le_add_of_nonneg_left (sq_nonneg s))
  have hδnonneg : 0 ≤ s / (s ^ 2 + r ^ 2) := by positivity
  have h34 : r ^ 3 ≤ r ^ 4 := by
    simpa only [mul_one, ← pow_succ] using mul_le_mul_of_nonneg_left hr
      (pow_nonneg hrpos.le 3)
  have hden4 : r ^ 4 ≤ (s ^ 2 + r ^ 2) ^ 2 := by
    convert pow_le_pow_left₀ (sq_nonneg r)
      (le_add_of_nonneg_left (sq_nonneg s)) 2 using 1
    ring
  refine ⟨hvalue, ?_, ?_⟩
  · have hderiv :
        deriv (fun t ↦ g (Real.arctan (t / s))) r =
          deriv g (Real.arctan (r / s)) * (s / (s ^ 2 + r ^ 2)) := by
      simpa only [Function.comp_def] using
        ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt.comp r
          (hasDerivAt_arctan_div hs.ne' r)).deriv
    rw [hderiv, abs_mul, abs_of_nonneg hδnonneg]
    calc
      _ ≤ D * (s / r ^ 2) := mul_le_mul hfirst hδ hδnonneg hD.le
      _ = _ := by ring
  · rw [(hasDerivAt_deriv_comp_arctan_div hs.ne' hg r).deriv]
    have habs : |-2 * r * s / (s ^ 2 + r ^ 2) ^ 2| =
        2 * r * s / (s ^ 2 + r ^ 2) ^ 2 := by
      simp only [abs_div, abs_mul, abs_of_pos hs, abs_of_pos hrpos,
        abs_of_nonneg (sq_nonneg (s ^ 2 + r ^ 2))]
      norm_num
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (s / (s ^ 2 + r ^ 2))), habs]
    calc
      _ ≤ K * (s / r ^ 2) ^ 2 + D * (2 * r * s / r ^ 4) :=
        add_le_add
          (mul_le_mul hsecond (pow_le_pow_left₀ hδnonneg hδ 2) (sq_nonneg _) hK.le)
          (mul_le_mul hfirst
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hden4)
            (by positivity) hD.le)
      _ = K * s ^ 2 / r ^ 4 + (2 * s * D) / r ^ 3 := by field_simp
      _ ≤ K * s ^ 2 / r ^ 3 + (2 * s * D) / r ^ 3 := by
        apply add_le_add
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity) h34
        · exact le_rfl
      _ = _ := by ring

end PDE.Analysis.Radial
