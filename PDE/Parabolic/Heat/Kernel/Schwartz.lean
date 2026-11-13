/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The time-one heat kernel is a Schwartz function

At time one the heat kernel is `(4π)^(-n/2) exp(B x x)` with the bilinear form
`B = -(1/4) ⟪·, ·⟫` of norm at most one. The bound for derivatives of a bilinear expression gives
`‖Dⁱ (B x x)‖ ≤ 2ⁱ (1 + ‖x‖)²`, and the bound for derivatives of a composition then gives
`‖Dᵐ exp(B x x)‖ ≤ m! exp(-‖x‖²/4) (2 (1 + ‖x‖)²)ᵐ`. Polynomials times `exp(-‖x‖²/4)` are bounded,
since `(1 + s)²ʲ ≤ 8ʲ j! exp((1 + s)²/8)` and `(1 + s)²/8 - s²/4 ≤ 1/4`.
-/

@[expose] public noncomputable section

open scoped SchwartzMap ContDiff Nat

section General

namespace PDE

/-- The derivatives of the identity are bounded by `1 + ‖x‖`. -/
theorem norm_iteratedFDeriv_id_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (i : ℕ)
    (x : V) : ‖iteratedFDeriv ℝ i (fun y : V ↦ y) x‖ ≤ 1 + ‖x‖ := by
  cases i with
  | zero => rw [norm_iteratedFDeriv_zero]; linarith
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hid : fderiv ℝ (fun y : V ↦ y) = fun _ ↦ ContinuousLinearMap.id ℝ V :=
      funext fun _ ↦ fderiv_fun_id
    rw [hid]
    cases i with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V), norm_nonneg x]
    | succ i =>
      rw [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      positivity

/-- Polynomial factors are absorbed by the Gaussian `exp(-s²/4)`. -/
theorem one_add_pow_mul_exp_neg_le (j : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ j * Real.exp (-(s ^ 2 / 4)) ≤ 8 ^ j * j ! * Real.exp (1 / 4) := by
  have h1 : 1 ≤ 1 + s := by linarith
  have hu : 0 ≤ (1 + s) ^ 2 / 8 := by positivity
  have hfac := Real.pow_div_factorial_le_exp (x := (1 + s) ^ 2 / 8) hu j
  have hfac' : ((1 + s) ^ 2 / 8) ^ j ≤ j ! * Real.exp ((1 + s) ^ 2 / 8) := by
    rw [div_le_iff₀ (by positivity)] at hfac
    linarith
  have hpow : (1 + s) ^ j ≤ (1 + s) ^ (2 * j) := pow_le_pow_right₀ h1 (by omega)
  have hsq : (1 + s) ^ (2 * j) = 8 ^ j * ((1 + s) ^ 2 / 8) ^ j := by
    rw [div_pow, pow_mul]
    field_simp
  have hexp : Real.exp ((1 + s) ^ 2 / 8) * Real.exp (-(s ^ 2 / 4)) ≤ Real.exp (1 / 4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (s - 1)]
  calc
    _ ≤ (1 + s) ^ (2 * j) * Real.exp (-(s ^ 2 / 4)) := by gcongr
    _ = 8 ^ j * ((1 + s) ^ 2 / 8) ^ j * Real.exp (-(s ^ 2 / 4)) := by rw [hsq]
    _ ≤ 8 ^ j * (j ! * Real.exp ((1 + s) ^ 2 / 8)) * Real.exp (-(s ^ 2 / 4)) := by gcongr
    _ = 8 ^ j * j ! * (Real.exp ((1 + s) ^ 2 / 8) * Real.exp (-(s ^ 2 / 4))) := by ring
    _ ≤ _ := by gcongr

end PDE

end General

namespace HeatEquation

variable {n : ℕ}

/-- The quadratic form `-‖x‖²/4` as a bilinear expression. -/
def heatQuadratic (n : ℕ) : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ :=
  (-(1 / 4 : ℝ)) • innerSL ℝ

theorem heatQuadratic_apply_apply (x y : ℝ^n) :
    heatQuadratic n x y = -(1 / 4) * inner ℝ x y := by
  change (-(1 / 4 : ℝ)) * innerSL ℝ x y = _
  rw [innerSL_apply_apply]

theorem heatQuadratic_apply (x : ℝ^n) : heatQuadratic n x x = -(‖x‖ ^ 2 / 4) := by
  rw [heatQuadratic_apply_apply, real_inner_self_eq_norm_sq]
  ring

theorem norm_heatQuadratic_le : ‖heatQuadratic n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun x y ↦ ?_
  rw [heatQuadratic_apply_apply, norm_mul, one_mul]
  have h := abs_real_inner_le_norm x y
  rw [Real.norm_eq_abs] at *
  have hc : |(-(1 / 4 : ℝ))| = 1 / 4 := by norm_num
  rw [hc, Real.norm_eq_abs]
  nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y), abs_nonneg (inner ℝ x y)]

/-- Derivatives of the quadratic exponent. -/
theorem norm_iteratedFDeriv_heatQuadratic_le (i : ℕ) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ i (fun y ↦ heatQuadratic n y y) x‖ ≤ 2 ^ i * (1 + ‖x‖) ^ 2 := by
  refine ((heatQuadratic n).norm_iteratedFDeriv_le_of_bilinear_of_le_one contDiff_id contDiff_id
    x (N := (⊤ : ℕ∞)) (by exact_mod_cast le_top) norm_heatQuadratic_le).trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
      gcongr with j
      · exact PDE.norm_iteratedFDeriv_id_le j x
      · exact PDE.norm_iteratedFDeriv_id_le (i - j) x
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) = 2 ^ i := by
        exact_mod_cast Nat.sum_range_choose i
      rw [hsum]
      ring

theorem contDiff_heatQuadratic :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^n ↦ heatQuadratic n y y) :=
  (heatQuadratic n).contDiff.clm_apply contDiff_id

/-- Derivatives of the Gaussian `exp(-‖x‖²/4)`. -/
theorem norm_iteratedFDeriv_exp_heatQuadratic_le (m : ℕ) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ m (fun y ↦ Real.exp (heatQuadratic n y y)) x‖ ≤
      m ! * Real.exp (-(‖x‖ ^ 2 / 4)) * (2 * (1 + ‖x‖) ^ 2) ^ m := by
  have h := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y ↦ heatQuadratic n y y)
    (n := m) (N := (⊤ : ℕ∞)) Real.contDiff_exp contDiff_heatQuadratic (by exact_mod_cast le_top) x
    (C := Real.exp (heatQuadratic n x x)) (D := 2 * (1 + ‖x‖) ^ 2)
    (fun i _ ↦ by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
    (fun i hi _ ↦ by
      refine (norm_iteratedFDeriv_heatQuadratic_le i x).trans ?_
      rw [mul_pow, ← pow_mul]
      have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (by positivity))
  simpa only [Function.comp_def, heatQuadratic_apply] using h

/-- The normalizing constant `(4π)^(-n/2)` of the time-one heat kernel. -/
def heatKernelConstant (n : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-(n : ℝ) / 2)

theorem heatKernelConstant_pos (n : ℕ) : 0 < heatKernelConstant n := by
  unfold heatKernelConstant
  positivity

theorem fundamentalSolutionHeat_one_eq (x : ℝ^n) :
    fundamentalSolutionHeat x 1 = heatKernelConstant n * Real.exp (heatQuadratic n x x) := by
  norm_num [heatQuadratic_apply, fundamentalSolutionHeat, heatKernelConstant]

theorem contDiff_fundamentalSolutionHeat_one :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ fundamentalSolutionHeat x 1) := by
  simp_rw [fundamentalSolutionHeat_one_eq]
  exact contDiff_const.mul (Real.contDiff_exp.comp contDiff_heatQuadratic)

/-- The time-one heat kernel as a Schwartz function. -/
def heatKernelSchwartz (n : ℕ) : 𝓢(ℝ^n, ℝ) where
  toFun x := fundamentalSolutionHeat x 1
  smooth' := contDiff_fundamentalSolutionHeat_one.of_le (by exact_mod_cast le_top)
  decay' k m := by
    refine ⟨heatKernelConstant n * m ! * 2 ^ m * (8 ^ (k + 2 * m) * (k + 2 * m) ! *
      Real.exp (1 / 4)), fun x ↦ ?_⟩
    have hfun : (fun x : ℝ^n ↦ fundamentalSolutionHeat x 1) =
        heatKernelConstant n • fun x ↦ Real.exp (heatQuadratic n x x) := by
      funext x
      rw [fundamentalSolutionHeat_one_eq, Pi.smul_apply, smul_eq_mul]
    have hexp : ContDiffAt ℝ m (fun x ↦ Real.exp (heatQuadratic n x x)) x :=
      ((Real.contDiff_exp.comp (contDiff_heatQuadratic (n := n))).contDiffAt (x := x)).of_le
        (by exact_mod_cast le_top)
    rw [hfun, iteratedFDeriv_const_smul_apply hexp, norm_smul,
      Real.norm_eq_abs, abs_of_pos (heatKernelConstant_pos n)]
    have hb := norm_iteratedFDeriv_exp_heatQuadratic_le (n := n) m x
    have hpoly := PDE.one_add_pow_mul_exp_neg_le (k + 2 * m) (norm_nonneg x)
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    have hc := (heatKernelConstant_pos n).le
    calc
      _ ≤ ‖x‖ ^ k * (heatKernelConstant n *
          (m ! * Real.exp (-(‖x‖ ^ 2 / 4)) * (2 * (1 + ‖x‖) ^ 2) ^ m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hc) (by positivity)
      _ ≤ (1 + ‖x‖) ^ k * (heatKernelConstant n *
          (m ! * Real.exp (-(‖x‖ ^ 2 / 4)) * (2 * (1 + ‖x‖) ^ 2) ^ m)) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg hc (by positivity))
      _ = heatKernelConstant n * m ! * 2 ^ m *
          ((1 + ‖x‖) ^ (k + 2 * m) * Real.exp (-(‖x‖ ^ 2 / 4))) := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (mul_nonneg (mul_nonneg hc (by positivity))
        (by positivity))

@[simp]
theorem heatKernelSchwartz_apply (x : ℝ^n) :
    heatKernelSchwartz n x = fundamentalSolutionHeat x 1 := rfl

end HeatEquation
