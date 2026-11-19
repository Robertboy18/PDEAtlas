/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2
public import PDE.Analysis.Approximation.BilinearInterpolation

/-!
# Bilinear interpolation of trigonometric tables in reparametrized variables

The value of a table along a reparametrization `t ↦ φ t` of its first variable has the second
derivative `p_ββ (φ t) φ' (t) ^ 2 + p_β (φ t) φ'' (t)` in `t`, so bounds of the derivative tables
and of `φ'`, `φ''` give the bilinear interpolation error of `(t, θ) ↦ p (φ t, θ)` on a cell
(`abs_eval_comp_sub_bilinearInterpolant_le`). The derivative tables are the derivatives of the
values (`deriv_eval_β`, `iteratedDeriv_two_eval_β`, `iteratedDeriv_two_eval_θ`). The
reparametrizations used for the compactified radius are `t ↦ arctan (κ t)`
(`hasDerivAt_arctan_mul`, `hasDerivAt_arctan_mul_deriv`) and `u ↦ π / 2 - arctan u`
(`hasDerivAt_pi_div_two_sub_arctan`, `hasDerivAt_pi_div_two_sub_arctan_deriv`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open PDE.Analysis.Approximation Set

variable {Mβ Mθ : ℕ}

theorem deriv_eval_β (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    deriv (fun t ↦ p.eval t θ) β = (dβ p).eval β θ := by
  exact (hasDerivAt_eval_β p β θ).deriv

theorem iteratedDeriv_two_eval_β (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    iteratedDeriv 2 (fun t ↦ p.eval t θ) β = (dβ (dβ p)).eval β θ := by
  have h : deriv (fun t ↦ p.eval t θ) = fun t ↦ (dβ p).eval t θ :=
    funext fun t ↦ deriv_eval_β p t θ
  rw [iteratedDeriv_succ, iteratedDeriv_one, h, deriv_eval_β]

theorem iteratedDeriv_two_eval_θ (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    iteratedDeriv 2 (fun u ↦ p.eval β u) θ = (dθ (dθ p)).eval β θ := by
  have h : deriv (fun u ↦ p.eval β u) = fun u ↦ (dθ p).eval β u :=
    funext fun u ↦ (hasDerivAt_eval_θ p β u).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h]
  exact (hasDerivAt_eval_θ (dθ p) β θ).deriv

/-- **Bilinear interpolation along a reparametrization.** -/
theorem abs_eval_comp_sub_bilinearInterpolant_le (p : TrigPoly2 Mβ Mθ ℝ)
    {φ φ' φ'' : ℝ → ℝ} {a b c d t θ D₁ D₂ D₃ P₁ P₂ : ℝ} (hab : a < b) (hcd : c < d)
    (hφ : ∀ u, HasDerivAt φ (φ' u) u) (hφ' : ∀ u, HasDerivAt φ' (φ'' u) u)
    (hP₁ : ∀ u ∈ Icc a b, φ' u ^ 2 ≤ P₁) (hP₂ : ∀ u ∈ Icc a b, |φ'' u| ≤ P₂)
    (hD₁ : ∀ β θ, |(dβ p).eval β θ| ≤ D₁) (hD₂ : ∀ β θ, |(dβ (dβ p)).eval β θ| ≤ D₂)
    (hD₃ : ∀ β θ, |(dθ (dθ p)).eval β θ| ≤ D₃) (ht : t ∈ Icc a b) (hθ : θ ∈ Icc c d) :
    |p.eval (φ t) θ - bilinearInterpolant (fun u w ↦ p.eval (φ u) w) a b c d t θ| ≤
      (D₂ * P₁ + D₁ * P₂) * (b - a) ^ 2 / 8 + D₃ * (d - c) ^ 2 / 8 := by
  have hfx (u w : ℝ) :
      HasDerivAt (fun z ↦ p.eval (φ z) w) ((dβ p).eval (φ u) w * φ' u) u :=
    (hasDerivAt_eval_β p (φ u) w).comp u (hφ u)
  have hfxx (u w : ℝ) : HasDerivAt (fun z ↦ (dβ p).eval (φ z) w * φ' z)
      ((dβ (dβ p)).eval (φ u) w * φ' u ^ 2 + (dβ p).eval (φ u) w * φ'' u) u := by
    have h1 : HasDerivAt (fun z ↦ (dβ p).eval (φ z) w) ((dβ (dβ p)).eval (φ u) w * φ' u) u :=
      (hasDerivAt_eval_β (dβ p) (φ u) w).comp u (hφ u)
    exact (h1.mul (hφ' u)).congr_deriv (by ring)
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0 0)
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hD₂ 0 0)
  refine abs_sub_bilinearInterpolant_le (f := fun u w ↦ p.eval (φ u) w)
    (fx := fun u w ↦ (dβ p).eval (φ u) w * φ' u)
    (fxx := fun u w ↦ (dβ (dβ p)).eval (φ u) w * φ' u ^ 2 + (dβ p).eval (φ u) w * φ'' u)
    (fy := fun u w ↦ (dθ p).eval (φ u) w) (fyy := fun u w ↦ (dθ (dθ p)).eval (φ u) w)
    hab hcd
    (fun v _ ↦ (continuous_iff_continuousAt.2 fun u ↦ (hfx u v).continuousAt).continuousOn)
    (fun v _ u _ ↦ hfx u v) (fun v _ u _ ↦ hfxx u v) ?_
    (fun u _ ↦ (continuous_eval_θ p (φ u)).continuousOn)
    (fun u _ v _ ↦ hasDerivAt_eval_θ p (φ u) v)
    (fun u _ v _ ↦ hasDerivAt_eval_θ (dθ p) (φ u) v) (fun u _ v _ ↦ hD₃ _ _) ht hθ
  intro v _ u hu
  have hu' : u ∈ Icc a b := Ioo_subset_Icc_self hu
  calc |(dβ (dβ p)).eval (φ u) v * φ' u ^ 2 + (dβ p).eval (φ u) v * φ'' u|
      ≤ |(dβ (dβ p)).eval (φ u) v * φ' u ^ 2| + |(dβ p).eval (φ u) v * φ'' u| :=
        abs_add_le _ _
    _ = |(dβ (dβ p)).eval (φ u) v| * φ' u ^ 2 + |(dβ p).eval (φ u) v| * |φ'' u| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (φ' u))]
    _ ≤ D₂ * P₁ + D₁ * P₂ :=
        add_le_add (mul_le_mul (hD₂ _ _) (hP₁ u hu') (sq_nonneg _) hD₂0)
          (mul_le_mul (hD₁ _ _) (hP₂ u hu') (abs_nonneg _) hD₁0)

theorem hasDerivAt_arctan_mul (κ t : ℝ) :
    HasDerivAt (fun s ↦ Real.arctan (κ * s)) (κ / (1 + (κ * t) ^ 2)) t := by
  convert ((hasDerivAt_id' t).const_mul κ).arctan using 1
  ring

theorem hasDerivAt_arctan_mul_deriv (κ t : ℝ) :
    HasDerivAt (fun s ↦ κ / (1 + (κ * s) ^ 2))
      (-(2 * κ ^ 3 * t) / (1 + (κ * t) ^ 2) ^ 2) t := by
  have hd : HasDerivAt (fun s ↦ 1 + (κ * s) ^ 2) (2 * (κ * t) * κ) t := by
    convert (((hasDerivAt_id' t).const_mul κ).pow 2).const_add 1 using 1
    ring
  have hne : 1 + (κ * t) ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_const t κ).div hd hne using 1
  ring

theorem hasDerivAt_pi_div_two_sub_arctan (u : ℝ) :
    HasDerivAt (fun s ↦ Real.pi / 2 - Real.arctan s) (-(1 / (1 + u ^ 2))) u := by
  exact (Real.hasDerivAt_arctan u).const_sub (Real.pi / 2)

theorem hasDerivAt_pi_div_two_sub_arctan_deriv (u : ℝ) :
    HasDerivAt (fun s ↦ -(1 / (1 + s ^ 2))) (2 * u / (1 + u ^ 2) ^ 2) u := by
  have hd : HasDerivAt (fun s ↦ 1 + s ^ 2) (2 * u) u := by
    convert ((hasDerivAt_id' u).pow 2).const_add 1 using 1
    ring
  have hne : 1 + u ^ 2 ≠ 0 := by positivity
  convert ((hasDerivAt_const u (1 : ℝ)).div hd hne).neg using 1
  ring

end PDE.Analysis.TrigPoly2
