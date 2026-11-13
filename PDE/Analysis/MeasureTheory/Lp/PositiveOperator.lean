/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Norm domination by positive operators on real `Lᵖ`

Positivity preserves almost-everywhere order. Applied to all real linear
combinations of two coordinates, it also preserves a pointwise bound on
their Euclidean norm. Rational coefficients give one common conull set;
continuity then recovers every real coefficient.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LinearMap

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

/-- A positive real `Lᵖ` operator preserves almost-everywhere order. -/
theorem map_le_map_ae_of_nonneg
    (A : Lp ℝ p μ →ₗ[ℝ] Lp ℝ p μ)
    (hA : ∀ v : Lp ℝ p μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    {f g : Lp ℝ p μ} (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    ∀ᵐ x ∂μ, A f x ≤ A g x := by
  have hsub : ∀ᵐ x ∂μ, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx hsub
    simpa only [hsub, Pi.sub_apply, sub_nonneg] using hx
  have h := hA (g - f) hsub
  rw [map_sub] at h
  filter_upwards [h, Lp.coeFn_sub (A g) (A f)] with x hx hsub
  simpa only [hsub, Pi.sub_apply, sub_nonneg] using hx

/-- A positive real operator preserves a bound for the Euclidean norm of two
coordinates. No kernel representation or continuity of the operator is needed. -/
theorem norm_pair_apply_le_of_nonneg
    (A : Lp ℝ p μ →ₗ[ℝ] Lp ℝ p μ)
    (hA : ∀ v : Lp ℝ p μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    (f g w : Lp ℝ p μ)
    (hfg : ∀ᵐ x ∂μ, ‖(⟨f x, g x⟩ : ℂ)‖ ≤ w x) :
    ∀ᵐ x ∂μ, ‖(⟨A f x, A g x⟩ : ℂ)‖ ≤ A w x := by
  have hw : ∀ᵐ x ∂μ, 0 ≤ w x :=
    hfg.mono fun x hx ↦ (norm_nonneg _).trans hx
  have hlinear (a b : ℝ) :
      ∀ᵐ x ∂μ, a * A f x + b * A g x ≤ ‖(⟨a, b⟩ : ℂ)‖ * A w x := by
    have hpoint : ∀ᵐ x ∂μ, (a • f + b • g) x ≤ (‖(⟨a, b⟩ : ℂ)‖ • w) x := by
      filter_upwards [hfg, Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f,
        Lp.coeFn_smul b g, Lp.coeFn_smul ‖(⟨a, b⟩ : ℂ)‖ w]
          with x hx hadd ha hb hw
      simp only [hadd, ha, hb, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hcs : a * f x + b * g x ≤
          ‖(⟨a, b⟩ : ℂ)‖ * ‖(⟨f x, g x⟩ : ℂ)‖ := by
        simpa [Complex.mul_re, mul_comm] using
          (Complex.re_le_norm (star (⟨a, b⟩ : ℂ) * (⟨f x, g x⟩ : ℂ)))
      exact hcs.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have h := A.map_le_map_ae_of_nonneg hA hpoint
    rw [map_add, map_smul, map_smul, map_smul] at h
    filter_upwards [h, Lp.coeFn_add (a • A f) (b • A g), Lp.coeFn_smul a (A f),
      Lp.coeFn_smul b (A g), Lp.coeFn_smul ‖(⟨a, b⟩ : ℂ)‖ (A w)]
        with x hx hadd ha hb hw
    simpa only [hadd, ha, hb, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx
  filter_upwards [ae_all_iff.mpr (fun a : ℚ ↦
    ae_all_iff.mpr (fun b : ℚ ↦ hlinear a b)), hA w hw] with x hx hwx
  have hall (a b : ℝ) :
      a * A f x + b * A g x ≤ ‖(⟨a, b⟩ : ℂ)‖ * A w x :=
    Rat.denseRange_cast.induction_on₂
      (p := fun a b : ℝ ↦ a * A f x + b * A g x ≤ ‖(⟨a, b⟩ : ℂ)‖ * A w x)
      (isClosed_le (by fun_prop)
        (Complex.equivRealProdCLM.symm.continuous.norm.mul_const (A w x))) hx a b
  have h := hall (A f x) (A g x)
  have hsq := Complex.sq_norm (⟨A f x, A g x⟩ : ℂ)
  simp only [Complex.normSq_apply] at hsq
  nlinarith [norm_nonneg (⟨A f x, A g x⟩ : ℂ)]

end LinearMap
