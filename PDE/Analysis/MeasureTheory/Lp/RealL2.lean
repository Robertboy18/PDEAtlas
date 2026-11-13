/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real integrals and L² representatives

Square integrals give the finite real `L²` norm. For complex `L²` classes with
real representatives, ordinary product integrals compute the real part of the
inner product. Both facts hold for an arbitrary measure.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

/-- The ordinary square integral is the square of the finite real `L²` norm. -/
theorem integral_sq_eq_eLpNorm_toReal_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Real products of representatives compute the real part of the complex `L²` pairing. -/
theorem integral_mul_eq_re_inner {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {F G : Lp ℂ 2 μ}
    (hf : (fun x ↦ (f x : ℂ)) =ᵐ[μ] F)
    (hg : (fun x ↦ (g x : ℂ)) =ᵐ[μ] G) :
    (∫ x, f x * g x ∂μ) = (inner ℂ F G).re := by
  calc
    _ = ∫ x, (inner ℂ (F x) (G x)).re ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hx hy
      rw [← hx, ← hy, RCLike.inner_apply]
      simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
    _ = _ := by
      change (∫ x, RCLike.re (inner ℂ (F x) (G x)) ∂μ) = RCLike.re (inner ℂ F G)
      rw [integral_re (L2.integrable_inner (𝕜 := ℂ) F G), ← L2.inner_def]

end MeasureTheory
