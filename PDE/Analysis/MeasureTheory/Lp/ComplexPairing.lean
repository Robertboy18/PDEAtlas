/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Complex integral pairings in `L²`

Real and imaginary projections of complex `L²` classes split integral
pairings, including real `L∞` coefficients and conjugated tests. Hölder
integrability justifies every integral identity on an arbitrary measure space.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Split an integrable complex-real `L²` pairing into its two real pairings. -/
theorem integral_complex_pairing
    (f : Lp ℂ 2 μ) (g : Lp ℝ 2 μ) :
    ∫ x, f x * (g x : ℂ) ∂μ =
      (⟪Complex.reCLM.compLpL 2 μ f, g⟫_ℝ : ℂ) +
        Complex.I * (⟪Complex.imCLM.compLpL 2 μ f, g⟫_ℝ : ℂ) := by
  have hint := (Lp.memLp f).integrable_mul (Lp.memLp g).ofReal
  have hr : ∫ x, (f x).re * g x ∂μ =
      ⟪Complex.reCLM.compLpL 2 μ f, g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Complex.reCLM.coeFn_compLpL f] with x hx
    simp [hx, mul_comm]
  have hi : ∫ x, (f x).im * g x ∂μ =
      ⟪Complex.imCLM.compLpL 2 μ f, g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Complex.imCLM.coeFn_compLpL f] with x hx
    simp [hx, mul_comm]
  apply Complex.ext
  · have h := integral_re hint
    simpa [Complex.mul_re, hr] using h.symm
  · have h := integral_im hint
    simpa [Complex.mul_im, hi] using h.symm

/-- Split a complex-real `L²` pairing with a real essentially bounded multiplier. -/
theorem integral_complex_coefficient_pairing
    (a : Lp ℝ ∞ μ) (f : Lp ℂ 2 μ)
    (g : Lp ℝ 2 μ) :
    ∫ x, (a x : ℂ) * f x * (g x : ℂ) ∂μ =
      (⟪a • Complex.reCLM.compLpL 2 μ f, g⟫_ℝ : ℂ) +
        Complex.I * (⟪a • Complex.imCLM.compLpL 2 μ f, g⟫_ℝ : ℂ) := by
  have haf : MemLp (fun x ↦ (a x : ℂ) * f x) 2 μ :=
    (Lp.memLp a).ofReal.mul (Lp.memLp f)
  let af := haf.toLp (fun x ↦ (a x : ℂ) * f x)
  have hre : Complex.reCLM.compLpL 2 μ af =
      a • Complex.reCLM.compLpL 2 μ f := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLpL af, haf.coeFn_toLp,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a (Complex.reCLM.compLpL 2 μ f),
      Complex.reCLM.coeFn_compLpL f] with x hx ha hs hf
    change af x = _ at ha
    change (a • Complex.reCLM.compLpL 2 μ f : Lp ℝ 2 μ) x = _ at hs
    simp only [smul_eq_mul, Pi.mul_apply] at hs
    rw [hx, ha, hs, hf]
    simp
  have him : Complex.imCLM.compLpL 2 μ af =
      a • Complex.imCLM.compLpL 2 μ f := by
    apply Lp.ext
    filter_upwards [Complex.imCLM.coeFn_compLpL af, haf.coeFn_toLp,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a (Complex.imCLM.compLpL 2 μ f),
      Complex.imCLM.coeFn_compLpL f] with x hx ha hs hf
    change af x = _ at ha
    change (a • Complex.imCLM.compLpL 2 μ f : Lp ℝ 2 μ) x = _ at hs
    simp only [smul_eq_mul, Pi.mul_apply] at hs
    rw [hx, ha, hs, hf]
    simp
  rw [← hre, ← him, ← integral_complex_pairing af g]
  apply integral_congr_ae
  filter_upwards [haf.coeFn_toLp] with x hx
  rw [hx]

/-- Split a conjugated `L²` test into its real and imaginary parts. -/
theorem integral_mul_conj_eq
    (f : X → ℂ) (hf : MemLp f 2 μ)
    (g : Lp ℂ 2 μ) :
    ∫ x, f x * star (g x) ∂μ =
      (∫ x, f x * (Complex.reCLM.compLpL 2 μ g x : ℂ)
        ∂μ) -
      Complex.I * ∫ x, f x * (Complex.imCLM.compLpL 2 μ g x : ℂ)
        ∂μ := by
  have hr := hf.integrable_mul
    (Lp.memLp (Complex.reCLM.compLpL 2 μ g)).ofReal
  have hi := hf.integrable_mul
    (Lp.memLp (Complex.imCLM.compLpL 2 μ g)).ofReal
  change Integrable (fun x ↦ f x *
    (Complex.reCLM.compLpL 2 μ g x : ℂ)) μ at hr
  change Integrable (fun x ↦ f x *
    (Complex.imCLM.compLpL 2 μ g x : ℂ)) μ at hi
  rw [← integral_const_mul, ← integral_sub hr (hi.const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards [Complex.reCLM.coeFn_compLpL g, Complex.imCLM.coeFn_compLpL g]
    with x hxr hxi
  simp only [hxr, hxi, Complex.reCLM_apply, Complex.imCLM_apply]
  apply Complex.ext <;> simp
  ring

end MeasureTheory.Lp
