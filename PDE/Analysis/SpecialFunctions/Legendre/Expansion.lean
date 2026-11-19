/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.Completeness
public import PDE.Analysis.Spectral.OrthogonalFamily

/-!
# Legendre series in `L²((0, π), sin θ dθ)`

The Legendre functions `P_l (cos θ)` are orthogonal with squared norms `c_l = 2 / (2l + 1)`, the
associated functions `sin θ · P_l' (cos θ)`, `l ≥ 1`, with `c_l = 2 l (l + 1) / (2l + 1)`, and
both families span dense subspaces of `L²((0, π), sin θ dθ)`. After normalization they are
Hilbert bases. Every `f` in the space is therefore the sum `∑ a_l P_l (cos θ)` of its Legendre
series, `a_l = ⟪P_l (cos θ), f⟫ / c_l`, and likewise of its associated series, with Parseval's
identity in both cases.

Under the reflection `θ ↦ π - θ`, which preserves `sin θ dθ`, the function `P_l (cos θ)` has the
parity `(-1)ˡ` and `sin θ · P_l' (cos θ)` has the parity `(-1)ˡ⁺¹`. A function of parity `ε`
therefore has vanishing coefficients on every mode of the other parity.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open MeasureTheory Polynomial Set PDE.Analysis.Spectral
open scoped RealInnerProductSpace

/-- The squared norm `2 / (2l + 1)` of `P_l (cos θ)` is positive. -/
theorem legendre_normSq_pos (l : ℕ) : 0 < 2 / (2 * (l : ℝ) + 1) := by positivity

/-- The Legendre Hilbert basis `√((2l + 1) / 2) · P_l (cos θ)` of `L²((0, π), sin θ dθ)`. -/
def legendreBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 polarAngleMeasure) :=
  hilbertBasisOfOrthogonal legendre_normSq_pos inner_legendreLp legendre_complete

/-- The elements of the Legendre Hilbert basis. -/
theorem legendreBasis_apply (l : ℕ) :
    legendreBasis l = (Real.sqrt (2 / (2 * (l : ℝ) + 1)))⁻¹ • legendreLp l :=
  hilbertBasisOfOrthogonal_apply _ _ _ l

/-- The Legendre coefficient `(2l + 1) / 2 · ∫ P_l (cos θ) f (θ) sin θ dθ`. -/
def legendreCoeff (f : Lp ℝ 2 polarAngleMeasure) (l : ℕ) : ℝ :=
  ⟪legendreLp l, f⟫ / (2 / (2 * (l : ℝ) + 1))

/-- **Legendre series.** Every `f ∈ L²((0, π), sin θ dθ)` is the sum of its Legendre series
`∑ a_l P_l (cos θ)`, `a_l = (2l + 1) / 2 · ∫ P_l (cos θ) f (θ) sin θ dθ`. -/
theorem hasSum_legendreCoeff_smul (f : Lp ℝ 2 polarAngleMeasure) :
    HasSum (fun l ↦ legendreCoeff f l • legendreLp l) f :=
  hasSum_inner_div_smul_of_orthogonal legendre_normSq_pos inner_legendreLp legendre_complete f

/-- Parseval's identity for the Legendre series: `‖f‖² = ∑ 2 / (2l + 1) · a_l²`. -/
theorem hasSum_sq_legendreCoeff (f : Lp ℝ 2 polarAngleMeasure) :
    HasSum (fun l : ℕ ↦ 2 / (2 * (l : ℝ) + 1) * legendreCoeff f l ^ 2) (‖f‖ ^ 2) := by
  convert hasSum_inner_sq_div_of_orthogonal legendre_normSq_pos inner_legendreLp
    legendre_complete f using 1
  funext l
  have h := legendre_normSq_pos l
  rw [legendreCoeff]
  field_simp

/-- The squared norm `2 (l + 1) (l + 2) / (2l + 3)` of `sin θ · P_{l+1}' (cos θ)` is
positive. -/
theorem associatedLegendre_normSq_pos (l : ℕ) :
    0 < 2 * ((l + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) + 1) / (2 * ((l + 1 : ℕ) : ℝ) + 1) := by
  positivity

/-- The associated Legendre functions of degree at least one are orthogonal. -/
theorem inner_associatedLegendreLp_succ (l m : ℕ) :
    ⟪associatedLegendreLp (l + 1), associatedLegendreLp (m + 1)⟫ =
      if l = m then 2 * ((l + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) + 1) / (2 * ((l + 1 : ℕ) : ℝ) + 1)
      else 0 := by
  rw [inner_associatedLegendreLp]
  simp only [Nat.add_right_cancel_iff]

/-- The associated Legendre Hilbert basis of `L²((0, π), sin θ dθ)`, indexed by `l` for the
degree `l + 1`. -/
def associatedLegendreBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 polarAngleMeasure) :=
  hilbertBasisOfOrthogonal associatedLegendre_normSq_pos inner_associatedLegendreLp_succ
    associatedLegendre_complete

/-- The associated Legendre coefficient `(2l + 1) / (2 l (l + 1)) · ∫ sin θ P_l' (cos θ) f (θ)
sin θ dθ`; it vanishes for `l = 0`. -/
def associatedLegendreCoeff (f : Lp ℝ 2 polarAngleMeasure) (l : ℕ) : ℝ :=
  ⟪associatedLegendreLp l, f⟫ / (2 * (l : ℝ) * (l + 1) / (2 * l + 1))

/-- **Associated Legendre series.** Every `f ∈ L²((0, π), sin θ dθ)` is the sum of its series
`∑ b_l sin θ P_l' (cos θ)`; the term `l = 0` is zero. -/
theorem hasSum_associatedLegendreCoeff_smul (f : Lp ℝ 2 polarAngleMeasure) :
    HasSum (fun l ↦ associatedLegendreCoeff f l • associatedLegendreLp l) f := by
  have h := hasSum_inner_div_smul_of_orthogonal associatedLegendre_normSq_pos
    inner_associatedLegendreLp_succ associatedLegendre_complete f
  rw [← hasSum_nat_add_iff' 1]
  simpa [associatedLegendreCoeff, associatedLegendreLp] using h

/-- The Legendre function has the parity `(-1)ˡ` under `θ ↦ π - θ`. -/
theorem legendre_eval_cos_pi_sub (l : ℕ) (θ : ℝ) :
    (legendre l).eval (Real.cos (Real.pi - θ)) = (-1) ^ l * (legendre l).eval (Real.cos θ) := by
  rw [Real.cos_pi_sub, legendre_eval_neg]

/-- Parseval's identity for the associated Legendre series:
`‖f‖² = ∑ 2 l (l + 1) / (2l + 1) · b_l²`. -/
theorem hasSum_sq_associatedLegendreCoeff (f : Lp ℝ 2 polarAngleMeasure) :
    HasSum (fun l : ℕ ↦ 2 * (l : ℝ) * (l + 1) / (2 * l + 1) * associatedLegendreCoeff f l ^ 2)
      (‖f‖ ^ 2) := by
  have h := hasSum_inner_sq_div_of_orthogonal associatedLegendre_normSq_pos
    inner_associatedLegendreLp_succ associatedLegendre_complete f
  rw [← hasSum_nat_add_iff' 1]
  convert h using 1
  · funext l
    have hl := associatedLegendre_normSq_pos l
    simp only [associatedLegendreCoeff]
    push_cast at hl ⊢
    field_simp
  · simp [associatedLegendreCoeff]

/-- The associated Legendre function has the parity `(-1)ˡ⁺¹` under `θ ↦ π - θ`. -/
theorem sin_mul_derivative_legendre_eval_cos_pi_sub (l : ℕ) (θ : ℝ) :
    Real.sin (Real.pi - θ) * (derivative (legendre l)).eval (Real.cos (Real.pi - θ)) =
      (-1) ^ (l + 1) * (Real.sin θ * (derivative (legendre l)).eval (Real.cos θ)) := by
  rw [Real.sin_pi_sub, Real.cos_pi_sub, derivative_legendre_eval_neg]
  ring

/-- If `g (π - θ) = s g (θ)` and `f (π - θ) = ε f (θ)` almost everywhere, then
`⟪g, f⟫ = s ε ⟪g, f⟫`. -/
theorem inner_toLp_eq_mul_of_reflection {g : ℝ → ℝ} (hg : MemLp g 2 polarAngleMeasure) {s ε : ℝ}
    (hgs : ∀ θ, g (Real.pi - θ) = s * g θ) {f : Lp ℝ 2 polarAngleMeasure}
    (hf : ∀ᵐ θ ∂polarAngleMeasure, f (Real.pi - θ) = ε * f θ) :
    ⟪hg.toLp g, f⟫ = s * ε * ⟪hg.toLp g, f⟫ := by
  calc ⟪hg.toLp g, f⟫ = ∫ θ, g θ * f θ ∂polarAngleMeasure := inner_toLp_polarAngleMeasure hg f
    _ = ∫ θ, g (Real.pi - θ) * f (Real.pi - θ) ∂polarAngleMeasure :=
        (integral_polarAngleMeasure_comp_pi_sub fun θ ↦ g θ * f θ).symm
    _ = ∫ θ, s * ε * (g θ * f θ) ∂polarAngleMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [hf] with θ hθ
        rw [hgs, hθ]
        ring
    _ = s * ε * ⟪hg.toLp g, f⟫ := by
        rw [integral_const_mul, inner_toLp_polarAngleMeasure]

/-- A real number equal to `s ε` times itself vanishes unless `ε = s`, for `s = ±1`. -/
theorem eq_zero_of_eq_mul_of_ne {a s ε : ℝ} (hs : s ^ 2 = 1) (ha : a = s * ε * a)
    (hε : ε ≠ s) : a = 0 := by
  by_contra h
  have h₁ : s * ε = 1 := by
    have := mul_right_cancel₀ h (ha.symm.trans (one_mul a).symm)
    exact this
  apply hε
  calc ε = s ^ 2 * ε := by rw [hs, one_mul]
    _ = s * (s * ε) := by ring
    _ = s := by rw [h₁, mul_one]

/-- **Parity of the Legendre series.** If `f (π - θ) = ε f (θ)` almost everywhere, the
coefficient of `P_l (cos θ)` vanishes unless `ε = (-1)ˡ`. -/
theorem legendreCoeff_eq_zero_of_parity {f : Lp ℝ 2 polarAngleMeasure} {ε : ℝ}
    (hf : ∀ᵐ θ ∂polarAngleMeasure, f (Real.pi - θ) = ε * f θ) {l : ℕ} (hl : ε ≠ (-1) ^ l) :
    legendreCoeff f l = 0 := by
  have h := inner_toLp_eq_mul_of_reflection (memLp_eval_cos (legendre l) 2)
    (legendre_eval_cos_pi_sub l) hf
  rw [legendreCoeff, show legendreLp l = (memLp_eval_cos (legendre l) 2).toLp _ from rfl,
    eq_zero_of_eq_mul_of_ne (by rw [← pow_mul, mul_comm, pow_mul]; simp) h hl, zero_div]

/-- **Parity of the associated Legendre series.** If `f (π - θ) = ε f (θ)` almost everywhere,
the coefficient of `sin θ · P_l' (cos θ)` vanishes unless `ε = (-1)ˡ⁺¹`. -/
theorem associatedLegendreCoeff_eq_zero_of_parity {f : Lp ℝ 2 polarAngleMeasure} {ε : ℝ}
    (hf : ∀ᵐ θ ∂polarAngleMeasure, f (Real.pi - θ) = ε * f θ) {l : ℕ}
    (hl : ε ≠ (-1) ^ (l + 1)) : associatedLegendreCoeff f l = 0 := by
  have h := inner_toLp_eq_mul_of_reflection (memLp_sin_mul_eval_cos (derivative (legendre l)) 2)
    (sin_mul_derivative_legendre_eval_cos_pi_sub l) hf
  rw [associatedLegendreCoeff, show associatedLegendreLp l =
      (memLp_sin_mul_eval_cos (derivative (legendre l)) 2).toLp _ from rfl,
    eq_zero_of_eq_mul_of_ne (by rw [← pow_mul, mul_comm, pow_mul]; simp) h hl, zero_div]

/-- A function with `f (π - θ) = ε f (θ)` almost everywhere gives an element of
`L²((0, π), sin θ dθ)` with the same parity. -/
theorem toLp_pi_sub_of_parity {f : ℝ → ℝ} (hf : MemLp f 2 polarAngleMeasure) {ε : ℝ}
    (hpar : ∀ᵐ θ ∂polarAngleMeasure, f (Real.pi - θ) = ε * f θ) :
    ∀ᵐ θ ∂polarAngleMeasure, hf.toLp f (Real.pi - θ) = ε * hf.toLp f θ := by
  have h₁ := hf.coeFn_toLp
  have h₂ := QuasiMeasurePreserving.ae_eq_comp
    measurePreserving_pi_sub_polarAngleMeasure.quasiMeasurePreserving h₁
  filter_upwards [h₁, h₂, hpar] with θ hθ₁ hθ₂ hθ₃
  simp only [Function.comp_apply] at hθ₂
  rw [hθ₂, hθ₁, hθ₃]

/-- **Parity of the Legendre series** for a square-integrable function: if
`f (π - θ) = ε f (θ)` almost everywhere, the coefficient of `P_l (cos θ)` vanishes unless
`ε = (-1)ˡ`. -/
theorem legendreCoeff_toLp_eq_zero_of_parity {f : ℝ → ℝ} (hf : MemLp f 2 polarAngleMeasure)
    {ε : ℝ} (hpar : ∀ᵐ θ ∂polarAngleMeasure, f (Real.pi - θ) = ε * f θ) {l : ℕ}
    (hl : ε ≠ (-1) ^ l) : legendreCoeff (hf.toLp f) l = 0 :=
  legendreCoeff_eq_zero_of_parity (toLp_pi_sub_of_parity hf hpar) hl

/-- **Parity of the associated Legendre series** for a square-integrable function: if
`f (π - θ) = ε f (θ)` almost everywhere, the coefficient of `sin θ · P_l' (cos θ)` vanishes
unless `ε = (-1)ˡ⁺¹`. -/
theorem associatedLegendreCoeff_toLp_eq_zero_of_parity {f : ℝ → ℝ}
    (hf : MemLp f 2 polarAngleMeasure) {ε : ℝ}
    (hpar : ∀ᵐ θ ∂polarAngleMeasure, f (Real.pi - θ) = ε * f θ) {l : ℕ}
    (hl : ε ≠ (-1) ^ (l + 1)) : associatedLegendreCoeff (hf.toLp f) l = 0 :=
  associatedLegendreCoeff_eq_zero_of_parity (toLp_pi_sub_of_parity hf hpar) hl

end PDE.Analysis.SpecialFunctions
