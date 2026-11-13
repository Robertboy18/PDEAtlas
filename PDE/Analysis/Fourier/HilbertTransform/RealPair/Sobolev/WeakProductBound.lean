/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakProductBound
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.Weak
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.EvenSupport
public import PDE.Analysis.Calculus.Parity
import CAS.ExactTactic

/-!
# Velocity control by the product of the two weighted energies

The Hilbert transform preserves both weak L² norms. The sharp one-dimensional
product estimate and the sum of the two energies therefore give the velocity
constant `(a b)^(-1/4)`. Compact Lipschitz perturbations are sufficient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped ENNReal NNReal

namespace PDE.Analysis.IsHilbertPair

/-- Hilbert isometry transfers the sharp weak product estimate to a continuous
representative of the transform. -/
theorem sq_le_l2_mul_l2_weakDerivative {ω v η : ℝ → ℝ}
    (h : IsHilbertPair ω v) (hv : Continuous v) (hη : MemLp η 2 volume)
    (hweak : Evolution.HasWeakTimeDerivativeOn univ ω η) (x : ℝ) :
    v x ^ 2 ≤ (eLpNorm ω 2 volume).toReal * (eLpNorm η 2 volume).toReal := by
  obtain ⟨w, hw, hderiv⟩ := h.exists_hasWeakTimeDerivativeOn hη hweak
  have hb := hderiv.sq_apply_le_l2_mul_l2 hv h.memLp_right hw.memLp_right x
  simpa only [h.eLpNorm_eq, hw.eLpNorm_eq] using hb

end PDE.Analysis.IsHilbertPair

namespace PDE.Analysis.IsHilbertPair

/-- Finite combined weighted energy controls a continuous Hilbert
representative with constant `(a b)^(-1/4)`. -/
theorem velocity_le_of_product_lipschitz_energy
    {ω v φ σ : ℝ → ℝ} {L a b E : ℝ} {K : ℝ≥0}
    (ha : 0 < a) (hb : 0 < b) (hE : 0 ≤ E)
    (hω : LipschitzWith K ω) (hc : HasCompactSupport ω) (hodd : Function.Odd ω)
    (hsupport : ∀ x, L ≤ x → ω x = 0)
    (hp : IsHilbertPair ω v) (hv : Continuous v)
    (hφ : ∀ x ∈ Ioo 0 L, a ≤ φ x) (hσ : ∀ x ∈ Ioo 0 L, b ≤ σ x)
    (hint : IntegrableOn (fun x ↦ ω x ^ 2 * φ x) (Ioo 0 L))
    (hintX : IntegrableOn (fun x ↦ deriv ω x ^ 2 * σ x) (Ioo 0 L))
    (henergy : (∫ x in Ioo 0 L, ω x ^ 2 * φ x) +
      (∫ x in Ioo 0 L, deriv ω x ^ 2 * σ x) ≤ E ^ 2) (x : ℝ) :
    |v x| ≤ √(√(1 / (a * b))) * E := by
  let I := ∫ y in Ioo 0 L, ω y ^ 2 * φ y
  let J := ∫ y in Ioo 0 L, deriv ω y ^ 2 * σ y
  have hI : 0 ≤ I :=
    integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioo).mono
      fun y hy ↦ mul_nonneg (sq_nonneg _) (ha.le.trans (hφ y hy))
  have hJ : 0 ≤ J :=
    integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioo).mono
      fun y hy ↦ mul_nonneg (sq_nonneg _) (hb.le.trans (hσ y hy))
  have h0 := eLpNorm_le_of_even_sq_weighted_energy ha (Real.sqrt_nonneg I)
    (fun y ↦ by simp only [hodd y, neg_sq]) hsupport hφ hint
    (le_of_eq (Real.sq_sqrt hI).symm)
  have hd : ∀ y, L ≤ y → deriv ω y = 0 := by
    intro y hy
    have hzero : HasDerivWithinAt ω 0 (Ici y) y :=
      (hasDerivWithinAt_const y (Ici y) (0 : ℝ)).congr
        (fun z hz ↦ hsupport z (hy.trans hz)) (hsupport y hy)
    exact hzero.deriv_eq_zero (uniqueDiffWithinAt_Ici y)
  have hη := Calculus.memLp_deriv_of_lipschitzWith_compactSupport hω hc 2
  have h1 := eLpNorm_le_of_even_sq_weighted_energy hb (Real.sqrt_nonneg J)
    (fun y ↦ congrArg (fun z : ℝ ↦ z ^ 2) (even_deriv_of_odd hodd y))
    hd hσ hintX (le_of_eq (Real.sq_sqrt hJ).symm)
  have hproduct := hp.sq_le_l2_mul_l2_weakDerivative hv hη
    (Calculus.hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport hω hc) x
  have hconstant : √(2 / a) * √(2 / b) = 2 * √(1 / (a * b)) := by
    calc
      _ = √(4 * (1 / (a * b))) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        cas
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num)]
        have hs : √(4 : ℝ) = 2 := by cas
        rw [hs]
  have hIJ : 2 * √I * √J ≤ I + J := by
    nlinarith [sq_nonneg (√I - √J), Real.sq_sqrt hI, Real.sq_sqrt hJ]
  have hsq : v x ^ 2 ≤ √(1 / (a * b)) * E ^ 2 := by
    calc
      _ ≤ (√(2 / a) * √I) * (√(2 / b) * √J) :=
        hproduct.trans (mul_le_mul h0 h1 ENNReal.toReal_nonneg (by positivity))
      _ = √(1 / (a * b)) * (2 * √I * √J) := by
        calc
          _ = (√(2 / a) * √(2 / b)) * (√I * √J) := by cas
          _ = _ := by rw [hconstant]; cas
      _ ≤ √(1 / (a * b)) * (I + J) :=
        mul_le_mul_of_nonneg_left hIJ (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hE)).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)] using hsq

end PDE.Analysis.IsHilbertPair
