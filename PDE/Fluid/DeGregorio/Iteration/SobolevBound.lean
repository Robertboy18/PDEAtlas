/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import CAS.ExactTactic

/-!
# An H² bound for the frozen Hilbert transport production

The stretching coefficient is the concrete Hilbert transform of the input.
Its first two derivatives are identified with the transforms of the input
derivatives. Hilbert isometry and the one-dimensional Sobolev bound therefore
control the full H² energy production using only input and output H² norms.

The input is `C³` and the output `C²`, both with compact support. The bound loses
no derivative: the second derivative of the Hilbert transform enters only through
its L² norm.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory PDE.Analysis
open scoped ENNReal

namespace DeGregorio

private theorem sobolev_production_scalar_bound
    {A B C a b c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    3 * ((A + B) * a * a) + (A + B) * b * b + (A + B) * c * c +
        2 * ((a + b) * B * b) + 2 * ((a + b) * C * c) +
        2 * ((b + c) * B * c) ≤
      9 * (A + B + C) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h₁ : 2 * (a + b) * b ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := two_mul_le_add_sq a b
    cas using h
  have h₂ : 2 * (a + b) * c ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := add_le_add (two_mul_le_add_sq a c) (two_mul_le_add_sq b c)
    cas using h
  have h₃ : 2 * (b + c) * c ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := two_mul_le_add_sq b c
    cas using h
  have h₀ : 3 * ((A + B) * a * a) + (A + B) * b * b + (A + B) * c * c ≤
      3 * (A + B) * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := add_nonneg hA hB
    cas using h
  linarith [mul_le_mul_of_nonneg_left h₁ hB, mul_le_mul_of_nonneg_left h₂ hC,
    mul_le_mul_of_nonneg_left h₃ hB, mul_nonneg (add_nonneg hA hC)
      (add_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c))]

/-- The Hilbert transport H² production is bounded by the input H²
size times the output H² energy. All velocity bounds and derivative Hilbert
pairs are derived from the original concrete pair. -/
theorem norm_integral_hilbert_sobolev_production_le {f w u : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hsuppf : HasCompactSupport f)
    (hw : ContDiff ℝ 2 w) (hsuppw : HasCompactSupport w)
    (hu : ContDiff ℝ 3 u) (hpair : IsHilbertPair f (deriv u)) :
    ‖∫ x,
      3 * deriv u x * w x ^ 2 + deriv u x * deriv w x ^ 2 -
        deriv u x * deriv (deriv w) x ^ 2 +
        2 * deriv (deriv u) x * w x * deriv w x +
        2 * deriv (deriv (deriv u)) x * w x * deriv (deriv w) x +
        2 * deriv (deriv u) x * deriv w x * deriv (deriv w) x‖ ≤
      9 * (lpNorm f 2 volume + lpNorm (deriv f) 2 volume +
        lpNorm (deriv (deriv f)) 2 volume) *
          ((∫ x, w x ^ 2) + (∫ x, deriv w x ^ 2) + ∫ x, deriv (deriv w) x ^ 2) := by
  let h := deriv u
  let q := deriv w
  let r := deriv q
  have hh : ContDiff ℝ 2 h := hu.deriv'
  have hq : ContDiff ℝ 1 q := hw.deriv'
  have hr : Continuous r := hq.continuous_deriv le_rfl
  have hpair₁ := hpair.deriv_of_contDiff_two hh.continuous
    (hf.of_le (by norm_num)) hsuppf
  have hpair₂ := hpair₁.deriv_of_contDiff_two (hh.continuous_deriv (by norm_num))
    (hf.deriv' (n := 2)) hsuppf.deriv
  have hwLp : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hsuppw
  have hqLp : MemLp q 2 volume := hq.continuous.memLp_of_hasCompactSupport hsuppw.deriv
  have hrLp : MemLp r 2 volume := hr.memLp_of_hasCompactSupport hsuppw.deriv.deriv
  let A := lpNorm f 2 volume
  let B := lpNorm (deriv f) 2 volume
  let C := lpNorm (deriv (deriv f)) 2 volume
  let a := lpNorm w 2 volume
  let b := lpNorm q 2 volume
  let c := lpNorm r 2 volume
  have hH (x : ℝ) : ‖h x‖ ≤ A + B :=
    hpair.norm_le_eLpNorm_add_deriv hh.continuous (hf.of_le (by norm_num)) hsuppf x
  have hW (x : ℝ) : ‖w x‖ ≤ a + b :=
    SobolevSpace.norm_apply_le_eLpNorm_toReal_add_deriv
      (hw.of_le (by norm_num)) (by norm_num) hwLp hqLp x
  have hQ (x : ℝ) : ‖q x‖ ≤ b + c :=
    SobolevSpace.norm_apply_le_eLpNorm_toReal_add_deriv
      hq (by norm_num) hqLp hrLp x
  have hAB : 0 ≤ A + B := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have hab : 0 ≤ a + b := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have hbc : 0 ≤ b + c := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have h₀ := abs_integral_triple_mul_le_of_bound hh.continuous.aestronglyMeasurable hAB hH hwLp hwLp
  have h₁ := abs_integral_triple_mul_le_of_bound hh.continuous.aestronglyMeasurable hAB hH hqLp hqLp
  have h₂ := abs_integral_triple_mul_le_of_bound hh.continuous.aestronglyMeasurable hAB hH hrLp hrLp
  have h₃ := abs_integral_triple_mul_le_of_bound hw.continuous.aestronglyMeasurable hab hW
    hpair₁.memLp_right hqLp
  have h₄ := abs_integral_triple_mul_le_of_bound hw.continuous.aestronglyMeasurable hab hW
    hpair₂.memLp_right hrLp
  have h₅ := abs_integral_triple_mul_le_of_bound hq.continuous.aestronglyMeasurable hbc hQ
    hpair₁.memLp_right hrLp
  change |∫ x, h x * w x * w x| ≤ (A + B) * a * a at h₀
  change |∫ x, h x * q x * q x| ≤ (A + B) * b * b at h₁
  change |∫ x, h x * r x * r x| ≤ (A + B) * c * c at h₂
  have hnorm₁ : lpNorm (deriv h) 2 volume = B :=
    congrArg ENNReal.toReal hpair₁.eLpNorm_eq
  have hnorm₂ : lpNorm (deriv (deriv h)) 2 volume = C :=
    congrArg ENNReal.toReal hpair₂.eLpNorm_eq
  rw [hnorm₁] at h₃ h₅
  rw [hnorm₂] at h₄
  have hHtop := memLp_top_of_bound (μ := volume) hh.continuous.aestronglyMeasurable (A + B)
    (Eventually.of_forall hH)
  have hWtop := memLp_top_of_bound (μ := volume) hw.continuous.aestronglyMeasurable (a + b)
    (Eventually.of_forall hW)
  have hQtop := memLp_top_of_bound (μ := volume) hq.continuous.aestronglyMeasurable (b + c)
    (Eventually.of_forall hQ)
  have hI₀ := (hHtop.mul (r := 2) hwLp).integrable_mul hwLp
  have hI₁ := (hHtop.mul (r := 2) hqLp).integrable_mul hqLp
  have hI₂ := (hHtop.mul (r := 2) hrLp).integrable_mul hrLp
  have hI₃ := (hWtop.mul (r := 2) hpair₁.memLp_right).integrable_mul hqLp
  have hI₄ := (hWtop.mul (r := 2) hpair₂.memLp_right).integrable_mul hrLp
  have hI₅ := (hQtop.mul (r := 2) hpair₁.memLp_right).integrable_mul hrLp
  have halgebra : (fun x ↦
      3 * deriv u x * w x ^ 2 + deriv u x * deriv w x ^ 2 -
        deriv u x * deriv (deriv w) x ^ 2 +
        2 * deriv (deriv u) x * w x * deriv w x +
        2 * deriv (deriv (deriv u)) x * w x * deriv (deriv w) x +
        2 * deriv (deriv u) x * deriv w x * deriv (deriv w) x) =
      fun x ↦ 3 * (h x * w x * w x) + h x * q x * q x - h x * r x * r x +
        2 * (w x * deriv h x * q x) + 2 * (w x * deriv (deriv h) x * r x) +
        2 * (q x * deriv h x * r x) := by
    funext x
    dsimp [h, q, r]
    cas
  obtain ⟨l₀, u₀⟩ := abs_le.mp h₀
  obtain ⟨l₁, u₁⟩ := abs_le.mp h₁
  obtain ⟨l₂, u₂⟩ := abs_le.mp h₂
  obtain ⟨l₃, u₃⟩ := abs_le.mp h₃
  obtain ⟨l₄, u₄⟩ := abs_le.mp h₄
  obtain ⟨l₅, u₅⟩ := abs_le.mp h₅
  have hI₀₁ := (hI₀.const_mul 3).add hI₁
  have hI₀₁₂₃ := (hI₀₁.sub hI₂).add (hI₃.const_mul 2)
  rw [halgebra, integral_add, integral_add, integral_add, integral_sub, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    Real.norm_eq_abs]
  · refine (abs_le.2 ⟨by linarith, by linarith⟩).trans ((sobolev_production_scalar_bound
      (A := A) (B := B) (C := C) (a := a) (b := b) (c := c) lpNorm_nonneg lpNorm_nonneg
      lpNorm_nonneg).trans_eq ?_)
    rw [integral_sq_eq_eLpNorm_toReal_sq hwLp, integral_sq_eq_eLpNorm_toReal_sq hqLp,
      integral_sq_eq_eLpNorm_toReal_sq hrLp]
    rfl
  exacts [hI₀.const_mul 3, hI₁, hI₀₁, hI₂, hI₀₁.sub hI₂, hI₃.const_mul 2, hI₀₁₂₃, hI₄.const_mul 2,
    hI₀₁₂₃.add (hI₄.const_mul 2), hI₅.const_mul 2]

end DeGregorio
